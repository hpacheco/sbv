-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Dynamic.Solver
--
-- Driving the Symbolic → Query lifecycle by hand.
--
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes          #-}

module Data.SBV.Dynamic.Solver
  ( -- * One-shot runs that thread caller state
    sdRunWithState
    -- * Incremental runs (one solver process, many check-sats)
  , sdRunIncremental
    -- * Per-solver base configuration for the dynamic route
  , sdSolverConfig
  , sdWithQuantifiers
  ) where

import Control.Concurrent      (forkIO, Chan, newChan, readChan, writeChan)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, readMVar, takeMVar)
import qualified Control.Exception as C
import Control.Monad           (forM, when, unless)
import Control.Monad.IO.Class  (liftIO)
import Control.Monad.Reader    (runReaderT)
import qualified Data.Foldable as F
import Data.IORef              (newIORef, readIORef, writeIORef)
import Data.List               (isPrefixOf)
import Data.Maybe              (isNothing, isJust, listToMaybe)

import Data.SBV                ( SMTConfig(..), SMTResult(..), SBool
                               , z3, cvc4, cvc5, bitwuzla, boolector )
import Data.SBV.Control        (Query, getSMTResult, SMTOption(..), CheckSatResult(..))
import Data.SBV.Control.Utils  ( modifyQueryState, getConfig, checkSatUsing, getModel, runProofOn, executeQuery )
import Data.SBV.Control.Query  (getUnsatCore, getUnknownReason)
import Data.SBV.Core.Data      (SolverContext(..), Outputtable(..), SMTProblem(..))
import Data.SBV.Dynamic.Delayed (sValToSBool)
import Data.SBV.Core.Symbolic  ( SVal, Symbolic, QueryT(..), QueryState(..), Solver(..), State(..)
                               , SMTSolver(..), SolverCapabilities(..), smtLibPgmText, symbolicEnv
                               , extractSymbolicSimulationState, isRunIStage
                               , runSymbolic, SBVRunMode(..), IStage(..), QueryContext(..) )

-- | Export of @Data.SBV.Provers.Prover.runWithQuery@.
runWithQuery :: (a -> Symbolic SBool) -> Bool -> Query b -> SMTConfig -> a -> IO b
runWithQuery reducer isSAT q cfg a = fst <$> runSymbolic cfg (SMTMode QueryInternal ISetup isSAT cfg) comp
  where comp = do _ <- reducer a >>= output
                  executeQuery QueryInternal q

-- | @check-sat@, optionally under an explicit tactic string. 
sdGetSMTResult :: Maybe String -> Query SMTResult
sdGetSMTResult Nothing      = getSMTResult
sdGetSMTResult (Just using) = getSMTResultUsing using

-- | 'getSMTResult' with the check-sat driven by a tactic string
getSMTResultUsing :: String -> Query SMTResult
getSMTResultUsing using = do
    cfg <- getConfig
    cs  <- checkSatUsing using
    case cs of
        Unsat  -> Unsatisfiable cfg   <$> unsatCoreIfRequested cfg
        Sat    -> Satisfiable   cfg   <$> getModel
        DSat p -> DeltaSat      cfg p <$> getModel
        Unk    -> Unknown       cfg   <$> getUnknownReason
  where
    unsatCoreIfRequested cfg
        | or [b | ProduceUnsatCores b <- solverSetOptions cfg] = Just <$> getUnsatCore
        | otherwise                                            = pure Nothing

-- | Refine the solver configuration from inside 'Query'.
sdModifyQueryCfg :: (SMTConfig -> SMTConfig) -> Query ()
sdModifyQueryCfg f = modifyQueryState $ \qst -> qst { queryConfig = f (queryConfig qst) }

-- | Run an encoding that also produces caller state, then check-sat.
sdRunWithState
    :: Bool                                     -- ^ @isProve@: prove (negate) vs. sat
    -> SMTConfig
    -> (st -> SMTConfig -> SMTConfig)            -- ^ late, state-dependent config refinement
    -> Maybe String                              -- ^ optional check-sat tactic
    -> (Query SMTResult -> Query SMTResult)      -- ^ measurement hook (@id@ for none)
    -> Symbolic (SVal, st)                       -- ^ the encoding, and the state it built
    -> IO (SMTResult, st)
sdRunWithState isProve cfg = sdRunWithStateRace (sdSeedRace cfg) isProve (sdStripRaceOptions cfg)

-- | 'sdRunWithState' over a race of solver processes: the encoding
-- runs once, then one solver process per config tweak races on it and the
-- first decisive answer wins.
sdRunWithStateRace
    :: [SMTConfig -> SMTConfig]                  -- ^ one tweak per replica (seeds, transcript names, ...)
    -> Bool                                      -- ^ @isProve@: prove (negate) vs. sat
    -> SMTConfig
    -> (st -> SMTConfig -> SMTConfig)            -- ^ late, state-dependent config refinement
    -> Maybe String                              -- ^ optional check-sat tactic
    -> (Query SMTResult -> Query SMTResult)      -- ^ measurement hook (@id@ for none)
    -> Symbolic (SVal, st)                       -- ^ the encoding, and the state it built
    -> IO (SMTResult, st)
sdRunWithStateRace tweaks isProve cfg refine tactic measure body = do
    ref <- newEmptyMVar
    let reduce m = do
            (b,st) <- m
            liftIO $ putMVar ref st
            return (sValToSBool b)
    let getRes = do
            st <- liftIO $ readMVar ref
            sdModifyQueryCfg (refine st)
            measure (sdGetSMTResult tactic)
    let isSAT = not isProve
    r <- fst <$> runSymbolic cfg (SMTMode QueryInternal ISetup isSAT cfg)
                   (reduce body >>= output >> executeQueryRace tweaks decisive getRes)
    st <- readMVar ref
    return (r,st)
  where
    decisive Unknown{} = False
    decisive _         = True

-- | 'Data.SBV.Control.Utils.executeQuery' over a race of solver processes: the encoding is
-- lowered to SMT-Lib once, then one solver process per config tweak races on
-- that same text and the first answer the @decisive@ predicate accepts wins.
executeQueryRace :: forall a. [SMTConfig -> SMTConfig] -> (a -> Bool) -> Query a -> Symbolic a
executeQueryRace tweaks decisive query = do
    st <- symbolicEnv
    rm <- liftIO $ readIORef (runMode st)
    case rm of
      SMTMode qc stage isSAT cfg | not (isRunIStage stage) -> do
          let slvr    = solver cfg
              backend = engine slvr
              dsatOK  = isNothing (dsatPrecision cfg) || isJust (supportsDeltaSat (capabilities slvr))
          unless dsatOK $ error $ "Data.SBV.Dynamic.Solver: delta-sat precision is specified but " ++ show (name slvr) ++ " does not support it"

          res     <- liftIO $ extractSymbolicSimulationState st
          setOpts <- liftIO $ reverse <$> readIORef (rSMTOptions st)
          let cfg' = cfg { solverSetOptions = solverSetOptions cfg ++ setOpts }
              pgm  = smtLibPgmText (smtLibPgm (runProofOn rm QueryInternal [] res) cfg')
          liftIO $ writeIORef (runMode st) $ SMTMode qc IRun isSAT cfg

          let run c s = backend c s pgm (runReaderT (runQueryT query))
          liftIO $ case tweaks of
            _ : _ : _ -> runRace tweaks decisive cfg' st run
            _         -> do
              let terminate mbE = readIORef (rQueryState st) >>= F.mapM_ (\qs -> queryTerminate qs mbE)
                  cfg'' = case tweaks of
                            [tweak] -> tweak cfg'
                            _       -> cfg'
              C.mask $ \restore -> do
                r <- restore (run cfg'' st) `C.catch` \e -> terminate (Just e) >> C.throwIO (e :: C.SomeException)
                terminate Nothing
                pure r
      _ -> error $ "Data.SBV.Dynamic.Solver.executeQueryRace: invalid query call in mode " ++ show rm

-- | The concurrent part of 'executeQueryRace': one solver process per
-- tweak, first decisive answer wins, everything else is killed.
runRace :: forall a. [SMTConfig -> SMTConfig] -> (a -> Bool) -> SMTConfig -> State -> (SMTConfig -> State -> IO a) -> IO a
runRace tweaks decisive cfg st run = C.mask $ \restore -> do
    replicas <- forM tweaks $ \tweak -> do
        qsRef <- newIORef Nothing
        oaRef <- readIORef (rOutstandingAsserts st) >>= newIORef
        pure (tweak cfg, st { rQueryState = qsRef, rOutstandingAsserts = oaRef })

    done <- newChan :: IO (Chan (Int, Either C.SomeException a))
    F.for_ (zip [0 ..] replicas) $ \(i, (c, s)) -> forkIO $ do
        r <- C.try (run c s)
        writeChan done (i, r)

    let ignoringSync act = act `C.catch` \(e :: C.SomeException) ->
                               case C.fromException e of
                                 Just (a :: C.SomeAsyncException) -> C.throwIO a
                                 Nothing                          -> pure ()

        killReplica (_, s) = ignoringSync $ readIORef (rQueryState s) >>= F.mapM_ queryKill

        stopLosers winner = F.for_ (zip [0 :: Int ..] replicas) $ \(i, r) ->
                                when (Just i /= winner) (killReplica r)

        -- Wait for the first decisive answer, remembering the best indecisive outcome seen so far.
        collect :: Int -> Maybe (Int, Either C.SomeException a) -> IO (Int, Either C.SomeException a)
        collect 0 fallback = case fallback of
                               Just r  -> pure r
                               Nothing -> error "Data.SBV.Dynamic.Solver.runRace: no replicas"
        collect n fallback = do
            r@(_, outcome) <- readChan done
            case outcome of
              Right v | decisive v -> pure r
              Right _              -> collect (n - 1) (Just r)
              Left _               -> collect (n - 1) (case fallback of
                                                          Just f@(_, Right _) -> Just f
                                                          _                   -> Just r)

    (winner, outcome) <- restore (collect (length replicas) Nothing) `C.onException` stopLosers Nothing
    stopLosers (Just winner)
    case outcome of
      Right v -> do 
                    readIORef (rQueryState (snd (replicas !! winner))) >>= F.mapM_ (\qs -> queryTerminate qs Nothing)
                    pure v
      Left e  -> C.throwIO e 

-- | Incremental / long-lived variant of 'sdRunWithState'. Runs @setup@ in
-- 'Symbolic' once, asserts its encoding, enters 'Query', and then loops: each
-- iteration check-sats, hands the result plus the current state to @loop@, and
-- either stops (@Nothing@) or asserts one more constraint and goes again
-- (@Just@).
sdRunIncremental
    :: Bool                                      -- ^ @isProve@, same convention as 'sdRunWithState'
    -> SMTConfig
    -> (st -> SMTConfig -> SMTConfig)            -- ^ late, state-dependent config refinement
    -> Maybe String                              -- ^ optional check-sat tactic
    -> (Query SMTResult -> Query SMTResult)      -- ^ measurement hook (@id@ for none)
    -> Symbolic (SVal, st)                       -- ^ setup: encoding + shared state
    -> (st -> SMTResult -> Query (Maybe SBool, st))
       -- ^ loop step: @(Nothing, st')@ terminates, @(Just c, st')@ asserts @c@ and iterates.
    -> IO (SMTResult, st)
sdRunIncremental isProve cfg refine tactic measure setup loop = do
    stRef <- newEmptyMVar
    let reduce m = do
            (encoding, st0) <- m
            liftIO $ putMVar stRef st0
            return (sValToSBool encoding)
    let query0 = do
            st0 <- liftIO $ readMVar stRef
            sdModifyQueryCfg (refine st0)
            let iter st = do
                    result <- measure (sdGetSMTResult tactic)
                    (mbNext, st') <- loop st result
                    case mbNext of
                        Nothing -> do
                            _ <- liftIO $ takeMVar stRef -- drain the initial state
                            liftIO $ putMVar stRef st'
                            return result
                        Just c -> do
                            constrain c
                            iter st'
            iter st0
    r <- runWithQuery reduce (not isProve) query0 (sdStripRaceOptions cfg) setup
    stFinal <- readMVar stRef
    return (r, stFinal)

-- | Force @supportsQuantifiers@ on in a config's capability table.
sdWithQuantifiers :: SMTConfig -> SMTConfig
sdWithQuantifiers cfg = cfg { solver = s { capabilities = caps { supportsQuantifiers = True } } }
  where s    = solver cfg
        caps = capabilities s

-- | The base configuration for each solver the dynamic route can use.
sdSolverConfig :: Solver -> SMTConfig
sdSolverConfig Z3        = z3
sdSolverConfig CVC5      = cvc5
sdSolverConfig CVC4      = cvc4
sdSolverConfig Bitwuzla  = sdWithQuantifiers bitwuzla
sdSolverConfig Boolector = boolector
sdSolverConfig s         = error $ "Data.SBV.Dynamic.Solver.sdSolverConfig: unsupported SMT solver " ++ show s

-- | The config's parallelism request, realised as a seed race: one config
-- per process, all running the same query, differing in the solver's random
-- seed.
-- Z3 5.1.0 returns answers @unknown@ in parallel mode. This is a SBV-side workaround for the same behavior.
sdSeedRace :: SMTConfig -> [SMTConfig -> SMTConfig]
sdSeedRace cfg
    | not (sdSupportsSeed $ name $ solver cfg) = [id] -- default behavior
    | size < 2  = [id]
    | otherwise = map process [0 .. size - 1]
  where
    size = sdRequestedThreads cfg
    cap  = maybe [] (sdSetMemoryCap cfg) (sdMemoryCap cfg)
    process 0 c = c
    process i c = c { extraArgs  = extraArgs c ++ sdSetSeedArgs c i ++ cap
                    , transcript = fmap (++ "." ++ show i) (transcript c)
                    }

-- | How many solver processes a config allows: its solver's own parallelism
-- options (z3: @parallel.enable@ / @parallel.threads.max@).
sdRequestedThreads :: SMTConfig -> Int
sdRequestedThreads cfg = case name (solver cfg) of
    Z3 | enabled ":parallel.enable" -> maximum $ 1 : values ":parallel.threads.max"
    _                               -> 1
  where
    opts        = solverSetOptions cfg
    enabled k   = or [ v == "true" | OptionKeyword k' [v] <- opts, k' == k ]
    values k    = [ n | OptionKeyword k' [v] <- opts, k' == k, (n, "") <- reads v ]

-- | The per-process memory cap a config asks for, in MB (z3: @memory_max_size@).
sdMemoryCap :: SMTConfig -> Maybe Int
sdMemoryCap cfg = case name (solver cfg) of
    Z3 -> listToMaybe [ n | OptionKeyword ":memory_max_size" [v] <- solverSetOptions cfg, (n, "") <- reads v ]
    _  -> Nothing

-- | Remove from a config the options a race answers itself: the solver's internal parallelism and the memory cap.
sdStripRaceOptions :: SMTConfig -> SMTConfig
sdStripRaceOptions cfg = case name (solver cfg) of
    Z3 -> cfg { solverSetOptions = filter (not . isRaceOption) (solverSetOptions cfg) }
    _  -> cfg
  where
    isRaceOption (OptionKeyword k _) = "parallel." `isPrefixOf` bare k || bare k == "memory_max_size"
      where bare = dropWhile (== ':')
    isRaceOption _                   = False

-- | Can this solver's random seed be set ('sdSetSeedArgs')?
sdSupportsSeed :: Solver -> Bool
sdSupportsSeed Z3 = True
sdSupportsSeed CVC4 = True
sdSupportsSeed CVC5 = True
sdSupportsSeed _ = False

-- | Set the command-line arguments that set this solver's random seed.
sdSetSeedArgs :: SMTConfig -> Int -> [String]
sdSetSeedArgs cfg n = case name (solver cfg) of
    Z3   -> ["smt.random_seed=" ++ show n, "sat.random_seed=" ++ show n]
    CVC4 -> ["--seed=" ++ show n]
    CVC5 -> ["--seed=" ++ show n]
    _    -> []

-- | Set the command-line arguments that cap this solver's memory, in MB. 
sdSetMemoryCap :: SMTConfig -> Int -> [String]
sdSetMemoryCap cfg mb = case name (solver cfg) of
    Z3 -> ["memory_max_size=" ++ show mb]
    _  -> []
