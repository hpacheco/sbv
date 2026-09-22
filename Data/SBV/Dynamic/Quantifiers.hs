-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Dynamic.Quantifiers
--
-- Quantification for the dynamic interface.
--
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.SBV.Dynamic.Quantifiers
  ( -- * Dynamic binders
    Quantifier(..)
  , svQuantVar
    -- * Variable creation, uniformly across 'Symbolic' and 'Query'
  , svFreshVar
  , SVarMonad(..)
    -- * Closing a quantified body
  , svQuantified
  , sbQuantified
    -- * Polarity-correct range guards
  , svConstrainQuantified
    -- * Encoders layered over 'Symbolic'
  , SymbolicTrans(..)
    -- * Asserting from inside an encoder
  , stConstrain
  , sdConstrain
    -- * Closing a delayed quantified body
  , sdQuantified
    -- * Polarity-correct guard for an inner quantifier group
  , sdGuardInner
    -- * Polarity-correct guards, with the assertion supplied
  , sdConstrainQuantified
  , sdConstrainQuantifieds
    -- * Finite expansions
  , sdForallCon
  , sdExistsCon
    -- * Ranges
  , sdRangeSym
  , sdRangeHybrid
  ) where

import Control.Monad             (forM)
import Control.Monad.IO.Class    (MonadIO, liftIO)

import Data.SBV.Core.Data        (SBV(..), SBool, SolverContext(..), quantifiedBool, Constraint(..))
import Data.SBV.Core.Kind        (Kind)
import Data.SBV.Core.Symbolic    ( SVal, Symbolic, Query, Quantifier(..), MonadSymbolic(..)
                                 , MonadQuery, VarContext(..), quantVar, cache, svMkSymVar )
import qualified Data.SBV.Core.Symbolic as Sym
import Data.SBV.Core.Operations  (svAnd, svOr, svNot)
import Data.SBV.Dynamic          (svNewVar)
import Data.SBV.Control.Utils    (inNewContext)
import Data.SBV.Dynamic.Delayed
  ( SExprF(..), SDelayedOps(..), andSBV, andsSBV, orsSBV, impliesSBV
  , compareSBV, intSBV, toSVal, fromSVal, toSBool )
import Data.SBV.Dynamic.Delayed (sdConstrainQuantifiedWith)

-- | A monadic constraint body.
instance Constraint Symbolic a => Constraint Symbolic (Symbolic a) where
  mkConstraint st ma = ma >>= mkConstraint st

-- | A quantified variable of a computed 'Kind'. The SVal-level mirror
-- of the typed 'Data.SBV.Core.Data.mkQArg'.
svQuantVar :: MonadSymbolic m => Quantifier -> Kind -> m SVal
svQuantVar q k = symbolicEnv >>= \st -> liftIO $ do
  sv <- quantVar q st k
  pure (Sym.SVal k (Right (cache (const (pure sv)))))

-- | A fresh free variable of a computed 'Kind' from inside 'Query'. The SVal-level mirror of 'Data.SBV.Control.freshVar'.
svFreshVar :: (MonadIO m, MonadQuery m) => Kind -> String -> m SVal
svFreshVar k nm = inNewContext $ svMkSymVar QueryVar k (Just nm)

-- | Create a free variable of a computed 'Kind'.
class (MonadIO m, Monad m) => SVarMonad m where
  svVar :: Kind -> String -> m SVal

instance SVarMonad Symbolic where
  svVar = svNewVar

instance SVarMonad Query where
  svVar = svFreshVar

-- | Close a quantified body. This is the dynamic mirror of @quantifiedBool@.
svQuantified :: Symbolic SVal -> Symbolic SVal
svQuantified body = pure (unwrap (quantifiedBool (SBV <$> body :: Symbolic SBool)))
  where unwrap (SBV v) = v

-- | 'svQuantified' at the typed boolean.
sbQuantified :: Symbolic SBool -> Symbolic SBool
sbQuantified body = pure (quantifiedBool body)

-- | Attach a guard to a quantified body with the correct polarity.
svConstrainQuantified :: Monad m
                     => (SVal -> m ())   -- ^ assert (used only for the outermost group)
                     -> Quantifier       -- ^ the quantifier this guard sits under
                     -> Bool             -- ^ is this the outermost group?
                     -> SVal             -- ^ the guard
                     -> m SVal           -- ^ the body
                     -> m SVal
svConstrainQuantified assert _ True g body = assert g >> body
svConstrainQuantified _ ALL False g body = svOr (svNot g) <$> body
svConstrainQuantified _ EX  False g body = svAnd g <$> body

-- | A 'MonadTrans' layered over 'Symbolic'.
class MonadIO m => SymbolicTrans m where
  liftSymbolic :: Symbolic a -> m a
  mapSymbolic  :: (Symbolic a -> Symbolic b) -> m a -> m b

-- | Assert an 'SBool' from inside the encoder, without leaving it.
stConstrain :: SymbolicTrans m => SBool -> m ()
stConstrain = liftSymbolic . constrain

-- | 'stConstrain' at the delayed AST.
sdConstrain :: (SymbolicTrans m,SDelayedOps o1 o2 on) => SExprF o1 o2 on -> m ()
sdConstrain = stConstrain . toSBool

-- | 'svQuantified' at the delayed AST.
sdQuantified :: SDelayedOps o1 o2 on => Symbolic (SExprF o1 o2 on) -> Symbolic (SExprF o1 o2 on)
sdQuantified m = fmap fromSVal $ svQuantified (fmap toSVal m)

-- | Guard an inner quantifier group's body with the polarity that quantifier
-- demands.
sdGuardInner :: (Monad m,SDelayedOps o1 o2 on)
             => Quantifier
             -> SExprF o1 o2 on          -- ^ the range guard
             -> m (SExprF o1 o2 on)      -- ^ the body
             -> m (SExprF o1 o2 on)
sdGuardInner ALL g = fmap (impliesSBV g)
sdGuardInner EX  g = fmap (andSBV g)

-- | Delayed variant of 'svConstrainQuantified'.
sdConstrainQuantified :: (SymbolicTrans m,SDelayedOps o1 o2 on)
                       => Quantifier
                       -> Bool                        -- ^ is this the outermost group?
                       -> SExprF o1 o2 on             -- ^ the guard
                       -> m (SExprF o1 o2 on)         -- ^ the body
                       -> m (SExprF o1 o2 on)
sdConstrainQuantified = sdConstrainQuantifiedWith sdConstrain

-- | 'sdConstrainQuantified' for a list of nested guards.

sdConstrainQuantifieds :: (SymbolicTrans m,SDelayedOps o1 o2 on)
                        => Quantifier
                        -> Bool
                        -> [SExprF o1 o2 on]
                        -> m (SExprF o1 o2 on)
                        -> m (SExprF o1 o2 on)
sdConstrainQuantifieds _ _ []       m = m
sdConstrainQuantifieds q isOuter (c:cs) m =
    sdConstrainQuantified q isOuter c (sdConstrainQuantifieds q isOuter cs m)

-- | Forall over a concrete index set, as a conjunction. No quantifier reaches the solver.
sdForallCon :: (Monad m,SDelayedOps o1 o2 on) => [a] -> (a -> m (SExprF o1 o2 on)) -> m (SExprF o1 o2 on)
sdForallCon js f = fmap andsSBV $ mapM f js

-- | Exists over a concrete index set, as a disjunction. No quantifier reaches the solver.
sdExistsCon :: (Monad m,SDelayedOps o1 o2 on) => [a] -> (a -> m (SExprF o1 o2 on)) -> m (SExprF o1 o2 on)
sdExistsCon js f = fmap orsSBV $ mapM f js

-- | Quantified variable of kind @k@, relativised to @[smin, smax]@ and closed. 
sdRangeSym :: (SymbolicTrans m,SDelayedOps o1 o2 on)
           => Quantifier
           -> Kind                                        -- ^ kind of the bound variable
           -> SExprF o1 o2 on                             -- ^ @smin@
           -> SExprF o1 o2 on                             -- ^ @smax@
           -> (SExprF o1 o2 on -> m (SExprF o1 o2 on))    -- ^ the body
           -> m (SExprF o1 o2 on)
sdRangeSym q kind smin smax f = mapSymbolic sdQuantified $ do
    sj <- fmap SVal $ liftSymbolic (svQuantVar q kind)
    sdGuardInner q (compareSBV sdLeq smin sj `andSBV` compareSBV sdLeq sj smax) (f sj)

-- | Hybrid quantifier. Iterate concretely over @[0 .. maxk-1]@ and gate each index by the symbolic bounds. No quantifier reaches the solver.
sdRangeHybrid :: (Monad m,SDelayedOps o1 o2 on)
              => Quantifier
              -> Kind                                  -- ^ kind of the index literals
              -> SExprF o1 o2 on                       -- ^ symbolic @smin@
              -> SExprF o1 o2 on                       -- ^ symbolic @smax@
              -> Int                                   -- ^ concrete iteration bound
              -> (Int -> m (SExprF o1 o2 on))          -- ^ the body, at a concrete index
              -> m (SExprF o1 o2 on)
sdRangeHybrid q kind smin smax maxk f = fmap combine $ forM [0..maxk-1] $ \j -> do
    let jSBV = intSBV kind j
    let inRange = compareSBV sdLeq smin jSBV `andSBV` compareSBV sdLeq jSBV smax
    body <- f j
    return $ case q of
        ALL -> impliesSBV inRange body
        EX  -> inRange `andSBV` body
  where
    combine = case q of
        ALL -> andsSBV
        EX  -> orsSBV
