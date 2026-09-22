-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Dynamic.Fun
--
-- Dynamic functions (uninterpreted and interpreted).
--
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Data.SBV.Dynamic.Fun
  ( uninterpretedFun
  , interpretedFun
  , dynamicFun
  , DynBody(..)
  ) where

import Control.Monad          (void)
import Control.Monad.IO.Class (liftIO)

import Data.SBV.Core.Data     (SVal(..), Lambda(..))
import Data.SBV.Core.Kind     (Kind)
import Data.SBV.Core.Symbolic ( State, Symbolic, SBVType(..), SBVExpr(..), UICodeKind(..), UIName(..)
                              , newUninterpreted, newExpr, svToSV, forceSVArg, cache, lambdaVar, outputSVal )
import Data.SBV.Lambda        (lambda, LambdaScope(..))

-- | A callable @[SVal] -> SVal@ that, on every application, registers the
-- function symbol @nm@ of the given kinds with the body the @code@ producer returns, and applies it to the arguments.
dynamicFun :: String -> [Kind] -> Kind -> (State -> IO UICodeKind) -> ([SVal] -> SVal)
dynamicFun nm kins kout code = f
  where
    f ins = SVal kout $ Right $ cache result
      where
        result st = do
            op    <- newUninterpreted st (UIGiven nm) Nothing (SBVType $ kins ++ [kout]) =<< code st
            swins <- mapM (svToSV st) ins
            mapM_ forceSVArg swins
            newExpr st kout $ SBVApp op swins

-- | An uninterpreted function symbol (opaque body).
uninterpretedFun :: String -> [Kind] -> Kind -> [SVal] -> SVal
uninterpretedFun nm kins kout = dynamicFun nm kins kout $ const $ pure $ UINone True

-- | An interpreted function symbol.
interpretedFun :: String -> [Kind] -> Kind -> ([SVal] -> Symbolic SVal) -> ([SVal] -> SVal)
interpretedFun nm kins kout f = dynamicFun nm kins kout $ \st ->
    UISMT <$> lambda st TopLevel kout (DynBody kins f)

-- | A lambda body over a runtime list of argument kinds.
data DynBody = DynBody [Kind] ([SVal] -> Symbolic SVal)

instance Lambda Symbolic DynBody where
  mkLambda st (DynBody kins f) = go kins f
    where
      go []     g = void $ outputSVal =<< g []
      go (k:ks) g = do a <- liftIO $ lambdaVar st k
                       go ks (g . (SVal k (Right (cache (const (pure a)))) :))
