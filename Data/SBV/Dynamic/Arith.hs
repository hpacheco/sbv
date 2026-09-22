-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Dynamic.Arith
--
-- Derived arithmetic on 'SVal'.
--
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Data.SBV.Dynamic.Arith
  ( svGcd
  , svLcm
  , sdLcm
  , sdLcms
  , sdBvSubO
  ) where

import Data.SBV.Core.Kind         (HasKind(..))
import Data.SBV.Core.Symbolic     (SVal)
import Data.SBV.Core.Operations   (svIte, svEqual, svOr, svRem, svTimes
                                  , svDivide, svDecrement)
import Data.SBV.Tools.Overflow    (bvSubO)

import Data.SBV.Dynamic.Delayed   (SExprF, SDelayedOps, intSVal, lift2SBV
                                  , toSVal, fromSBool)

-- | Euclidean GCD on symbolic word values, as a fixed unrolling whose depth is
-- computed from a concrete upper bound @maxVal@ on the operands.
svGcd :: Int -> SVal -> SVal -> SVal
svGcd maxVal a b = go a b (intSVal k (maxIters maxVal))
    where
    k = kindOf a
    go :: SVal -> SVal -> SVal -> SVal
    go x y c = svIte
        (svEqual c (intSVal k 0) `svOr` svEqual y (intSVal k 0))
        x
        (go y (svRem x y) (svDecrement c))
    maxIters :: Int -> Int
    maxIters n
        | n <= 1    = 1
        | otherwise = ceiling $ 1.44 * logBase 2 (realToFrac n :: Double)


-- Assumes that the product fits in the operand's kind.
svLcm :: Int -> SVal -> SVal -> SVal
svLcm maxVal a b = svDivide top bot
    where
    top = svTimes a b
    bot = svGcd maxVal a b

-- | Lifting into the delayed AST of 'svLcm'.
sdLcm :: SDelayedOps o1 o2 on => Int -> SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
sdLcm maxVal = lift2SBV (svLcm maxVal)

sdLcms :: SDelayedOps o1 o2 on => Int -> [SExprF o1 o2 on] -> Maybe (SExprF o1 o2 on)
sdLcms _      [] = Nothing
sdLcms maxVal xs = Just $ foldl1 (sdLcm maxVal) xs

-- | Lifting into the delayed AST of @Data.SBV.Tools.Overflow.bvSubO@.
sdBvSubO :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
sdBvSubO x y = fromSBool $ bvSubO (toSVal x) (toSVal y)
