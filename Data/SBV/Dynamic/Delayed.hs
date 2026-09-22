-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Dynamic.Delayed
--
-- A delayed expression AST over 'SVal'.
--
-- SBV's 'SVal' constructors fold constants and simplify eagerly, at term-construction time, and the caching that goes with it is aggressive. This recovers some control.
--
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE ViewPatterns           #-}

module Data.SBV.Dynamic.Delayed
  ( -- * The delayed AST and its operators
    SExprF(..)
  , SDelayedOps(..)
  , SDOp1(..)
  , SDOp2(..)
  , SDOpn(..)
  , SDExpr
    -- * Lowering to, and lifting from, 'SVal'
  , toSVal
  , fromSVal
  , svalToCV
  , sValToSBool
  , toSBool
  , fromSBool
  , liftSBV
  , lift2SBV
  , lift3SBV
    -- * Constants
  , trueSBV
  , falseSBV
  , boolSBV
  , intSBV
  , intSVal
  , isTrueSBV
  , isFalseSBV
  , unIntSBV
    -- * Boolean algebra 
  , andSBV
  , andsSBV
  , orSBV
  , orsSBV
  , notSBV
  , impliesSBV
  , equivSBV
    -- * Comparisons
  , compareSBV
  , compareCastSBV
    -- * Kind unification and casts
  , unifySBV
  , castSBV
    -- * Arithmetic
  , plusSBV
  , plusCastSBV
  , minusSBV
  , minusCastSBV
  , timesSBV
  , timesCastSBV
  , divSBV
  , divCastSBV
  , quotSBV
  , modSBV
  , modCastSBV
  , remSBV
  , incrementSBV
  , decrementSBV
  , incSBV
  , minSBV
  , maxSBV
  , minimumSBV
  , maximumSBV
  , productSBV
  , summationSBV
    -- * Conditionals and multiplexers
  , iteSBV
  , iteCastSBV
  , iteMultiplexerSBV
  , iteLinearMuxSBV
    -- * Membership / range predicates over a concrete value set
  , sdIntRange
    -- * Bit-packed groups of values
  , sdUnpackFields
    -- * Polarity-correct guards
  , sdConstrainQuantifiedWith
  ) where

import Data.IntSet               (IntSet)
import qualified Data.IntSet as IntSet
import GHC.Generics               (Generic)

import Data.SBV.Core.Concrete     (CV(..), CVal(..), trueCV, falseCV)
import Data.SBV.Core.Data         (SBV(..), SBool)
import Data.SBV.Core.Kind         (Kind(..), HasKind(..))
import Data.SBV.Core.Symbolic     (SVal, Quantifier(..))
import qualified Data.SBV.Core.Symbolic as CS
import Data.SBV.Core.Operations
  ( svInteger, svNot, svAnd, svOr, svTrue, svFalse
  , svEqual, svNotEqual, svLessThan, svLessEq, svGreaterThan, svGreaterEq
  , svPlus, svMinus, svTimes, svQuot, svRem, svIte, svIncrement, svDecrement )
import Data.SBV.Dynamic.KindArith
  ( svUnifyKind, svPlusKind, svMinusKind, svTimesKind, svModKind, svDivKind
  , svCastKind, svUnpackFields )

-----------------------------------------------------------------------------
-- The AST

-- | The delayed expression type, parameterised over the labels of its unary,
-- binary and n-ary operators.
data SExprF o1 o2 on
    = SConst CV
    | SVal SVal
    | SOp1 o1 (SExprF o1 o2 on)
    | SOp2 o2 (SExprF o1 o2 on) (SExprF o1 o2 on)
    | SOpn on [SExprF o1 o2 on]
  deriving (Show,Generic)

-- | What the delayed layer needs to know about a consumer's operator labels.
class SDelayedOps o1 o2 on | o1 -> o2 on, o2 -> o1 on, on -> o1 o2 where
  -- | Is this the unary negation?
  sdIsNot   :: o1 -> Bool
  -- | Is this binary operator a comparison?
  sdIsCmp   :: o2 -> Bool
  -- | The negation of a comparison.
  sdNegCmp  :: o2 -> o2
  -- | The 'SVal' semantics of a comparison.
  sdCmpSVal :: o2 -> SVal -> SVal -> SVal
  -- | The n-ary conjunction label.
  sdAnd     :: on
  -- | The n-ary disjunction label.
  sdOr      :: on
  sdIsAnd   :: on -> Bool
  sdIsOr    :: on -> Bool
  -- | The equality label.
  sdEq      :: o2
  -- | Strict less-than.
  sdLt      :: o2
  -- | Less-or-equal.
  sdLeq     :: o2
  -- | Greater-or-equal.
  sdGeq     :: o2

-----------------------------------------------------------------------------
-- A delayed vocabulary

-- | Delayed unary label.
data SDOp1 = SDNot
  deriving (Eq,Ord,Show,Generic)

-- | Delayed binary labels.
data SDOp2 = SDEq | SDNeq | SDLt | SDLeq | SDGt | SDGeq
  deriving (Eq,Ord,Show,Generic)

-- | Delayed n-ary labels.
data SDOpn = SDAnd | SDOr
  deriving (Eq,Ord,Show,Generic)

-- | The delayed AST for a consumer that has no operator type of its own.
type SDExpr = SExprF SDOp1 SDOp2 SDOpn

instance SDelayedOps SDOp1 SDOp2 SDOpn where
  sdIsNot SDNot = True

  sdIsCmp _ = True   

  sdNegCmp SDEq  = SDNeq
  sdNegCmp SDNeq = SDEq
  sdNegCmp SDLt  = SDGeq
  sdNegCmp SDLeq = SDGt
  sdNegCmp SDGt  = SDLeq
  sdNegCmp SDGeq = SDLt

  sdCmpSVal SDEq  = svEqual
  sdCmpSVal SDNeq = svNotEqual
  sdCmpSVal SDLt  = svLessThan
  sdCmpSVal SDLeq = svLessEq
  sdCmpSVal SDGt  = svGreaterThan
  sdCmpSVal SDGeq = svGreaterEq

  sdAnd = SDAnd
  sdOr  = SDOr

  sdIsAnd SDAnd = True
  sdIsAnd _     = False

  sdIsOr SDOr = True
  sdIsOr _    = False

  sdEq  = SDEq
  sdLt  = SDLt
  sdLeq = SDLeq
  sdGeq = SDGeq

-----------------------------------------------------------------------------
-- Kinds

instance SDelayedOps o1 o2 on => HasKind (SExprF o1 o2 on) where
    kindOf (SConst cv) = kindOf cv
    kindOf (SVal sv) = kindOf sv
    kindOf (SOp1 o _) | sdIsNot o = KBool
    kindOf (SOp2 o _ _) | sdIsCmp o = KBool
    kindOf (SOpn o _) | sdIsAnd o || sdIsOr o = KBool
    kindOf _ = error "Data.SBV.Dynamic.Delayed: kindOf on an unmodelled delayed node"

-----------------------------------------------------------------------------
-- Lowering / lifting

svalToCV :: SVal -> Maybe CV
svalToCV (CS.SVal _ (Left cv)) = Just cv
svalToCV _ = Nothing

-- | Lower a delayed expression to an 'SVal'. 
toSVal :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SVal
toSVal (SConst cv) = CS.SVal (kindOf cv) (Left cv)
toSVal (SVal sv) = sv
toSVal (SOp1 o e) | sdIsNot o = svNot (toSVal e)
toSVal (SOp2 o x y) | sdIsCmp o = sdCmpSVal o (toSVal x) (toSVal y)
toSVal (SOpn o es) | sdIsAnd o = foldl svAnd svTrue (map toSVal es)
toSVal (SOpn o es) | sdIsOr o = foldl svOr svFalse (map toSVal es)
toSVal _ = error "Data.SBV.Dynamic.Delayed: toSVal on an unmodelled delayed node"

-- | Lift an 'SVal'.
fromSVal :: SVal -> SExprF o1 o2 on
fromSVal (svalToCV -> Just cv) = SConst cv
fromSVal v = SVal v

sValToSBool :: SVal -> SBool
sValToSBool sv = case kindOf sv of
    KBool -> SBV sv
    k -> error $ "sValToSBool: expected a bool but found a " ++ show k

toSBool :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SBool
toSBool e = sValToSBool $ toSVal e

fromSBool :: SBool -> SExprF o1 o2 on
fromSBool (SBV b) = fromSVal b

liftSBV :: SDelayedOps o1 o2 on => (SVal -> SVal) -> SExprF o1 o2 on -> SExprF o1 o2 on
liftSBV f e = fromSVal $ f (toSVal e)

lift2SBV :: SDelayedOps o1 o2 on => (SVal -> SVal -> SVal) -> SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
lift2SBV f x y = fromSVal $ f (toSVal x) (toSVal y)

lift3SBV :: SDelayedOps o1 o2 on => (SVal -> SVal -> SVal -> SVal) -> SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
lift3SBV f x y z = fromSVal $ f (toSVal x) (toSVal y) (toSVal z)

-----------------------------------------------------------------------------
-- Constants

trueSBV :: SExprF o1 o2 on
trueSBV = SConst trueCV

falseSBV :: SExprF o1 o2 on
falseSBV = SConst falseCV

boolSBV :: Bool -> SExprF o1 o2 on
boolSBV False = falseSBV
boolSBV True = trueSBV

isFalseSBV :: SExprF o1 o2 on -> Bool
isFalseSBV (SConst cv) = cv == falseCV
isFalseSBV _ = False

isTrueSBV :: SExprF o1 o2 on -> Bool
isTrueSBV (SConst cv) = cv == trueCV
isTrueSBV _ = False

intSVal :: Kind -> Int -> SVal
intSVal k i = svInteger k $ toEnum i

intSBV :: Kind -> Int -> SExprF o1 o2 on
intSBV k i = fromSVal $ intSVal k i

-- | Read a delayed expression back as a concrete 'Int'.
unIntSBV :: SExprF o1 o2 on -> Maybe Int
unIntSBV (SConst cv) = Just (fromEnum (cvToInteger cv))
unIntSBV (SVal (CS.SVal _ (Left cv))) = Just (fromEnum (cvToInteger cv))
unIntSBV _ = Nothing

-- @fromCV@ at 'Integer' without depending on "Data.SBV.Core.Model".
cvToInteger :: CV -> Integer
cvToInteger (CV _ (CInteger i)) = i
cvToInteger cv = error $ "Data.SBV.Dynamic.Delayed: expected an integral CV, got " ++ show cv

-----------------------------------------------------------------------------
-- Boolean algebra.

andSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
andSBV (SOpn (sdIsAnd -> True) xs) (SOpn (sdIsAnd -> True) ys) = SOpn sdAnd (xs ++ ys)
andSBV (SOpn (sdIsAnd -> True) xs) y = SOpn sdAnd (y : xs)
andSBV x (SOpn (sdIsAnd -> True) ys) = SOpn sdAnd (x : ys)
andSBV x y = SOpn sdAnd [x,y]

andsSBV :: (Foldable t,SDelayedOps o1 o2 on) => t (SExprF o1 o2 on) -> SExprF o1 o2 on
andsSBV = foldl andSBV trueSBV

orSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
orSBV (SOpn (sdIsOr -> True) xs) (SOpn (sdIsOr -> True) ys) = SOpn sdOr (xs ++ ys)
orSBV (SOpn (sdIsOr -> True) xs) y = SOpn sdOr (y : xs)
orSBV x (SOpn (sdIsOr -> True) ys) = SOpn sdOr (x : ys)
orSBV x y = SOpn sdOr [x,y]

orsSBV :: (Foldable t,SDelayedOps o1 o2 on) => t (SExprF o1 o2 on) -> SExprF o1 o2 on
orsSBV = foldl orSBV falseSBV

-- | De Morgan, pushed as far in as it goes.
notSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on
notSBV (SOp1 (sdIsNot -> True) e) = e
notSBV (SOp2 o x y) | sdIsCmp o = SOp2 (sdNegCmp o) x y
notSBV (SOpn o es) | sdIsAnd o = SOpn sdOr (map notSBV es)
notSBV (SOpn o es) | sdIsOr o = SOpn sdAnd (map notSBV es)
notSBV x = liftSBV svNot x

impliesSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
impliesSBV x y = notSBV x `orSBV` y

equivSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
equivSBV x y = SOp2 sdEq x y

-----------------------------------------------------------------------------
-- Comparisons

compareSBV :: o2 -> SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
compareSBV op e1 e2 = SOp2 op e1 e2

compareCastSBV :: SDelayedOps o1 o2 on => o2 -> SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
compareCastSBV op e1 e2 = compareSBV op v1 v2
    where (v1,v2) = unifySBV e1 e2

-----------------------------------------------------------------------------
-- Kind unification and casts

unifySBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> (SExprF o1 o2 on,SExprF o1 o2 on)
unifySBV v1 v2 = (castSBV k12 v1,castSBV k12 v2)
    where k12 = svUnifyKind (kindOf v1) (kindOf v2)

-- | Cast a delayed expression to a target kind. 
castSBV :: SDelayedOps o1 o2 on => Kind -> SExprF o1 o2 on -> SExprF o1 o2 on
castSBV k e
    | kindOf e == k = e
    | otherwise     = liftSBV (svCastKind k) e

-----------------------------------------------------------------------------
-- Arithmetic.
-- Currently, nothing here is delayed.

plusSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
plusSBV = lift2SBV svPlus

plusCastSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
plusCastSBV v1 v2 = plusSBV (castSBV k12 v1) (castSBV k12 v2)
    where k12 = svPlusKind (kindOf v1) (kindOf v2)

minusSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
minusSBV = lift2SBV svMinus

minusCastSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
minusCastSBV v1 v2 = minusSBV (castSBV k12 v1) (castSBV k12 v2)
    where k12 = svMinusKind (kindOf v1) (kindOf v2)

timesSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
timesSBV = lift2SBV svTimes

timesCastSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
timesCastSBV v1 v2 = timesSBV (castSBV k12 v1) (castSBV k12 v2)
    where k12 = svTimesKind (kindOf v1) (kindOf v2)

remSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
remSBV = lift2SBV svRem

modSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
modSBV = remSBV

modCastSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
modCastSBV v1 v2 = modSBV (castSBV k12 v1) (castSBV k12 v2)
    where k12 = svModKind (kindOf v1) (kindOf v2)

quotSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
quotSBV = lift2SBV svQuot

divSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
divSBV = quotSBV

divCastSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
divCastSBV v1 v2 = divSBV (castSBV k12 v1) (castSBV k12 v2)
    where k12 = svDivKind (kindOf v1) (kindOf v2)

decrementSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on
decrementSBV = liftSBV svDecrement

incrementSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on
incrementSBV = liftSBV svIncrement

incSBV :: SDelayedOps o1 o2 on => Int -> SExprF o1 o2 on -> SExprF o1 o2 on
incSBV i v = plusSBV v $ intSBV (kindOf v) i

minSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
minSBV x y = iteSBV (compareSBV sdLeq x y) x y

minimumSBV :: SDelayedOps o1 o2 on => [SExprF o1 o2 on] -> Maybe (SExprF o1 o2 on)
minimumSBV [] = Nothing
minimumSBV xs = Just $ foldl1 minSBV xs

maxSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
maxSBV x y = iteSBV (compareSBV sdLeq x y) y x

maximumSBV :: SDelayedOps o1 o2 on => [SExprF o1 o2 on] -> Maybe (SExprF o1 o2 on)
maximumSBV [] = Nothing
maximumSBV xs = Just $ foldl1 maxSBV xs

productSBV :: SDelayedOps o1 o2 on => [SExprF o1 o2 on] -> Maybe (SExprF o1 o2 on)
productSBV [] = Nothing
productSBV xs = Just $ foldl1 timesSBV xs

summationSBV :: SDelayedOps o1 o2 on => [SExprF o1 o2 on] -> Maybe (SExprF o1 o2 on)
summationSBV [] = Nothing
summationSBV xs = Just $ foldl1 plusSBV xs

-----------------------------------------------------------------------------
-- Conditionals and multiplexers

iteSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
iteSBV = lift3SBV svIte

-- | 'iteSBV' with the two branches unified to a common kind.
iteCastSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on -> SExprF o1 o2 on
iteCastSBV c t e = iteSBV c t' e'
    where (t', e') = unifySBV t e

-- | Balanced-tree multiplexer over a sorted domain: @O(log n)@ comparisons on
-- the path to each case.
iteMultiplexerSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> [Int] -> [SExprF o1 o2 on] -> SExprF o1 o2 on
iteMultiplexerSBV index domain formulas = walk (zip domain formulas)
  where
    walk []  = error "empty mux"
    walk [(_, f)] = f
    walk xs = case splitAt (length xs `div` 2) xs of
        (left, right@((pivot,_):_)) ->
            let condition = compareSBV sdLt index $ intSBV (kindOf index) pivot
            in iteSBV condition (walk left) (walk right)
        -- unreachable: 'xs' has >= 2 elements here, so the right half is non-empty
        (_, []) -> error "iteMultiplexerSBV: empty right half"

-- | Linear equality-ladder multiplexer.
iteLinearMuxSBV :: SDelayedOps o1 o2 on => SExprF o1 o2 on -> [Int] -> [SExprF o1 o2 on] -> SExprF o1 o2 on
iteLinearMuxSBV _ [] _ = error "iteLinearMuxSBV: empty domain"
iteLinearMuxSBV _ _ [] = error "iteLinearMuxSBV: empty formulas"
iteLinearMuxSBV _ [_] [f] = f
iteLinearMuxSBV index (d:ds) (f:fs) =
    let cond = compareSBV sdEq index (intSBV (kindOf index) d)
    in iteSBV cond f (iteLinearMuxSBV index ds fs)

-----------------------------------------------------------------------------
-- Membership / range predicates

-- | Is a sorted, ascending list exactly a contiguous interval? Returns its
-- endpoints if so. 
sdIsInterval :: [Int] -> Maybe (Int,Int)
sdIsInterval [] = Nothing
sdIsInterval [x] = Just (x,x)
sdIsInterval (x:xs) = sdIsInterval xs >>= \(i,j) -> if i==x+1 then Just (x,j) else Nothing

-- | \"@v@ is one of these values\", as small a predicate as the value set allows.
sdIntRange :: SDelayedOps o1 o2 on
           => SExprF o1 o2 on      -- ^ the value being restricted
           -> Maybe IntSet         -- ^ the allowed values (@Nothing@ = unrestricted)
           -> Maybe IntSet         -- ^ the value's full extent (@Nothing@ = unknown)
           -> SExprF o1 o2 on
sdIntRange v mbis mbts = go mbis mbts
  where
    go (Just is) (Just ts)
        | IntSet.size is == 0 = falseSBV
        | is == ts = trueSBV
        | IntSet.size (IntSet.difference ts is) < IntSet.size is = notSBV $ mk (IntSet.toList $ IntSet.difference ts is)
        | otherwise = mk (IntSet.toList is)
    go (Just is) Nothing = mk (IntSet.toList is)
    go Nothing _ = trueSBV

    mint = fmap IntSet.findMin mbts
    maxt = fmap IntSet.findMax mbts
    kind = kindOf v
    vop op i = compareSBV op v (intSBV kind i)
    mk [i] = vop sdEq i
    mk [i,j] = vop sdEq i `orSBV` vop sdEq j
    mk is = case sdIsInterval is of
        Just (i,j) ->
            (if mint==Just i then trueSBV else vop sdGeq i)
            `andSBV`
            (if maxt==Just j then trueSBV else vop sdLeq j)
        Nothing -> orsSBV $ map (\i -> vop sdEq i) is

-----------------------------------------------------------------------------
-- Bit-packed groups

-- | 'Data.SBV.Dynamic.KindArith.svUnpackFields' lifted to the delayed AST.
sdUnpackFields :: SDelayedOps o1 o2 on => Kind -> Int -> (Kind,[SExprF o1 o2 on -> SExprF o1 o2 on])
sdUnpackFields k num = (k',map liftSBV projs)
  where (k',projs) = svUnpackFields k num

-----------------------------------------------------------------------------
-- Quantifier guards

-- | The delayed-AST instance of the polarity rule documented on
-- 'Data.SBV.Dynamic.Quantifiers.svConstrainQuantified'.
sdConstrainQuantifiedWith :: (Monad m,SDelayedOps o1 o2 on)
                      => (SExprF o1 o2 on -> m ())   -- ^ assert (outermost group only)
                      -> Quantifier
                      -> Bool                        -- ^ is this the outermost group?
                      -> SExprF o1 o2 on             -- ^ the guard
                      -> m (SExprF o1 o2 on)         -- ^ the body
                      -> m (SExprF o1 o2 on)
sdConstrainQuantifiedWith assertIt _ True c m = assertIt c >> m
sdConstrainQuantifiedWith _ ALL False c m = fmap (impliesSBV c) m
sdConstrainQuantifiedWith _ EX  False c m = fmap (andSBV c) m
