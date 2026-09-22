-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Dynamic.KindArith
--
-- Width arithmetic for the dynamic interface.
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns #-}

module Data.SBV.Dynamic.KindArith
  ( -- * Enumerating a bounded kind
    svKindRange
  , svEnumerateKind
  , svKindIntSet
    -- * Deriving a kind from a value range
  , svWordKindFor
  , svIntKindFor
  , svKindForIntSet
  , svBoolAsWordKind
    -- * Bit-width helpers
  , svSignedWidth
  , svBitsFor
  , svCeilLog2
    -- * Result kinds of the arithmetic operators
  , svUnifyKind
  , svPlusKind
  , svMinusKind
  , svTimesKind
  , svModKind
  , svDivKind
    -- * Total dynamic cast
  , svCastKind
    -- * Unpacking a packed word
  , svUnpackFields
  ) where

import Data.IntSet              (IntSet)
import qualified Data.IntSet as IntSet

import Data.SBV.Core.Kind       (Kind(..), HasKind(..))
import Data.SBV.Core.Symbolic   (SVal)
import Data.SBV.Core.Operations ( svIte, svNotEqual, svInteger, svTrue, svFalse
                                , svFromIntegral, svExtract )

-- | The range @(min, max)@ a bounded kind can represent; @Nothing@ for kinds that are not finite.
svKindRange :: Kind -> Maybe (Integer, Integer)
svKindRange (KBounded False n) = Just (0, 2^n - 1)
svKindRange (KBounded True  n) = Just (negate (2^(n-1)), 2^(n-1) - 1)
svKindRange _                  = Nothing

-- | Every value of a bounded kind, in order.
svEnumerateKind :: Kind -> Maybe [Integer]
svEnumerateKind k = (\(lo, hi) -> [lo .. hi]) <$> svKindRange k

-- | Every value of a bounded kind as an 'IntSet'.
svKindIntSet :: Kind -> Maybe IntSet
svKindIntSet k = mk <$> svKindRange k
  where mk (lo, hi) = IntSet.fromList [fromEnum lo .. fromEnum hi]

-- | @ceiling (logBase 2 n)@ on 'Int'.
svCeilLog2 :: Int -> Int
svCeilLog2 n
  | n <= 1    = 0
  | otherwise = ceiling (logBase 2 (fromIntegral n :: Double))

-- | Bits needed to hold values up to @n@ inclusive.
svBitsFor :: Integer -> Int
svBitsFor n = max 1 (length (takeWhile (<= n) (iterate (* 2) 1)))

-- | The smallest unsigned kind holding @0 .. hi@.
-- Bit-vectors need at least one bit, so a singleton domain still costs a bit.
svWordKindFor :: Int -> Kind
svWordKindFor hi = KBounded False $ max 1 $ svCeilLog2 (hi + 1)

-- | The smallest signed kind holding @lo .. hi@.
svIntKindFor :: Int -> Int -> Kind
svIntKindFor lo hi = KBounded True $ max 1 (max maxExp minExp + 1)
  where
    maxExp = svCeilLog2 (hi + 1)
    minExp = svCeilLog2 (negate lo)

-- | The smallest kind holding every member of a value set.
svKindForIntSet :: IntSet -> Kind
svKindForIntSet is
  | lo < 0    = svIntKindFor lo hi
  | otherwise = svWordKindFor hi
  where lo = IntSet.findMin is
        hi = IntSet.findMax is

-- | The 1-bit unsigned kind of a 'KBool'.
svBoolAsWordKind :: Kind
svBoolAsWordKind = KBounded False 1

-- | Bits needed to hold a bounded kind's whole range as a signed value. 
svSignedWidth :: Kind -> Int
svSignedWidth (KBounded True  n) = n
svSignedWidth (KBounded False n) = n + 1
svSignedWidth k                  = error ("svSignedWidth: not a bounded kind: " ++ show k)

-- | The kind two operands must both be cast to before they can be compared or
-- selected between. 
svUnifyKind :: Kind -> Kind -> Kind
svUnifyKind k1 k2 | k1 == k2 = k1
svUnifyKind k1@(KBounded sign1 n1) k2@(KBounded sign2 n2)
  | sign1 == sign2 = KBounded sign1 (max n1 n2)
  | otherwise      = KBounded True (max (svSignedWidth k1) (svSignedWidth k2))
svUnifyKind KUnbounded _ = KUnbounded
svUnifyKind _ KUnbounded = KUnbounded
svUnifyKind KBool k2 = svUnifyKind svBoolAsWordKind k2
svUnifyKind k1 KBool = svUnifyKind k1 svBoolAsWordKind
svUnifyKind k1 k2 = error $ "svUnifyKind: " ++ show k1 ++ " " ++ show k2

-- | Result kind of an addition: one extra bit for the carry.
svPlusKind :: Kind -> Kind -> Kind
svPlusKind (KBounded sign1 n1) (KBounded sign2 n2)
  | sign1 == sign2 = KBounded (max sign1 sign2) (max n1 n2 + 1)
svPlusKind k1@(KBounded _ _) k2@(KBounded _ _) =
    KBounded True (max (svSignedWidth k1) (svSignedWidth k2) + 1)
svPlusKind KUnbounded _ = KUnbounded
svPlusKind _ KUnbounded = KUnbounded
svPlusKind KBool k2 = svPlusKind svBoolAsWordKind k2
svPlusKind k1 KBool = svPlusKind k1 svBoolAsWordKind
svPlusKind k1 k2 = error $ "svPlusKind: " ++ show k1 ++ " " ++ show k2

-- | Result kind of a subtraction. Always signed — a difference can go negative
-- whatever the operands are.
svMinusKind :: Kind -> Kind -> Kind
svMinusKind k1@(KBounded sign1 n1) k2@(KBounded sign2 n2)
  | sign1 == sign2 = KBounded True (max n1 n2 + 1)
  | otherwise      = KBounded True (max (svSignedWidth k1) (svSignedWidth k2) + 1)
svMinusKind KUnbounded _ = KUnbounded
svMinusKind _ KUnbounded = KUnbounded
svMinusKind KBool k2 = svMinusKind svBoolAsWordKind k2
svMinusKind k1 KBool = svMinusKind k1 svBoolAsWordKind
svMinusKind k1 k2 = error $ "svMinusKind: " ++ show k1 ++ " " ++ show k2

-- | Result kind of a multiplication: the widths add.
svTimesKind :: Kind -> Kind -> Kind
svTimesKind (KBounded sign1 n1) (KBounded sign2 n2)
  | sign1 == sign2 = KBounded (max sign1 sign2) (n1 + n2)
svTimesKind k1@(KBounded _ _) k2@(KBounded _ _) =
    KBounded True (svSignedWidth k1 + svSignedWidth k2)
svTimesKind KUnbounded _ = KUnbounded
svTimesKind _ KUnbounded = KUnbounded
svTimesKind KBool k2 = svTimesKind svBoolAsWordKind k2
svTimesKind k1 KBool = svTimesKind k1 svBoolAsWordKind
svTimesKind k1 k2 = error $ "svTimesKind: " ++ show k1 ++ " " ++ show k2

-- | Result kind of a remainder. Deliberately unsigned-only.
svModKind :: Kind -> Kind -> Kind
svModKind k1 k2 | k1 == k2 = k1
svModKind (KBounded False n1) (KBounded False n2) = KBounded False (n1 + n2)
svModKind k1 k2 = error $ "svModKind unsupported " ++ show k1 ++ " " ++ show k2

-- | Result kind of a division. Same unsigned-only restriction as 'svModKind'.
svDivKind :: Kind -> Kind -> Kind
svDivKind k1 k2 | k1 == k2 = k1
svDivKind (KBounded False n1) (KBounded False n2) = KBounded False (n1 + n2)
svDivKind k1 k2 = error $ "svDivKind unsupported " ++ show k1 ++ " " ++ show k2

-- | Cast an 'SVal' to a target 'Kind'.
svCastKind :: Kind -> SVal -> SVal
svCastKind k sv = case (ke, k) of
    (_, (== ke) -> True)          -> sv
    (KBool,        KBounded _ _)  -> svIte sv (svInteger k 1) (svInteger k 0)
    (KBounded _ _, KBounded _ _)  -> svFromIntegral k sv
    (KBounded _ _, KBool)         -> svIte (svNotEqual sv (svInteger ke 0)) svTrue svFalse
    _ -> error $ "svCastKind unsupported from " ++ show ke ++ " to " ++ show k
  where
    ke = kindOf sv

-- | The inverse of 'Data.SBV.Dynamic.svPackBits', generalized from bits to
-- fields: @svUnpackFields k n@ gives the kind of a word holding @n@ values of
-- kind @k@ (LSB first, matching 'svPackBits') together with the @n@
-- projections back out of it.
svUnpackFields :: Kind -> Int -> (Kind, [SVal -> SVal])
svUnpackFields KBool num = (KBounded False num, projs)
  where
    projs = map (\i -> svCastKind KBool . svExtract i i) [0 .. num - 1]
svUnpackFields k@(KBounded sign sz) num = (KBounded sign (sz * num), projs)
  where
    projs = map (\i -> svCastKind k . svExtract (i*sz + sz - 1) (i*sz)) [0 .. num - 1]
svUnpackFields k num = error $ "svUnpackFields unsupported " ++ show k ++ " " ++ show num
