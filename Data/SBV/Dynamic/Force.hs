-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Dynamic.Force
--
-- Deep forcing of dynamic values.
--
-- SBV's 'SVal' is lazy by construction. 
--
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.SBV.Dynamic.Force
  ( -- * Deep forcing inside the Symbolic state
    SBVNFData(..)
    -- * Forcing that needs no SBV state
  , forceIO
    -- * Rebuilding an SVal from an already-elaborated SV
  , svFromSV
  ) where

import Control.DeepSeq          (NFData, force, rnf)
import Control.Exception        (evaluate)
import Control.Monad.IO.Class   (MonadIO, liftIO)

import Data.SBV.Core.Concrete   (CV)
import Data.SBV.Core.Data       (SBV(..), SBool)
import Data.SBV.Core.Kind       (Kind, HasKind(..))
import Data.SBV.Core.Symbolic   (SV, SVal, Symbolic, cache, forceSVArg, svToSymSV)
import qualified Data.SBV.Core.Symbolic as CS

import Data.SBV.Dynamic.Delayed (SExprF(..))

-- | Structures whose SBV content can be deep-forced inside the 'Symbolic'
-- state.
class SBVNFData a where
  -- | Force @a@ completely, running any cached SBV computation it contains.
  forceSBV :: a -> Symbolic a

instance SBVNFData CV where
  forceSBV v = forceIO v

instance SBVNFData SVal where
  forceSBV v = do
    sv <- svToSymSV v
    !() <- liftIO $! forceSVArg sv
    let v' = svFromSV sv (kindOf v)
    forceIO v'

instance SBVNFData SBool where
  forceSBV (SBV v) = SBV <$> forceSBV v

instance SBVNFData (SExprF o1 o2 on) where
  forceSBV (SConst cv) = do
    cv' <- forceSBV cv
    return $! SConst cv'
  forceSBV (SVal sv) = do
    sv' <- forceSBV sv
    return $! SVal sv'
  forceSBV (SOp1 o e1) = do
    e1' <- forceSBV e1
    return $! SOp1 o e1'
  forceSBV (SOp2 o e1 e2) = do
    e1' <- forceSBV e1
    e2' <- forceSBV e2
    return $! SOp2 o e1' e2'
  forceSBV (SOpn o es) = do
    es' <- mapM forceSBV es
    return $! SOpn o es'

instance {-# OVERLAPPABLE #-} NFData a => SBVNFData a where
  forceSBV = return . force

forceIO :: (MonadIO m, NFData a) => a -> m a
forceIO a = do
  !() <- liftIO $! evaluate $! rnf a
  return a

svFromSV :: SV -> Kind -> SVal
svFromSV sv k = CS.SVal k (Right (cache (const (return sv))))
