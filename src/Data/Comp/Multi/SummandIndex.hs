{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Comp.Multi.SummandIndex where
{-
Module      : SummandIndex
Description : Type level calculation of the size of a summand in a higher order compositional functor
              and a type class to calculate the index of a summand within a higher order compositional functor.
              This can be used to produce a map from summand index to some value.

This module provides a type level calculation of the size of a summand in a higher order compositional functor.
It also provides a type class to calculate the index of a summand within a higher order compositional functor.
You can use this to produce a map from summand index to some value.
-}

import Data.Kind
import Data.Comp.Multi.Ops
import Data.Comp.SubsumeCommon
import GHC.TypeLits
import qualified Data.Proxy as P



-- Type level calculation of the size of a particular summand.
type family SummandSize (f :: (Type -> Type) -> Type -> Type) where
  SummandSize (f :+: g) = SummandSize f + SummandSize g
  SummandSize _ = 1


-- Given the size type of the summand create an integer value.
getSummandSize :: forall (f :: (Type -> Type) -> Type -> Type) (num :: Type) . (Integral num, KnownNat (SummandSize f)) => (Proxy f) -> num
getSummandSize (_pr :: Proxy f) = fromIntegral $ natVal (P :: Proxy (SummandSize f))


-- | Given a higher order compositional functor g and a summand f return a unique index for the summand f within g.
class SummandIndex p (f :: (Type -> Type) -> Type -> Type) (g :: (Type -> Type) -> Type -> Type) where
    summandIndex :: Proxy g -> Proxy p -> f a i -> Int


instance SummandIndex (Found Here) f f where
    summandIndex _ _ _ = 0


instance SummandIndex (Found p) f g => SummandIndex (Found (Le p)) f (g :+: g') where
    summandIndex _ _ x = summandIndex (P :: Proxy g) (P :: Proxy (Found p)) x


instance (SummandIndex (Found p) f g', KnownNat (SummandSize g)) => SummandIndex (Found (Ri p)) f (g :+: g') where
    summandIndex _ _ x = getSummandSize (P :: Proxy g) + summandIndex (P :: Proxy g') (P :: Proxy (Found p)) x


instance (SummandIndex (Found p1) f1 g, SummandIndex (Found p2) f2 g)
    => SummandIndex (Found (Sum p1 p2)) (f1 :+: f2) g where
    summandIndex _ _ (Inl x) = summandIndex (P :: Proxy g) (P :: Proxy (Found p1)) x
    summandIndex _ _ (Inr x) = summandIndex (P :: Proxy g) (P :: Proxy (Found p2)) x


-- | Given a higher order compositional functor g and a summand f return a unique index for the summand f within g.
getSummandIndex :: forall f g a i . (f :<: g, SummandIndex (ComprEmb (Elem f g)) f g) => P.Proxy g -> f a i -> Int
getSummandIndex _pr = summandIndex (P :: Proxy g) (P :: Proxy (ComprEmb (Elem f g)))
