{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Comp.Multi.SummandIndex where

import Data.Kind
import Data.Comp.Multi.Ops
import Data.Comp.SubsumeCommon
import GHC.TypeLits
import qualified Data.Proxy as P


type family SummandSize (f :: (Type -> Type) -> Type -> Type) where
  SummandSize (f :+: g) = SummandSize f + SummandSize g
  SummandSize _ = 1


summandSize :: forall (f :: (Type -> Type) -> Type -> Type) (num :: Type) . (Integral num, KnownNat (SummandSize f)) => (Proxy f) -> num
summandSize (_pr :: Proxy f) = fromIntegral $ natVal (P :: Proxy (SummandSize f))

getSummandIndex :: forall f g a i . (f :<: g, SummandIndex (ComprEmb (Elem f g)) f g) => P.Proxy g -> f a i -> Int
getSummandIndex _pr = summandIndex (P :: Proxy g) (P :: Proxy (ComprEmb (Elem f g)))

class SummandIndex p (f :: (Type -> Type) -> Type -> Type) (g :: (Type -> Type) -> Type -> Type) where
    summandIndex :: Proxy g -> Proxy p -> f a i -> Int


instance SummandIndex (Found Here) f f where
    summandIndex _ _ _ = 0


instance SummandIndex (Found p) f g => SummandIndex (Found (Le p)) f (g :+: g') where
    summandIndex _ _ x = summandIndex (P :: Proxy g) (P :: Proxy (Found p)) x


instance (SummandIndex (Found p) f g', KnownNat (SummandSize g)) => SummandIndex (Found (Ri p)) f (g :+: g') where
    summandIndex _ _ x = summandSize (P :: Proxy g) + summandIndex (P :: Proxy g') (P :: Proxy (Found p)) x


instance (SummandIndex (Found p1) f1 g, SummandIndex (Found p2) f2 g)
    => SummandIndex (Found (Sum p1 p2)) (f1 :+: f2) g where
    summandIndex _ _ (Inl x) = summandIndex (P :: Proxy g) (P :: Proxy (Found p1)) x
    summandIndex _ _ (Inr x) = summandIndex (P :: Proxy g) (P :: Proxy (Found p2)) x

