module Data.Comp.Multi.SummandIndex where

import Data.Comp.SubsumeCommon


type family SummandSize f where
  SummandSize (f :+: g) = SummandSize f + SummandSize g
  SummandSize _ = 1


summandSize :: (Integral num) => (Proxy f) -> num
summandSize pr = fromIntegral $ natVal (P :: Proxy (SummandSize f))


class SummandIndex p f g where
    summandIndex :: Proxy p -> f -> Int


instance SummandIndex (Found Here) f f where
    summandIndex _ _ = 0


instance SummandIndex (Found p) f g => SummandIndex (Found (Le p)) f (g :+: g') where
    summandIndex _ x = summandIndex (P :: Proxy (Found p)) x


instance SummandIndex (Found p) f g => SummandIndex (Found (Ri p)) f (g' :+: g) where
    summandIndex _ x = summandSize (P :: Proxy g) + summandIndex (P :: Proxy (Found p)) x


instance (SummandIndex (Found p1) f1 g, SummandIndex (Found p2) f2 g)
    => SummandIndex (Found (Sum p1 p2)) (f1 :+: f2) g where
    summandIndex _ (Inl x) = summandIndex (P :: Proxy (Found p1)) x
    summandIndex _ (Inr x) = summandIndex (P :: Proxy (Found p2)) x
