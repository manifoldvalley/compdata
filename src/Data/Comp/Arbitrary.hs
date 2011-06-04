{-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, TemplateHaskell, FlexibleInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Arbitrary
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines generation of arbitrary values for signatures, which
-- lifts to generating arbitrary terms.
--
--------------------------------------------------------------------------------

module Data.Comp.Arbitrary
    ( ArbitraryF(..)
    )where

import Test.QuickCheck
import Data.Comp.Term
import Data.Comp.Sum
import Data.Comp.Ops
import Data.Comp.Derive.Utils
import Data.Comp.Derive
import Control.Applicative

{-| This lifts instances of 'ArbitraryF' to instances of 'Arbitrary'
for the corresponding term type. -}

instance (ArbitraryF f) => Arbitrary (Term f) where
    arbitrary = Term <$> arbitraryF
    shrink (Term expr) = map Term $ shrinkF expr

instance (ArbitraryF f, Arbitrary p) => ArbitraryF (f :&: p) where
    arbitraryF' = map addP arbitraryF'
        where addP (i,gen) =  (i,(:&:) <$> gen <*> arbitrary)
    arbitraryF = (:&:) <$> arbitraryF <*> arbitrary
    shrinkF (v :&: p) = tail [v' :&: p'| v' <- v: shrinkF v, p' <- p : shrink p ]

{-|
  This lifts instances of 'ArbitraryF' to instances of 'ArbitraryF' for 
  the corresponding context functor.
-}
instance (ArbitraryF f) => ArbitraryF (Context f) where
    arbitraryF = oneof [Term <$> arbitraryF , Hole <$> arbitrary]
    shrinkF (Term expr) = map Term $ shrinkF expr
    shrinkF (Hole a) = map Hole $ shrink a


{-| This lifts instances of 'ArbitraryF' to instances of 'Arbitrary'
for the corresponding context type.  -}

instance (ArbitraryF f, Arbitrary a) => Arbitrary (Context f a) where
    arbitrary = arbitraryF
    shrink = shrinkF


{-| Instances of 'ArbitraryF' are closed under forming sums.  -}

instance (ArbitraryF f , ArbitraryF g) => ArbitraryF (f :+: g) where
    arbitraryF' = map inl arbitraryF' ++ map inr arbitraryF'
        where inl (i,gen) = (i,Inl <$> gen)
              inr (i,gen) = (i,Inr <$> gen)
    shrinkF (Inl val) = map Inl (shrinkF val)
    shrinkF (Inr val) = map Inr (shrinkF val)


$(derive [makeArbitraryF] $ [''Maybe,''[]] ++ tupleTypes 2 10)