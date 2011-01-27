{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Derive.HEquality
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Patrick Bahrm, Tom Hvitved
-- Stability   :  unknown
-- Portability :  unknown
--
-- The equality algebra (equality on terms).
--
--------------------------------------------------------------------------------
module Data.ALaCarte.Derive.HEquality
    (
     HEqF(..),
     KEq(..),
     instanceHEqF
    ) where

import Data.ALaCarte.Derive.Utils
import Data.ALaCarte.Multi.HFunctor
import Language.Haskell.TH hiding (Cxt, match)


class KEq f where
    keq :: f i -> f j -> Bool

{-|
  Functor type class that provides an 'Eq' instance for the corresponding
  term type class.
-}
class HEqF f where

    heqF :: KEq g => f g i -> f g j -> Bool


instance KEq f => Eq (f i) where
    (==) = keq

instance Eq a => KEq (K a) where
    keq (K x) (K y) = x == y

instance KEq a => Eq (A a) where
     A x == A y = x `keq`  y

{-| This function generates an instance declaration of class 'EqF' for
a type constructor of any first-order kind taking at least one
argument. The implementation is not capable of deriving instances for
recursive data types. -}

instanceHEqF :: Name -> Q [Dec]
instanceHEqF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let args' = init args
      argNames = (map (VarT . tyVarBndrName) (init args'))
      ftyp = VarT . tyVarBndrName $ last args'
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''Eq . (: [])) argNames
      classType = AppT (ConT ''HEqF) complType
  eqFDecl <- funD 'heqF  (eqFClauses ftyp constrs)
  return $ [InstanceD preCond classType [eqFDecl]]
      where eqFClauses ftyp constrs = map (genEqClause ftyp . normalCon') constrs
                                   ++ (defEqClause constrs)
            filterFarg fArg ty x = (fArg == ty, x)
            defEqClause constrs
                | length constrs  < 2 = []
                | otherwise = [clause [wildP,wildP] (normalB [|False|]) []]
            genEqClause ftyp (constr, argts) = do 
              let n = length argts
              varNs <- newNames n "x"
              varNs' <- newNames n "y"
              let pat = ConP constr $ map VarP varNs
                  pat' = ConP constr $ map VarP varNs'
                  vars = map VarE varNs
                  vars' = map VarE varNs'
                  mkEq ty x y = let (x',y') = (return x,return y)
                                in if containsType ty ftyp
                                   then [| $x' `keq` $y'|]
                                   else [| $x' == $y'|]
                  eqs = listE $ zipWith3 mkEq argts vars vars'
              body <- if n == 0 
                      then [|True|]
                      else [|and $eqs|]
              return $ Clause [pat, pat'] (NormalB body) []