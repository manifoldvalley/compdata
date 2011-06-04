{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances,
  ScopedTypeVariables, UndecidableInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.Show
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @ShowD@.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Derive.Show
    (
     PShow(..),
     ShowD(..),
     makeShowD
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.Param.FreshM
import Control.Monad
import Language.Haskell.TH hiding (Cxt, match)

-- |Printing of parametric values.
class PShow a where
    pshow :: a -> FreshM String

{-| Signature printing. An instance @ShowD f@ gives rise to an instance
  @Show (Term f)@. -}
class ShowD f where
    showD :: PShow a => f Var a -> FreshM String

{-| Derive an instance of 'ShowD' for a type constructor of any parametric
  kind taking at least two arguments. -}
makeShowD :: Name -> Q [Dec]
makeShowD fname = do
  -- Comments below apply to the example where name = T, args = [a,b,c], and
  -- constrs = [(X,[c]), (Y,[a,c]), (Z,[b -> c])], i.e. the data type
  -- declaration: T a b c = X c | Y a c | Z (b -> c)
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  -- coArg = c (covariant difunctor argument)
  let coArg :: Name = tyVarBndrName $ last args
  -- conArg = b (contravariant difunctor argument)
  let conArg :: Name = tyVarBndrName $ last $ init args
  -- argNames = [a]
  let argNames = map (VarT . tyVarBndrName) (init $ init args)
  -- compType = T a
  let complType = foldl AppT (ConT name) argNames
  -- classType = Difunctor (T a)
  let classType = AppT (ConT ''ShowD) complType
  -- constrs' = [(X,[c]), (Y,[a,c]), (Z,[b -> c])]
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  showDDecl <- funD 'showD (map (showDClause conArg coArg) constrs')
  return [InstanceD [] classType [showDDecl]]
      where showDClause :: Name -> Name -> (Name,[Type]) -> ClauseQ
            showDClause conArg coArg (constr, args) = do
              varXs <- newNames (length args) "x"
              -- Pattern for the constructor
              let patx = ConP constr $ map VarP varXs
              body <- showDBody (nameBase constr) conArg coArg (zip varXs args)
              return $ Clause [patx] (NormalB body) []
            showDBody :: String -> Name -> Name -> [(Name, Type)] -> ExpQ
            showDBody constr conArg coArg x =
                [|liftM (unwords . (constr :) .
                         map (\x -> if elem ' ' x then "(" ++ x ++ ")" else x))
                        (sequence $(listE $ map (showDB conArg coArg) x))|]
            showDB :: Name -> Name -> (Name, Type) -> ExpQ
            showDB conArg coArg (x, tp)
                | not (containsType tp (VarT conArg)) &&
                  not (containsType tp (VarT coArg)) =
                    [| return $ show $(varE x) |]
                | otherwise =
                    case tp of
                      VarT a
                          | a == coArg -> [| pshow $(varE x) |]
                      AppT (AppT ArrowT (VarT a)) _
                          | a == conArg ->
                              [| do {v <- genVar;
                                     body <- pshow $ $(varE x) v;
                                     return $ "\\" ++ show v ++ " -> " ++ body} |]
                      SigT tp' _ ->
                          showDB conArg coArg (x, tp')
                      _ ->
                          if containsType tp (VarT conArg) then
                              [| showD $(varE x) |]
                          else
                              [| pshow $(varE x) |]