----------------------------------------------------------------------------
-- |
-- Module      :  ALaCarte.TH
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

module ALaCarte.TH where

import Control.Applicative
import Data.List
import Language.Haskell.TH

import qualified ALaCarte

-- TODO write more functions
-- Assume following datatype
-- data Expr = Nil | Cons Lam Lam | Lambda [Param] Lam
-- 1. define i* versions of all class constructors, e.g. iCons, iNil, iLambda
-- that would employ inject
-- 2. pattern-generating function so following definition will work
-- f $(match 'Expr (Lambda (Cons x Nil) body))
-- or
-- f [match| Expr Lambda (Cons x Nil) body |]
-- - probably it shouldn't generate view patterns with projections but
-- should aim for real patterns instead
-- - ^ cons - defeats extensibility of compositional data types and
--            requires recompilation on datatype changes
-- - cons against view patterns - may be slow and/or messy
--
-- also toplevel match quasiquoted could generate predicate that checks
-- given shape

-- TODO: check that typeName resolves to functor (* -> *) and
-- use underapplied type (of kind * -> *) in context in type signatures.
deriveInjectingConstructor :: Name -> Q [Dec]
deriveInjectingConstructor datatypeName = do
  TyConI dataDef <- reify datatypeName
  let (t, tvars, constructors) =
        case dataDef of
          DataD _ctx typeName tvs cs _csNames ->
            (typeName, tvs, cs)
          NewtypeD _ctx typeName tvs c _ ->
            (typeName, tvs, [c])
          x -> error $ "Unsupported data declaration: " ++ show x
  -- case tvars of
  --   [] -> error $ "Type " ++ show t ++ " must be of kind higher than *"
  --   _  ->
  concat <$> mapM (makeInjectingConstructor t tvars) constructors
  where
    mkDatatypeType :: Name -> [TyVarBndr] -> TypeQ
    mkDatatypeType typeName tvars =
      foldl' appT (conT typeName) $ map (varT . tvarName) tvars

    tvarName :: TyVarBndr -> Name
    tvarName (PlainTV name)    = name
    tvarName (KindedTV name _) = name

    expandCon :: Con -> (Name, [Type])
    expandCon (NormalC name fieldTypes) = (name, map snd fieldTypes)
    expandCon (RecC name fieldTypes)    = (name, map (\(_, _, t) ->t) fieldTypes)
    expandCon x                         = error $ "Unsupported constructor " ++ show x

    makeInjectingConstructor :: Name -> [TyVarBndr] -> Con -> Q [Dec]
    makeInjectingConstructor tname tvars con = do
      gName <- newName "g"
      let (name, fieldTypes) = expandCon con
          -- t'                 = mkDatatypeType tname tvars
          g :: TypeQ
          g = varT gName
      vs <- mapM (const $ newName "x") fieldTypes
      (tF, tvars', generalType, body) <-
        case tvars of
          [] -> do
            let k     = mkName "ALaCarte.K"
                aName = mkName "a"
                a     = varT aName
            return ( appT (conT k) $ conT tname -- [t| ALaCarte.K $(tname) |]
                   , [PlainTV aName]
                   , appT g a
                   , appE (conE k) $ foldl' appE (conE name) $ map varE vs
                   )
          _  -> do
            return ( mkDatatypeType tname $ init tvars
                   , tvars
                   , appT g (varT $ tvarName $ last tvars)
                   , foldl' appE (conE name) $ map varE vs
                   )
      let tvars'' = PlainTV gName: tvars'
          conName = mkName $ "i" ++ nameBase name
          conType = forallT tvars'' (cxt [classP (mkName "ALaCarte.:<:") [tF, g]]) $
                    foldr appT generalType $ map (appT arrowT . return) fieldTypes
          pat     = map varP vs

      sig <- sigD conName $ conType
      fun <- funD conName
                  [ clause pat
                           (normalB [e| ALaCarte.inj $ $(body) |])
                           []]
      return [sig, fun]


-- data List a b = Nil
--               | Cons a b

-- iNil :: Term (List a)
-- iNil :: (List :<: g) => Term (g a)
-- iNil = inject Nil
--
-- iCons :: a -> Term (List a)
-- iCons = inject
