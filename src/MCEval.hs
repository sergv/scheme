----------------------------------------------------------------------------
-- |
-- Module      :  MCEval
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fcontext-stack=100 #-}

module MCEval where

import Control.Arrow
import Control.Applicative
import Control.Monad.Except
import Control.Monad.Identity
-- import Data.IntMap (IntMap)
import Data.Monoid
import Data.Text.Lazy (Text)
-- import Text.ParserCombinators.Parsec
import Text.PrettyPrint.Leijen.Text (Pretty, Doc)

import qualified Text.PrettyPrint.Leijen.Text as PP

import ALaCarte
import Parse
import Types

import Prelude hiding (mapM)


type ErrT a = ExceptT Text Identity a

--- prettyprinter for scheme sexps

showSexp :: (Pretty a) => a -> Text
showSexp = PP.displayT . PP.renderPretty 1.0 80 . PP.pretty

class PrettyAlg f g where
  prettyAlg :: f (Doc, Term g) -> Doc

instance (PrettyAlg f h, PrettyAlg g h) => PrettyAlg (f :+: g) h where
  prettyAlg (Inl f) = prettyAlg f
  prettyAlg (Inr g) = prettyAlg g

instance PrettyAlg (K AInt) g where
  prettyAlg (K (AInt n)) = PP.integer n
instance PrettyAlg (K ADouble) g where
  prettyAlg (K (ADouble x)) = PP.double x
instance PrettyAlg (K AString) g where
  prettyAlg (K (AString s)) = PP.dquotes $ PP.text s
instance PrettyAlg (K ABool) g where
  prettyAlg (K (ABool b)) = PP.text $ if b == True then "#t" else "#f"
instance PrettyAlg (K Nil) g where
  prettyAlg (K Nil) = PP.text "nil"
instance PrettyAlg (K Symbol) g where
  prettyAlg (K (Symbol sym)) = PP.text sym
instance (K Nil :<: g) => PrettyAlg List g where
  prettyAlg (List (x, _) xs (t, tExpr)) =
    case (xs, project tExpr) of
      ([], Just (K Nil)) -> PP.parens x
      (_, Just (K Nil))  -> PP.parens $ x PP.<+> PP.align (PP.sep $ map fst xs)
      (_, Nothing)       -> PP.parens $ x PP.<+> PP.align (PP.sep $ map fst xs ++ [PP.dot, t])
instance PrettyAlg Vector g where
  prettyAlg (Vector xs) =
    PP.text "#(" <> PP.cat (map fst xs) <> PP.text ")"
instance Pretty SchemeSexp where
  pretty = para prettyAlg


-- instance Error Text where
--   noMsg  = T.empty
--   strMsg = T.pack

-- class Depth f g where
--   depthAlg :: f (Term (g :&: Int)) -> Int
--
-- instance ({-f :<: g', g :<: g',-} Depth f g', Depth g g') => Depth (f :+: g) g' where
--   depthAlg (Inl x) = depthAlg x
--   depthAlg (Inr y) = depthAlg y
--
-- instance Depth List SchemeSexpF where
--   depthAlg (List h xs t) = 1 + (maximum $ map (\(_ :&: ann) -> ann) $ map unTerm $ h : t : xs)
--
-- instance Depth (K AInt) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth (K ADouble) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth (K AString) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth (K ABool) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth (K Nil) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth (K Symbol) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth Vector SchemeSexpF where
--   depthAlg _ = 1

-- Basically (Term g) goes to (Term h) which involves
-- histomorphism recursion and term homomorphisms in result.
-- Also conversion may fail, hence ErrT monad.
-- (f :<: g, f :<: h) =>
class GetProgram f h where
  -- getProgramAlg :: f (Term h, Term g) -> ErrT (Context h (Term h))
  getProgramAlg :: f (Term (SchemeSexpF :&: Term h)) -> ErrT (Context h (Term h))

instance (GetProgram f h', GetProgram g h') => GetProgram (f :+: g) h' where
  getProgramAlg (Inl x) = getProgramAlg x
  getProgramAlg (Inr y) = getProgramAlg y

instance (K AInt :<: g, Functor g) => GetProgram (K AInt) g where
  getProgramAlg = return . symToSym . inject . K . unK
  -- getProgramAlg (K x@(AInt _))    = return . symToSym . inject $ K x
instance (K ADouble :<: g, Functor g) => GetProgram (K ADouble) g where
  getProgramAlg = return . symToSym . inject . K . unK
instance (K AString :<: g, Functor g) => GetProgram (K AString) g where
  getProgramAlg = return . symToSym . inject . K . unK
instance (K ABool :<: g, Functor g) => GetProgram (K ABool) g where
  getProgramAlg = return . symToSym . inject . K . unK
instance (K Nil :<: SchemeExprF) => GetProgram (K Nil) SchemeExprF where
  getProgramAlg = return . symToSym . inject . K . unK
instance GetProgram (K Symbol) SchemeExprF where
  getProgramAlg = return . symToSym . inject . K . unK

instance GetProgram List SchemeExprF where
  getProgramAlg (List (Term (hSexp :&: hExpr))
                      xs
                      (isNilTerm -> True)) =
    case proj hSexp of
      Just (K (Symbol "lambda"))
        | Term (argList :&: _): body <- xs ->
          if | Just (List h' xs' (isNilTerm -> True)) <- proj argList -> do
               args <- parseArgs $ h': xs'
               return $ Term $ iLambda args $ mkBegin body
             | isNil argList ->
               return $ Term $ iLambda [] $ mkBegin body
             | otherwise     ->
               err "invalid argument list of lambda form"
        | otherwise ->
          err "invalid lambda form"
      Just (K (Symbol "quote"))  ->
        case map (remA . unTerm) xs of
          [x] -> return $ symToSym $ Term $ iQuote $ Term $ stripA <$> x
          _   -> err "invalid quote form"
      Just (K (Symbol "set!"))   ->
        twoArgs iAssign "invalid set! form"
      Just (K (Symbol "define"))
        | Term (argList :&: _): body <- xs ->
          if | Just (K var@(Symbol _)) <- proj argList ->
               return $ Term $ iDefine var $ mkBegin body
             | Just (List (Term (h :&: _)) args (isNilTerm -> True)) <- proj argList,
               Just (K funcName@(Symbol _)) <- proj h -> do
               args' <- parseArgs args
               return $
                 Term $ iDefine funcName $
                 Term $ iLambda args' $ mkBegin body
             | otherwise ->
               err "invalid define form"
        | otherwise ->
          err "invalid define form"
        -- twoArgs iDefine "invalid define form"
      Just (K (Symbol "if"))     ->
        threeArgs iIf "invalid if form"
      Just (K (Symbol "begin"))  ->
        return $ mkBegin xs
      Just (K (Symbol "let"))
        | Term (bindings :&: _): body <- xs ->
          if | Just (List h' xs' (isNilTerm -> True)) <- proj bindings -> do
               bindings' <- mapM destructLetBinding $ h':xs'
               let bindings'' = map (Hole *** Hole) bindings'
               return $ Term $ iLet bindings'' $ mkBegin body
             | isNil bindings ->
               return $ Term $ iLet [] $ mkBegin body
             | otherwise ->
               err "invalid let form"
        | otherwise ->
          err "invalid let form"
      Just (K (Symbol "cond"))  -> do
        clauses <- mapM destructCondClause xs
        return $ Term $ iCond clauses
        -- return . symToSym . inject $ Cond $ map (ann . unTerm) clauses
      Just (K (Symbol "and"))   ->
        twoArgs iAnd "invalid and form"
      Just (K (Symbol "or"))    ->
        twoArgs iOr "invalid or form"
      Just (K (Symbol "not"))   ->
        singleArg iNot "invalid not form"
      _                         ->
        return $ symToSym $ Term $ iApply hExpr $ map (ann . unTerm) xs
       -- Just (K (Symbol v)) -> inject $ Apply hExpr $ map (ann . unTerm) xs
     where
       err msg = throwError $ msg <> ": " <> prettySexp
       prettySexp = showSexp (Term $ iList (Term $ stripA <$> hSexp)
                                           (map (Term . fmap stripA . remA . unTerm) xs)
                                           (Term iNil))
       mkBegin :: [Term (a :&: SchemeExpr)] -> Context SchemeExprF SchemeExpr
       mkBegin = symToSym . Term . iBegin . map (ann . unTerm)
       parseArgs :: [Term (SchemeSexpF :&: a)] -> ErrT [Symbol]
       parseArgs = mapM (toSymbol "invalid function argument" . stripA)
       -- singleArg :: a -> Text -> ErrT (Context SchemeExprF SchemeExpr)
       singleArg cons msg =
         case map (ann . unTerm) xs of
           [x] -> return $ symToSym $ Term $ cons x
           _   -> err msg
       twoArgs cons msg =
         case map (ann . unTerm) xs of
           [x, y] -> return $ symToSym $ Term $ cons x y
           _      -> err msg
       threeArgs cons msg =
         case map (ann . unTerm) xs of
           [x, y, z] -> return $ symToSym $ Term $ cons x y z
           _         -> err msg

       destructLetBinding :: (Term (SchemeSexpF :&: SchemeExpr)) -> ErrT (SchemeExpr, SchemeExpr)
       destructLetBinding binding@(Term (x :&: _)) =
         case proj x of
           Just (List (Term (origNameExpr :&: nameExpr))
                      [Term (_ :&: valExpr)]
                      (isNilTerm -> True)) -> do
             case proj origNameExpr of
               Just (K (Symbol _)) -> return (nameExpr, valExpr)
               _                   ->
                 throwError $ "invalid bound variable name in let form" <> prettyBinding
           _                           ->
             throwError $ "invalid let form binding" <> prettyBinding
         where
           prettyBinding = ": " <> showSexp (stripA binding)
       destructCondClause :: Term (SchemeSexpF :&: SchemeExpr) ->
                             ErrT (Context SchemeExprF SchemeExpr, Context SchemeExprF SchemeExpr)
       destructCondClause binding@(Term (x :&: _)) =
         case proj x of
           Just (List (Term (_ :&: condition))
                      body
                      (isNilTerm -> True)) ->
             return (symToSym condition, mkBegin body)
           _                           ->
             throwError $ "invalid cond form clause" <> prettyBinding
         where
           prettyBinding = ": " <> showSexp (stripA binding)

       toSymbol :: Text -> Term SchemeSexpF -> ErrT Symbol
       toSymbol errMsg t =
         case project t of
           Just (K sym@(Symbol _)) -> return sym
           _                       -> throwError $ errMsg <>
                                      ", symbol expected: " <> showSexp t
  getProgramAlg x = throwError $ "cannot exctract program from " <>
                    showSexp (inject $ fmap stripA x :: SchemeSexp)

instance GetProgram Vector SchemeExprF where
  getProgramAlg (Vector vs) =
    return . symToSym . Term . iVector $ map (ann . unTerm) vs

getProgram :: SchemeSexp -> Either Text SchemeExpr
getProgram = runIdentity . runExceptT . histoFutuM getProgramAlg

-- data SchemeExprF f = SelfEvaluating (AtomF f)
--                    | Variable Symbol
--                    | Quote SchemeSexp
--                    | Assign f f
--                    | Define f f
--                    | If f f f
--                    | LambdaProc (Lambda f)
--                    | PrimitiveProc (Primitive f)
--                    | Begin [f]
--                    | Cond [(f, f)]
--                    | Call f [f]
--                    | And f f
--                    | Or f f
--                    | Let [(f, f)] f
--                    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)



-- main :: IO ()
-- main = do
--   print $ (runParser "test" parser "(foo)" :: SchemeSexp)

-- -- these things may come up dering evaluation
-- data SchemeDataF f = DAtom (AtomF f)
--                    | DSymbol Symbol
--                    | DList f [f] f
--                    | DLambda (Lambda f)
--                    | DPrimitive (Primitive f)
--                    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
--
-- type SchemeData = Fix SchemeDataF
--
--
-- -- Program data type
-- data SchemeExprF f = SelfEvaluating (AtomF f)
--                    | Variable Symbol
--                    | Quote SchemeSexp
--                    | Assign f f
--                    | Define f f
--                    | If f f f
--                    | LambdaProc (Lambda f)
--                    | PrimitiveProc (Primitive f)
--                    | Begin [f]
--                    | Cond [(f, f)]
--                    | Call f [f]
--                    | And f f
--                    | Or f f
--                    | Let [(f, f)] f
--                    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
--
-- type SchemeExpr = Fix SchemeExprF
--
-- -- readProgram :: forall m. (MonadError Text m) => SchemeSexp -> m SchemeExpr
-- -- readProgram = paraM alg
-- --   where
-- --     alg :: SchemeSexpF (SchemeExpr, SchemeSexp) -> m SchemeExpr
-- --     alg (SAtom atom)                                                     =
-- --       return $ Fix $ SelfEvaluating atom
-- --     alg (SSymbol sym)                                                    =
-- --       return $ Fix $ Variable sym
-- --     alg (SList (_, SSymbol (Symbol "quote")) [(_, Fix sexp)] (_, Fix (SAtom Nil))) =
-- --       return $ Fix $ Quote sexp
-- --     alg (SList (_, SSymbol (Symbol "quote")) _           _)              =
-- --       throwError $ "invalid quote expression: " <> showSexp
-- --     alg (SList (_, SSymbol (Symbol "set!")) [(_, _), (_, _)])            =
-- --       undefined
-- --
-- --     -- alg (SPair (Fix (Variable (Symbol "quote"))) y)  = Fix $ Quote y
-- --     -- alg (SPair (Fix (Variable (Symbol "lambda"))) y) = Fix $ LambdaProc $ Lambda undefined
-- --     -- alg (SPair (Fix (Variable (Symbol "set!"))) y)   = Fix $ Quote y
-- --     -- alg (SPair x y)                                  = Fix $ Call x $ pairsToList y
-- --
-- --     -- pairsToList :: SchemeExpr
-- --
