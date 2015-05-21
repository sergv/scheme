----------------------------------------------------------------------------
-- |
-- Module      :  Eval.ExtractProgram
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverlappingInstances       #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -fcontext-stack=100 #-}

module Eval.ExtractProgram (GetProgram(..), getProgram) where

import Control.Arrow
import Control.Monad.Error hiding (mapM)
import Data.Monoid
import Data.Text.Lazy (Text)
-- import Data.Traversable (mapM)
import Data.Vector (Vector)
import qualified Data.Vector as V

import Text.PrettyPrint.Leijen.Text (Pretty)

import ALaCarte
import Types
import Utils

-- Basically (Term g) goes to (Term h) which involves
-- histomorphism recursion and term homomorphisms in result.
-- Also conversion may fail, hence Err monad.
-- (f :<: g, f :<: h) =>
class GetProgram f h where
  -- getProgramAlg :: f (Term h, Term g) -> Err (Context h (Term h))
  getProgramAlg :: Position
                -> f (Term (SchemeSexpF :&: U Position :*: Term (h :&: U Position)))
                -> Err (Context h (Term (h :&: U Position)))

instance (GetProgram f h', GetProgram g h') => GetProgram (f :+: g) h' where
  getProgramAlg p (Inl x) = getProgramAlg p x
  getProgramAlg p (Inr y) = getProgramAlg p y

instance (K AInt :<: h) => GetProgram (K AInt) h where
  getProgramAlg _pos = return . symToSym' . inj . K . unK
  -- getProgramAlg (K x@(AInt _))    = return . symToSym . inject $ K x
instance (K ADouble :<: h) => GetProgram (K ADouble) h where
  getProgramAlg _pos = return . symToSym' . inj . K . unK
instance (K AString :<: h) => GetProgram (K AString) h where
  getProgramAlg _pos = return . symToSym' . inj . K . unK
instance (K ABool :<: h) => GetProgram (K ABool) h where
  getProgramAlg _pos = return . symToSym' . inj . K . unK
instance (K Nil :<: h) => GetProgram (K Nil) h where
  getProgramAlg _pos = return . symToSym' . inj . K . unK
instance (K Symbol :<: h) => GetProgram (K Symbol) h where
  getProgramAlg _pos = return . symToSym' . inj . K . unK

instance forall h. (ToConstraint SpecialFormF h) => GetProgram List h where
  getProgramAlg sexpPos sexp@(List (Term (hSexp :&: _ :^: hExpr))
                                   xs
                                   (isNilTerm -> True)) =
    case proj hSexp of
      Just (K (Symbol "lambda"))
        | not (V.null xs)
        , Term (argList :&: argListPos :^: _) <- V.head xs
        , body                                <- V.tail xs ->
          if | Just (List h' xs' (isNilTerm -> True)) <- proj argList -> do
               args <- parseArgs $ V.cons h' xs'
               return $ Term $ iLambda args $ mkBegin body
             | isNil argList ->
               return $ Term $ iLambda V.empty $ mkBegin body
             | otherwise     ->
               err argListPos "invalid argument list of lambda form" argList
        | otherwise ->
          errSexp "invalid lambda form"
      Just (K (Symbol "quote")) ->
        case V.map (unTerm . stripA) xs of
          [x] -> return $ symToSym' $ iQuote $ Term x
          _   -> errSexp "invalid quote form"
      Just (K (Symbol "set!"))
        | [Term (var :&: _ :^: _), Term (_ :&: _ :^: val)] <- xs
        , Just (K sym@(Symbol _))                          <- proj var ->
        return $ symToSym' $ iAssign sym val
        | otherwise ->
          errSexp "invalid set! form"
      Just (K (Symbol "define"))
        | not (V.null xs)
        , Term (argList :&: _ :^: _) <- V.head xs
        , body                       <- V.tail xs ->
          if | Just (K var@(Symbol _)) <- proj argList ->
               return $ Term $ iDefine var $ mkBegin body
             | Just (List (Term (h :&: _ :^: _)) args (isNilTerm -> True)) <- proj argList,
               Just (K funcName@(Symbol _)) <- proj h -> do
               args' <- parseArgs args
               return $
                 Term $ iDefine funcName $
                 Term $ iLambda args' $ mkBegin body
             | otherwise ->
               errSexp "invalid define form"
        | otherwise ->
          errSexp "invalid define form"
      Just (K (Symbol "if"))    ->
        threeArgs iIf "invalid if form"
      Just (K (Symbol "begin")) ->
        return $ mkBegin xs
      Just (K (Symbol "let"))
        | not (V.null xs)
        , Term (bindings :&: _ :^: _) <- V.head xs
        , body                        <- V.tail xs ->
          if | Just (List h' xs' (isNilTerm -> True)) <- proj bindings -> do
               bindings' <- V.mapM destructLetBinding $ V.cons h' xs'
               let bindings'' = V.map (second Hole) bindings'
               return $ Term $ iLet bindings'' $ mkBegin body
             | isNil bindings ->
               return $ Term $ iLet V.empty $ mkBegin body
             | otherwise ->
               errSexp "invalid let form"
        | otherwise ->
          errSexp "invalid let form"
      Just (K (Symbol "cond"))  -> do
        (clauses, elseClause) <- destructCondClauses xs
        return $ Term $ iCond clauses elseClause
      Just (K (Symbol "and"))   ->
        twoArgs iAnd "invalid and form"
      Just (K (Symbol "or"))    ->
        twoArgs iOr "invalid or form"
      Just (K (Symbol "not"))   ->
        singleArg iNot "invalid not form"
      _                         ->
        return $ symToSym' $ iApply hExpr $ V.map (annLast . unTerm) xs
     where
       errSexp :: Text -> Err a
       errSexp msg = err sexpPos msg $ inj sexp
       err :: Position -> Text -> SchemeSexpF (Term (SchemeSexpF :&: p)) -> Err a
       err pos msg sexp =
         errorAt pos $ msg <> ": " <> showSexp (Term $ fmap stripA sexp)
       mkBegin :: Vector (Term (a :&: U Position :*: Term (h :&: U Position))) -> Context h (Term (h :&: U Position))
       mkBegin = symToSym' . iBegin . V.map (annLast . unTerm)
       parseArgs :: Vector (Term (SchemeSexpF :&: U Position :*: a)) -> Err (Vector Symbol)
       parseArgs = V.mapM (toSymbol "invalid function argument" . stripA)
       singleArg :: (Term (h :&: U Position) -> h (Term (h :&: U Position)))
                 -> Text
                 -> Err (Context h (Term (h :&: U Position)))
       singleArg cons msg =
         case V.map (annLast . unTerm) xs of
           [x] -> return $ symToSym' $ cons x
           _   -> errSexp msg
       twoArgs :: (Term (h :&: U Position) -> Term (h :&: U Position) -> h (Term (h :&: U Position)))
               -> Text
               -> Err (Context h (Term (h :&: U Position)))
       twoArgs cons msg =
         case V.map (annLast . unTerm) xs of
           [x, y] -> return $ symToSym' $ cons x y
           _      -> errSexp msg
       threeArgs :: (Term (h :&: U Position) -> Term (h :&: U Position) -> Term (h :&: U Position) -> h (Term (h :&: U Position)))
                 -> Text
                 -> Err (Context h (Term (h :&: U Position)))
       threeArgs cons msg =
         case V.map (annLast . unTerm) xs of
           [x, y, z] -> return $ symToSym' $ cons x y z
           _         -> errSexp msg

       destructLetBinding :: Term (SchemeSexpF :&: U Position :*: Term (h :&: U Position)) -> Err (Symbol, Term (h :&: U Position))
       destructLetBinding (Term (binding :&: bindPos :^: _)) =
         case proj binding of
           Just (List (Term (origNameExpr :&: origNameExprPos :^: _))
                      [Term (_ :^: valExpr)]
                      (isNilTerm -> True)) ->
             case proj origNameExpr of
               Just (K sym@(Symbol _)) -> return (sym, valExpr)
               _                       ->
                 err origNameExprPos "invalid bound variable name in let form" origNameExpr
           _                               ->
             err bindPos "invalid let form binding" binding
       destructCondClauses :: Vector (Term (SchemeSexpF :&: U Position :*: Term (h :&: U Position)))
                           -> Err ( Vector ( Context h (Term (h :&: U Position))
                                           , Context h (Term (h :&: U Position))
                                           )
                                  , Maybe (Context h (Term (h :&: U Position)))
                                  )
       destructCondClauses xs =
         V.foldM go (V.empty, Nothing) xs
         where
           go (clauses, elseClause) (Term (clause :&: clausePos :^: _)) =
             case elseClause of
               Nothing ->
                 case proj clause of
                   Just (List (Term (cond :&: _ :^: condition))
                              body
                              (isNilTerm -> True))
                     | Just (K (Symbol "else")) <- proj cond ->
                       return (clauses, Just (mkBegin body))
                     | otherwise ->
                       let newClause = (symToSym' $ remA $ unTerm condition, mkBegin body)
                       in  return (V.cons newClause clauses, elseClause)
                   _                               ->
                     err clausePos "invalid cond form clause" clause
               Just _ -> err clausePos "invalid cond form clause after the else clause" clause

       toSymbol :: (K Symbol :<: g, Pretty (Term g)) => Text -> Term g -> Err Symbol
       toSymbol errMsg t =
         case project t of
           Just (K sym@(Symbol _)) -> return sym
           _                       -> throwError $ errMsg <>
                                      ", symbol expected: " <> showSexp t
  getProgramAlg sexpPos x =
    errorAt sexpPos $ "cannot exctract program from " <>
    showSexp (inject $ fmap stripA x :: SchemeSexp)

instance (Vect :<: h) => GetProgram Vect h where
  getProgramAlg _ (Vect vs) =
    return . symToSym' . iVect $ V.map (annLast . unTerm) vs

getProgram :: Term (SchemeSexpF :&: U Position)
           -> Either Text (Term (SchemeExprF :&: U Position))
getProgram = -- runIdentity . runErrorT .
             runErr . histoFutuMAnn getProgramAlg

