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

{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverlappingInstances       #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# LANGUAGE InstanceSigs #-}

{-# OPTIONS_GHC -fcontext-stack=100 #-}

module MCEval where

import Control.Arrow
import Control.Applicative
import Control.Monad.Error hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Monad.State hiding (mapM)
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Data.Monoid
import Data.Text.Lazy (Text)
-- import Data.Traversable (mapM)
import Data.Vector (Vector)
import qualified Data.Vector as V

import Text.PrettyPrint.Leijen.Text (Pretty, Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import ALaCarte
import Types
import Utils

import Prelude hiding (mapM)


newtype Err a = Err { runErr :: Either Text a } -- ErrorT Text Identity a
              deriving (Functor, Applicative, Monad, MonadError Text)


--- Translate from one sum type into another.

class Translate f g where
  translateAlg :: f (Term g) -> Term g

instance (f :<: h, Translate g h) => Translate (f :+: g) h where
  translateAlg (Inl x) = translateAlg x
  translateAlg (Inr y) = translateAlg y

instance (f :<: g) => Translate f g where
  translateAlg = inject

retranslate :: (Translate f g, Functor f) => Term f -> Term g
retranslate = cata translateAlg

--- prettyprinter for scheme sexps

showSexp :: (Pretty a) => a -> Text
showSexp = PP.displayT . PP.renderPretty 0.8 80 . PP.pretty

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
      (_, Just (K Nil))  -> PP.parens $ x PP.<+> PP.align (PP.sep $ V.toList $ V.map fst xs)
      (_, Nothing)       -> PP.parens $ x PP.<+> PP.align (PP.sep $ V.toList (V.map fst xs) ++ [PP.dot, t])
instance PrettyAlg Vect g where
  prettyAlg (Vect xs) =
    PP.text "#(" <> PP.cat (V.toList $ V.map fst xs) <> PP.text ")"
instance Pretty SchemeSexp where
  pretty = para prettyAlg


-- instance Error Text where
--   noMsg  = T.empty
--   strMsg = T.pack

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
      Just (K (Symbol "quote"))  ->
        case V.map (unTerm . stripA) xs of
          [x] -> return $ symToSym' $ iQuote $ Term x
          _   -> errSexp "invalid quote form"
      Just (K (Symbol "set!"))
        | [Term (var :&: _ :^: _), Term (_ :&: _ :^: val)] <- xs
        , Just (K sym@(Symbol _))                          <- proj var ->
        return $ symToSym' $ iAssign sym val
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
      Just (K (Symbol "if"))     ->
        threeArgs iIf "invalid if form"
      Just (K (Symbol "begin"))  ->
        return $ mkBegin xs
      Just (K (Symbol "let"))
        | not (V.null xs)
        , Term (bindings :&: _ :^: _) <- V.head xs
        , body                        <- V.tail xs ->
          if | Just (List h' xs' (isNilTerm -> True)) <- proj bindings -> do
               bindings' <- V.mapM destructLetBinding $ V.cons h' xs'
               let bindings'' = V.map (id *** Hole) bindings'
               return $ Term $ iLet bindings'' $ mkBegin body
             | isNil bindings ->
               return $ Term $ iLet V.empty $ mkBegin body
             | otherwise ->
               errSexp "invalid let form"
        | otherwise ->
          errSexp "invalid let form"
      Just (K (Symbol "cond"))  -> do
        clauses <- V.mapM destructCondClause xs
        return $ Term $ iCond clauses
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
         throwError $ showPos pos <> msg <> ": " <> showSexp (Term $ fmap stripA sexp)
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
                      (isNilTerm -> True)) -> do
             case proj origNameExpr of
               Just (K sym@(Symbol _)) -> return (sym, valExpr)
               _                       ->
                 err origNameExprPos "invalid bound variable name in let form" origNameExpr
           _                               ->
             err bindPos "invalid let form binding" binding
       destructCondClause :: Term (SchemeSexpF :&: U Position :*: Term (h :&: U Position)) ->
                             Err (Context h (Term (h :&: U Position)), Context h (Term (h :&: U Position)))
       destructCondClause (Term (clause :&: clausePos :^: _)) =
         case proj clause of
           Just (List (Term (_ :^: condition))
                      body
                      (isNilTerm -> True)) ->
             return (symToSym' $ remA $ unTerm condition, mkBegin body)
           _                               ->
             err clausePos "invalid cond form clause" clause

       toSymbol :: (K Symbol :<: g, Pretty (Term g)) => Text -> Term g -> Err Symbol
       toSymbol errMsg t =
         case project t of
           Just (K sym@(Symbol _)) -> return sym
           _                       -> throwError $ errMsg <>
                                      ", symbol expected: " <> showSexp t
  getProgramAlg sexpPos x =
    throwError $ showPos sexpPos <> "cannot exctract program from " <>
    showSexp (inject $ fmap stripA x :: SchemeSexp)

instance (Vect :<: h) => GetProgram Vect h where
  getProgramAlg _ (Vect vs) =
    return . symToSym' . iVect $ V.map (annLast . unTerm) vs

getProgram :: Term (SchemeSexpF :&: U Position)
           -> Either Text (Term (SchemeExprF :&: U Position))
getProgram = -- runIdentity . runErrorT .
             runErr . histoFutuMAnn getProgramAlg

-- Desugarer

desugar :: Term (SchemeExprF :&: U Position) -> Term (SchemeCoreExprF :&: U Position)
desugar = termHomAnn desugarAlg

class Desugar f h where
  desugarAlg :: TermHom f h

instance (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
  desugarAlg (Inl f) = desugarAlg f
  desugarAlg (Inr g) = desugarAlg g

instance (f :<: h) => Desugar f h where
  desugarAlg f = Term $ inj $ fmap Hole f

instance (If :<: h, K Nil :<: h) => Desugar Cond h where
  desugarAlg (Cond cases) =
    V.foldr
      (\(test, body) ifFalse -> Term $ iIf (Hole test) (Hole body) ifFalse)
      (Term iNil)
      cases

-- Evaluator

data EvalState v = EvalState
  { evalStateMem       :: Memory v
  , evalStateFreshAddr :: Int
  , evalStateCurrFrame :: Frame
  }
  deriving (Show, Eq, Ord)

addNewObject :: Symbol -> v -> EvalState v -> EvalState v
addNewObject sym obj (EvalState {evalStateMem, evalStateFreshAddr, evalStateCurrFrame}) =
  EvalState evalStateMem' evalStateFreshAddr' evalStateCurrFrame'
  where
    addr                = Address evalStateFreshAddr
    evalStateMem'       = addToMemory addr obj evalStateMem
    evalStateFreshAddr' = evalStateFreshAddr + 1
    evalStateCurrFrame' = addToFrame sym addr evalStateCurrFrame

modifyObject :: Address -> v -> EvalState v -> EvalState v
modifyObject addr obj s =
  s { evalStateMem = addToMemory addr obj $ evalStateMem s }

newtype EvalM v a =
  EvalM (ReaderT Env (StateT (EvalState v) Err) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader Env
           , MonadState (EvalState v)
           , MonadError Text
           )

withNewFrame :: EvalM v a -> EvalM v a
withNewFrame action = do
  frame <- gets evalStateCurrFrame
  modify (\s -> s { evalStateCurrFrame = Frame M.empty })
  res <- local (addFrame frame) action
  modify (\s -> s { evalStateCurrFrame = frame })
  return res

inEnv :: Env -> EvalM v a -> EvalM v a
inEnv env action = do
  frame <- gets evalStateCurrFrame
  modify (\s -> s { evalStateCurrFrame = Frame M.empty })
  res <- local (const env) action
  modify (\s -> s { evalStateCurrFrame = frame })
  return res

runEvalM :: EvalM v a -> [(Symbol, v)] -> Either Text a
runEvalM (EvalM action) initBindings =
  runErr $ evalStateT (runReaderT action initEnv) emptyState
  where
    emptyState = EvalState (Memory mem) freeAddress (Frame M.empty)
    initEnv    = Env $ V.singleton $ Frame frame
    (freeAddress, frame, mem) =
      foldr
        (\(sym, val) (n, frame, mem) ->
           (n + 1 , M.insert sym (Address n) frame , IM.insert n val mem))
        (0, M.empty, IM.empty)
        initBindings

-- eval :: (Functor f, EvalProgram f f h) => Term (f :&: U Position) -> Either Text (Term h)
eval :: Term (SchemeCoreExprF :&: U Position) -> Either Text (SchemeVal (SchemeCoreExprF :&: U Position))
eval term = runEvalM (paraAnn evalProgramAlg term) initBindings
  where
    initBindings :: [(Symbol, SchemeVal (SchemeCoreExprF :&: U Position))]
    initBindings = [ (Symbol "+", Term iPrimitiveAdd)
                   , (Symbol "-", Term iPrimitiveSub)
                   , (Symbol "*", Term iPrimitiveMul)
                   , (Symbol "/", Term iPrimitiveDiv)
                   ]

class EvalProgram f g h where
  evalProgramAlg :: Position
                 -> f (EvalM (Term h) (Term h), Term (g :&: U Position))
                 -> EvalM (Term h) (Term h)

instance (EvalProgram f g h, EvalProgram f' g h) => EvalProgram (f :+: f') g h where
  evalProgramAlg p (Inl x) = evalProgramAlg p x
  evalProgramAlg p (Inr y) = evalProgramAlg p y

instance (K Nil :<: h) => EvalProgram (K Nil) g h where
  evalProgramAlg _ (K Nil) =
    return $ Term iNil

instance (K ABool :<: h) => EvalProgram (K ABool) g h where
  evalProgramAlg _ (K (ABool x)) =
    return $ Term $ iABool x

instance (K AString :<: h) => EvalProgram (K AString) g h where
  evalProgramAlg _ (K (AString x)) =
    return $ Term $ iAString x

instance (K ADouble :<: h) => EvalProgram (K ADouble) g h where
  evalProgramAlg _ (K (ADouble x)) =
    return $ Term $ iADouble x

instance (K AInt :<: h) => EvalProgram (K AInt) g h where
  evalProgramAlg _ (K (AInt x)) =
    return $ Term $ iAInt x

lookupInEnvM :: (MonadReader Env m, MonadState (EvalState v) m, MonadError Text m)
             => Symbol
             -> m (Maybe Address)
lookupInEnvM sym = do
  currFrame <- gets evalStateCurrFrame
  env       <- ask
  return $ lookupInEnv sym currFrame env

instance EvalProgram (K Symbol) g h where
  evalProgramAlg pos (K sym) = do
    mem  <- gets evalStateMem
    addr <- maybe err return =<< lookupInEnvM sym
    maybe err' return $ lookupMem addr mem
    where
      err = throwError $ showPos pos <> "unbound variable: " <> getSymbol sym
      err' = throwError $ showPos pos <> "bound variable absent in mem: " <> getSymbol sym

instance (Vect :<: h) => EvalProgram Vect g h where
  evalProgramAlg _ (Vect xs) =
    Term . iVect <$> V.mapM fst xs

instance (Functor g, K (Closure (g :&: U Position)) :<: h) => EvalProgram Lambda g h where
  evalProgramAlg _ (Lambda args (_, body)) = do
    currFrame <- gets evalStateCurrFrame
    env       <- ask
    return $ Term $ iClosure (addFrame currFrame env) args body

instance (ToConstraint SchemeSexpF h) => EvalProgram (K Quote) g h where
  evalProgramAlg _ (K (Quote sexp)) = return $ retranslate sexp

instance (K Nil :<: h, Show (Term h)) => EvalProgram Assign g h where
  evalProgramAlg pos (Assign var (val, _)) = do
    val' <- val
    addr <- lookupInEnvM var
    case addr of
      Nothing -> do
        modify (addNewObject var val')
      Just addr -> do
        modify (modifyObject addr val')
    return $ Term iNil

instance (K Nil :<: h) => EvalProgram Define g h where
  evalProgramAlg pos (Define sym (body, _)) = do
    addr <- lookupInEnvM sym
    case addr of
      Nothing -> do
        val <- body
        modify (addNewObject sym val)
        return $ Term iNil
      Just _ -> do
        throwError $ showPos pos <> " define cannot overwrite already set symbol " <> show' sym

instance (K ABool :<: h, K Nil :<: h) => EvalProgram If g h where
  evalProgramAlg _ (If (cond, _) (true, _) (false, _)) = do
    cond' <- cond
    if booleanValue cond'
      then true
      else false

instance (K Nil :<: h) => EvalProgram Begin g h where
  evalProgramAlg _ (Begin body) = do
    V.sequence_ $ V.init body'
    V.last body'
    where
      body' = V.map fst body

class Applicable f h where
  apply :: Position
        -> f (Term h)
        -> Vector (Term h)
        -> EvalM (Term h) (Term h)

instance (Applicable f h, Applicable g h) => Applicable (f :+: g) h where
  apply p (Inl f) args = apply p f args
  apply p (Inr g) args = apply p g args

instance (Functor g, EvalProgram g g h) =>
         Applicable (K (Closure (g :&: U Position))) h where
  apply pos (K (Closure env args body)) values = do
    inEnv env $ do
      populateFrame
      paraAnn evalProgramAlg body
    where
      populateFrame :: (MonadError Text m, MonadState (EvalState (Term h)) m) => m ()
      populateFrame
        | argCount == valCount = do
          modify $ \state ->
            V.foldr
              (\(arg, val) -> addNewObject arg val)
              state
              (V.zip args values)
        | otherwise                  =
          throwError msg
      msg = showPos pos <> "wrong number of arguments supplied for lambda: " <>
            "expected " <> show' argCount <> " but got " <> show' valCount
      argCount = V.length args
      valCount = V.length values

arith :: forall m h. (MonadError Text m, K AInt :<: h, K ADouble :<: h, Show (Term h))
      => Position
      -> (forall a. (Num a) => a -> a -> a)
      -> (forall a. (Num a) => a)
      -> (Double -> Double -> Double)
      -> Vector (Term h)
      -> m (Term h)
arith pos f def combine args = do
  (ints, doubles, isInt) <- V.foldM add (def, def, True) args
  if isInt
    then return $ Term $ iAInt ints
    else return $ Term $ iADouble $ combine (fromIntegral ints) doubles
  where
    add :: (MonadError Text m) => (Integer, Double, Bool) -> Term h -> m (Integer, Double, Bool)
    add (ints, doubles, isInt) v
      | Just (K (AInt n))    <- proj (unTerm v)
      = return (f ints n, doubles,     isInt)
      | Just (K (ADouble d)) <- proj (unTerm v)
      = return (ints,     f doubles d, False)
      | otherwise
      = throwError $ showPos pos <> "cannot add non-number " <> show' v

instance (K AInt :<: h, K ADouble :<: h, Show (Term h)) => Applicable (K PrimitiveAdd) h where
  apply pos (K PrimitiveAdd) values = arith pos (+) 0 (+) values

instance (K AInt :<: h, K ADouble :<: h, Show (Term h)) => Applicable (K PrimitiveSub) h where
  apply pos (K PrimitiveSub) values = arith pos (-) 0 (+) values

instance (K AInt :<: h, K ADouble :<: h, Show (Term h)) => Applicable (K PrimitiveMul) h where
  apply pos (K PrimitiveMul) values = arith pos (*) 1 (*) values

-- instance (K AInt :<: h, K ADouble :<: h, Show (Term h)) => Applicable (K PrimitiveDiv) h where
--   apply pos (K PrimitiveDiv) [Term a, Term b] =
--     arith pos (/) values

instance (Show (f (Term h)), Show (Term h)) => Applicable f h where
  apply pos expr args =
    throwError $ showPos pos <> "cannot apply " <> show' expr <>
    " to args " <> show' args

instance (Applicable h h) => EvalProgram Apply g h where
  evalProgramAlg pos (Apply (func, _) args) = do
    func' <- func
    args' <- V.mapM fst args
    apply pos (unTerm func') args'

instance EvalProgram Let g h where
  evalProgramAlg pos (Let bindings (body, _)) = do
    bindings' <- V.mapM (\(sym, (v, _)) -> (sym, ) <$> v) bindings
    withNewFrame $ do
      populateFrame bindings'
      body
    where
      populateFrame :: (MonadState (EvalState (Term h)) m) => Vector (Symbol, Term h) -> m ()
      populateFrame bindings =
        modify $ \state -> V.foldr (\(sym, v) -> addNewObject sym v) state bindings

booleanValue :: (K ABool :<: f, K Nil :<: f) => Term f -> Bool
booleanValue (Term x)
  | Just (K (ABool b)) <- proj x = b
  | Just (K Nil)       <- proj x = False
  | otherwise                    = True

instance (K ABool :<: h, K Nil :<: h) => EvalProgram And g h where
  evalProgramAlg _ (And (x, _) (y, _)) = do
    x' <- x
    if booleanValue x'
    then do
      y' <- y
      return $ Term $ iABool $ booleanValue y'
    else return $ Term $ iABool False

instance (K ABool :<: h, K Nil :<: h) => EvalProgram Or g h where
  evalProgramAlg _ (Or (x, _) (y, _)) = do
    x' <- x
    if booleanValue x'
    then return $ Term $ iABool True
    else do
      y' <- y
      return $ Term $ iABool $ booleanValue y'

instance (K ABool :<: h, K Nil :<: h) => EvalProgram Not g h where
  evalProgramAlg _ (Not (x, _)) = do
    x' <- x
    return $ Term $ iABool $ not $ booleanValue x'

-- class TransformSchemeVal f h where
--   transformSchemeVal :: (e -> e') -> f e (Term (h e)) -> Term (h e)
--
-- instance (TransformSchemeVal f h, TransformSchemeVal g h) => TransformSchemeVal (f e :+: g) h where
--   transformSchemeVal transform (Inl f) = transformSchemeVal transform f
--   transformSchemeVal transform (Inr g) = transformSchemeVal transform g
--
-- instance (f :<: h) => TransformSchemeVal f h where
--   transformSchemeVal _ f = inject f

evalPipeline :: Term (SchemeSexpF :&: U Position) -> Either Text (SchemeVal (SchemeCoreExprF :&: U Position))
evalPipeline = getProgram >=> eval . desugar

-- main :: IO ()
-- main = do
--   print $ (runParser "test" parser "(foo)" :: SchemeSexp)

