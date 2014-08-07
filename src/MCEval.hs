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
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE UndecidableInstances  #-}

module MCEval where

import Control.Applicative
import Control.Arrow
import Control.Monad.Error
import Control.Monad.Identity
import Data.Foldable (Foldable)
-- import Data.IntMap (IntMap)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Text.Lazy (Text)
import Data.Traversable (Traversable)
-- import Text.ParserCombinators.Parsec
import Text.ParserCombinators.UU hiding (Apply, Hole)
import Text.ParserCombinators.UU.BasicInstances hiding (Error)
import Text.ParserCombinators.UU.Utils
import Text.PrettyPrint.Leijen.Text (Pretty, Doc)


-- import qualified Data.Foldable as Foldable
-- import qualified Data.IntMap as IM
-- import qualified Data.Map as M
import qualified Data.Text.Lazy as T
-- import qualified Data.Traversable as Trav
import qualified Text.PrettyPrint.Leijen.Text as PP

import ALaCarte
import ALaCarte.TH

import Prelude hiding (mapM)


-- newtype Fix f = Fix { unFix :: f (Fix f) }
--
-- deriving instance (Show (f (Fix f))) => Show (Fix f)
-- deriving instance (Eq (f (Fix f))) => Eq (Fix f)
-- deriving instance (Ord (f (Fix f))) => Ord (Fix f)
--
-- type Alg f a = f a -> a
--
-- cata :: (Functor f) => Alg f a -> Fix f -> a
-- cata alg = alg . fmap (cata alg) . unFix
--
-- para :: (Functor f) => (f (a, Fix f) -> a) -> Fix f -> a
-- para alg = alg . fmap (para alg &&& id) . unFix
--
-- -- para' :: forall f a. (Functor f) => (f (a, Fix f) -> a) -> Fix f -> a
-- -- -- para' alg = fst . cata (alg &&& Fix . fmap snd)
-- -- para' alg = fst . cata f
-- --   where
-- --     f :: f (a, Fix f) -> (a, Fix f)
-- --     f x = (alg x, Fix $ fmap snd x)
--
-- paraM :: forall m f a. (Monad m, Traversable f) => (f (a, Fix f) -> m a) -> Fix f -> m a
-- paraM alg = alg <=< Trav.mapM g . unFix
--   where
--     g :: Fix f -> m (a, Fix f)
--     g x = paraM alg x >>= return . (, x)

--- Basic types

newtype AInt    = AInt { getAInt :: Integer }
                deriving (Show, Eq, Ord)
newtype ADouble = ADouble { getADouble :: Double }
                deriving (Show, Eq, Ord)
newtype AString = AString { getAString :: Text }
                deriving (Show, Eq, Ord)
newtype ABool   = ABool { getABool :: Bool }
                deriving (Show, Eq, Ord)
data Nil        = Nil
                deriving (Show, Eq, Ord)

type AtomF = K AInt :+: K ADouble :+: K AString :+: K ABool :+: K Nil

-- data Atom = AInt Integer
--           | ADouble Double
--           | AString Text
--           | ABool Bool
--           | Nil
--           deriving (Show, Eq, Ord)

newtype Symbol = Symbol { getSymbol :: Text }
               deriving (Show, Eq, Ord)

data List f = List f [f] f
            deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Vector f = Vector [f]
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type SchemeSexpF = Vector :+: List :+: K Symbol :+: AtomF

type SchemeSexp = Term SchemeSexpF

nil :: (K Nil :<: f) => Term f
nil = inject $ K Nil


--- Parser/prettyprinter for scheme sexps

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

many1 :: (Alternative f) => f a -> f [a]
many1 p = ((:) <$> p <*> many p)

mandatorySpace :: Parser String
mandatorySpace = pMunch (`elem` " \r\n\t") <?> "Mandatory whitespace"

parens :: ParserTrafo a a
parens p = pSym '(' *> p <* pSym ')'

parseNumber :: forall f. (K AInt :<: f, K ADouble :<: f) => Parser (Term f)
parseNumber =
  f <$> (consMb <$> sign <*> num)
    <*> pMaybe ((:) <$> dot <*> num)
    <*> pMaybe ((:) <$> e <*> (consMb <$> sign <*> num))
  where
    f :: String -> Maybe String -> Maybe String -> Term f
    f x Nothing Nothing = inject . K . AInt . read $ x
    f x y       z       = inject . K . ADouble . read $ x ++ y' ++ z'
      where
        y' = fromMaybe "" y
        z' = fromMaybe "" z
    sign = pMaybe (pSym '-' <|> pSym '+')
    -- num  = many1 pDigit
    dot  = pSym '.'
    e    = pSym 'e' <|> pSym 'E'

    num = (:) <$> pSatisfy isDigit ins <*> pMunch isDigit
    isDigit c = '0' <= c && c <= '9'
    ins = Insertion "Inserting character" 'Z' 10

    consMb :: Maybe a -> [a] -> [a]
    consMb (Just x) xs = x : xs
    consMb Nothing  xs = xs

-- TODO allow for \" inside strings, recognize \\, \n etc
-- todo replace pQuotedString by other version that is not surrounded with
-- lexeme
parseAString :: (K AString :<: f) => Parser (Term f)
parseAString = inject . K . AString . T.pack <$> pQuotedString
parseABool :: (K ABool :<: f) => Parser (Term f)
parseABool = inject . K . ABool <$> (pSym '#' *> (pure True <* pSym 't' <|>
                                                  pure False <* pSym 'f'))
parseSymbol :: (K Nil :<: f, K Symbol :<: f) => Parser (Term f)
parseSymbol = f . T.pack <$> ((:) <$> nondigitC <*> anyC)
  where
    f "nil" = nil
    f x     = inject $ K $ Symbol x
    anyC = pMunch anySymbolChar
    anySymbolChar c =  nonDigitSymbolChar c ||
                      '0' <= c && c <= '9'

    nondigitC = pSatisfy nonDigitSymbolChar ins
    nonDigitSymbolChar c = 'a' <= c && c <= 'z' ||
                           'A' <= c && c <= 'Z' ||
                           c == '-' ||
                           c == '+' ||
                           c == '*' ||
                           c == '/' ||
                           c == '!' ||
                           c == '?' ||
                           c == '<' ||
                           c == '>' ||
                           c == '=' ||
                           c == '_'
    ins = Insertion "Inserting character" 'Z' 10
parseList :: (List :<: f, K Nil :<: f) => Parser (Term f) -> Parser (Term f)
parseList p = parens $
              -- (\h (body, t) -> inject $ List h body t) <$> p <*>
              --                                              (([],)  <$> (pDot *> p) <|>
              --                                               (,nil) <$> many p)
              maybe nil (\(h, body, t) -> inject $ List h body t) <$>
              pMaybe ((,,)    <$>
                      p'      <*>
                      many p' <*>
                      (pDot *> p <|>
                       pure nil))
  where
    p' = p <* mandatorySpace
-- TODO fix whitespace handling for vectors of one element, #(a) - space not
-- mandatory
parseVector :: (Vector :<: f) => Parser (Term f) -> Parser (Term f)
parseVector p = pSym '#' *> parens (inject . Vector <$> many (p <* mandatorySpace))


parseTerm :: (Vector :<: f, List :<: f, K Symbol :<: f,
              K AInt :<: f, K ADouble :<: f, K AString :<: f,
              K ABool :<: f, K Nil :<: f) =>
             Parser (Term f)
parseTerm = parseNumber <|>
            parseAString <|>
            parseABool <|>
            -- parseNil <|>
            parseSymbol <|>
            parseList parseTerm <|>
            parseVector parseTerm

--- Closer to evaluation

newtype Address = Address { getAddress :: Int }
                deriving (Show, Eq, Ord)

newtype Frame = Frame (Map Symbol Address)
              deriving (Show, Eq, Ord)

newtype Env = Env [Frame]
            deriving (Show, Eq, Ord)

-- data Lambda f = Lambda Env [Symbol] f
data Lambda f = Lambda [Symbol] f
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


data Primitive f = PrimitiveAdd f f
                 | PrimitiveSub f f
                 | PrimitiveMul f f
                 | PrimitiveDiv f f
                 | PrimitiveEq f f
                 -- Primitive Text ([SchemeData] -> f)
                 deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- instance Show (Primitive f) where
--   show (Primitive tag _) = "Primitive " ++ tag

-- instance Eq (Primitive f) where
--   Primitive tag _ == Primitive tag' _ = tag == tag'
--
-- instance Ord (Primitive f) where
--   compare (Primitive tag _) (Primitive tag' _) = compare tag tag'

-- data Variable = Variable Symbol
--               deriving (Show, Eq, Ord)

data Quote f = Quote f
            deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Assign f = Assign f f
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Define f = Define f f
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data If f = If f f f
          deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Begin f = Begin [f]
             deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Apply f = Apply f [f]
             deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Let f = Let [(f, f)] f
           deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


data Cond f = Cond [(f, f)]
            deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data And f = And f f
           deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Or f = Or f f
          deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Not f = Not f
           deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


type SchemeExprF = Not :+: Or :+: And :+: Cond :+: Let :+: Apply :+: Begin :+:
                   If :+: Define :+: Assign :+: Quote :+:
                   {-K Variable :+: Primitive :+:-} Lambda :+: SchemeSexpF
type SchemeExpr = Term SchemeExprF


type ErrT a = ErrorT Text Identity a

instance Error Text where
  noMsg  = T.empty
  strMsg = T.pack

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
class GetProgram f g h where
  -- getProgramAlg :: f (Term h, Term g) -> ErrT (Context h (Term h))
  getProgramAlg :: f (Term (g :&: Term h)) -> ErrT (Context h (Term h))

instance (GetProgram f g' h', GetProgram g g' h') => GetProgram (f :+: g) g' h' where
  getProgramAlg (Inl x) = getProgramAlg x
  getProgramAlg (Inr y) = getProgramAlg y

instance GetProgram (K AInt) SchemeSexpF SchemeExprF where
  getProgramAlg = return . symToSym . inject . K . unK
  -- getProgramAlg (K x@(AInt _))    = return . symToSym . inject $ K x
instance GetProgram (K ADouble) SchemeSexpF SchemeExprF where
  getProgramAlg = return . symToSym . inject . K . unK
instance GetProgram (K AString) SchemeSexpF SchemeExprF where
  getProgramAlg = return . symToSym . inject . K . unK
instance GetProgram (K ABool) SchemeSexpF SchemeExprF where
  getProgramAlg = return . symToSym . inject . K . unK
instance GetProgram (K Nil) SchemeSexpF SchemeExprF where
  getProgramAlg = return . symToSym . inject . K . unK
instance GetProgram (K Symbol) SchemeSexpF SchemeExprF where
  getProgramAlg = return . symToSym . inject . K . unK

isNil :: (K Nil :<: f) => Term (f :&: p) -> Bool
isNil (Term (t :&: _)) = case proj t of
                         Just (K Nil) -> True
                         Nothing      -> False

instance GetProgram List SchemeSexpF SchemeExprF where
  getProgramAlg (List (Term (hSexp :&: hExpr))
                      xs
                      (isNil -> True)) =
    case proj hSexp of
      Just (K (Symbol "lambda"))   ->
        case xs of
          Term (argList :&: _): body -> do
            case proj argList of
              Just (List h' xs' (isNil -> True)) -> do
                args <- mapM (toSymbol . stripAllTermAnn) $ h': xs'
                return . inject $ Lambda args $ mkBegin body
              _                                  ->
                case proj argList of
                  Just (K Nil) ->
                    return . inject $ Lambda [] $ mkBegin body
                  _            ->
                    throwError $ "invalid argument list of lambda form" <> prettySexp
          _                ->
            throwError $ "invalid lambda form" <> prettySexp
      Just (K (Symbol "quote"))  ->
        singleArg Quote "invalid quote form"
      Just (K (Symbol "set!"))   ->
        twoArgs Assign "invalid set! form"
      Just (K (Symbol "define")) ->
        twoArgs Define "invalid define form"
      Just (K (Symbol "if"))     ->
        threeArgs If "invalid if form"
      Just (K (Symbol "begin"))  ->
        return $ mkBegin xs
      Just (K (Symbol "let"))    ->
        case xs of
          (Term (bindings :&: _)): body ->
            case proj bindings of
              Just (List h' xs' (isNil -> True)) -> do
                bindings' <- mapM destructBinding $ h':xs'
                let bindings'' = map (Hole *** Hole) bindings'
                return . inject $ Let bindings'' $ mkBegin body
              _                                  ->
                case proj bindings of
                  Just (K Nil) -> do
                    return . inject $ Let [] $ mkBegin body
                  _            ->
                     throwError $ "invalid let form" <> prettySexp
          _                             ->
            throwError $ "invalid let form" <> prettySexp
      Just (K (Symbol "cond"))  -> do
        undefined
        -- clauses <- mapM (stripAnn . unTerm) xs
        -- return . symToSym . inject $ Cond $ map (ann . unTerm) clauses
      Just (K (Symbol "and"))   ->
        twoArgs And "invalid and form"
      Just (K (Symbol "or"))    ->
        twoArgs Or "invalid or form"
      Just (K (Symbol "not"))   ->
        singleArg Not "invalid not form"
      _                         ->
        return . symToSym . inject $ Apply hExpr $ map (ann . unTerm) xs
       -- Just (K (Symbol v)) -> inject $ Apply hExpr $ map (ann . unTerm) xs
     where
       prettySexp = ": " <> showSexp (inject $ List (stripAllAnn hSexp)
                                                    (map (stripAllAnn . stripAnn . unTerm) xs)
                                                    (inject $ K Nil))

       mkBegin body = symToSym . inject $ Begin $ map (ann . unTerm) body
       destructBinding :: (Term (SchemeSexpF :&: SchemeExpr)) -> ErrT (SchemeExpr, SchemeExpr)
       destructBinding binding@(Term (x :&: _)) =
         case proj x of
           Just (List (Term (origNameExpr :&: nameExpr))
                      [Term (_ :&: valExpr)]
                      (isNil -> True)) -> do
             case proj origNameExpr of
               Just (K (Symbol _)) -> return (nameExpr, valExpr)
               _                   ->
                 throwError $ "invalid bound variable name in let form" <> prettyBinding
           _                           ->
             throwError $ "invalid binding in let form" <> prettyBinding
         where
           prettyBinding = ": " <> showSexp (stripAllTermAnn binding)
       singleArg cons msg =
         case map (ann . unTerm) xs of
           [x] -> return . symToSym . inject $ cons x
           _   -> throwError $ msg <> prettySexp
       twoArgs cons msg =
         case map (ann . unTerm) xs of
           [x, y] -> return . symToSym . inject $ cons x y
           _      -> throwError $ msg <> prettySexp
       threeArgs cons msg =
         case map (ann . unTerm) xs of
           [x, y, z] -> return . symToSym . inject $ cons x y z
           _         -> throwError $ msg <> prettySexp

       toSymbol :: Term SchemeSexpF -> ErrT Symbol
       toSymbol t =
         case project t of
           Just (K sym@(Symbol _)) -> return sym
           _                       -> throwError $ "symbol expected: " <> showSexp t

instance GetProgram Vector SchemeSexpF SchemeExprF where
  getProgramAlg (Vector vs) =
    return . symToSym . inject $ Vector $ map (ann . unTerm) vs

getProgram :: SchemeSexp -> Either Text SchemeExpr
getProgram = runIdentity . runErrorT . histoFutuM getProgramAlg

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

$(deriveInjectingConstructor ''AInt)
$(deriveInjectingConstructor ''ADouble)
$(deriveInjectingConstructor ''AString)
$(deriveInjectingConstructor ''ABool)
$(deriveInjectingConstructor ''Nil)
$(deriveInjectingConstructor ''Symbol)
$(deriveInjectingConstructor ''List)
$(deriveInjectingConstructor ''Vector)
$(deriveInjectingConstructor ''Lambda)

$(deriveInjectingConstructor ''Quote)
$(deriveInjectingConstructor ''Assign)
$(deriveInjectingConstructor ''Define)
$(deriveInjectingConstructor ''If)
$(deriveInjectingConstructor ''Begin)
$(deriveInjectingConstructor ''Apply)
$(deriveInjectingConstructor ''Let)
$(deriveInjectingConstructor ''Cond)
$(deriveInjectingConstructor ''And)
$(deriveInjectingConstructor ''Or)
$(deriveInjectingConstructor ''Not)

