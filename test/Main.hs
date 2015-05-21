----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fcontext-stack=100 #-}

module Main where

import Control.Applicative
import Data.Maybe (isJust)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import qualified Data.Vector as V
import Test.Tasty
-- import Test.Tasty.SmallCheck as SC
-- import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

-- import Text.ParserCombinators.UU
-- import Text.ParserCombinators.UU.Utils

import ALaCarte
import Eval
import Eval.ExtractProgram
import Eval.Desugar
import Types
-- import Parse
import SexpFrontend.Parser

projectsTo :: forall f g. (f :<: g) => Term g -> f (Term g) -> Assertion
projectsTo t _ = assertBool "projectsTo failed" $
                 isJust $ (project t :: Maybe (f (Term g)))

tests :: TestTree
tests = testGroup "Tests" [parserTests, extractorTests, evalTests]

testParseTerm :: Text -> SchemeSexp
testParseTerm source = either (error . T.unpack) id $ stripA <$> parseTerm "test" source

parserTests :: TestTree
parserTests = testGroup "Parser tests"
  [ testCase "Parse integer" $
    testParseTerm "1" @?= Term (iAInt 1)
  , testCase "Parse nil" $
    testParseTerm "nil" @?= Term iNil
  , testCase "Parse double" $
    projectsTo (testParseTerm "1.1" :: SchemeSexp) (K $ ADouble undefined)
  , testCase "Parse symbol" $
    testParseTerm "foo" @?= Term (iSymbol "foo")
  , testCase "Parse cons pair" $
    testParseTerm "(foo . bar)" @?=
    Term
     (iList
       (Term $ iSymbol "foo")
       []
       (Term $ iSymbol "bar"))
  , testCase "Parse sample sexp" $
    testParseTerm "(1 #t \"foo\" . foo)" @?=
    Term
      (iList
        (Term $ iAInt 1)
        [ Term $ iABool True
        , Term $ iAString "foo"
        ]
        (Term $ iSymbol "foo"))
  -- , testCase "Parse space in list" $
  --   testParseTerm "(1foo)" @?=
  --   (Term $ iList
  --             (Term $ iAInt 1)
  --             [ Term $ iABool True
  --             , Term $ iAString "foo"
  --             ]
  --             (Term $ iSymbol "foo")
  --             :: SchemeSexp)
  , testCase "Parse empty sexp" $
    testParseTerm "()" @?= Term iNil
  , testCase "Parse tricky sexp that tries to look like dotted list" $
    testParseTerm "(foo .bar baz)" @?=
    Term
      (iList
        (Term $ iSymbol "foo")
        [ Term $ iSymbol ".bar"
        , Term $ iSymbol "baz"
        ]
        (Term iNil))
  , testCase "Parse singleton int sexp" $
    testParseTerm "(10)" @?=
    Term
      (iList
        (Term $ iAInt 10)
        []
        (Term iNil))
  , testCase "Parse two-element int sexp" $
    testParseTerm "(10 20)" @?=
    Term
      (iList
        (Term $ iAInt 10)
        [Term $ iAInt 20]
        (Term iNil))
  , testCase "Parse two-element int dot-list sexp" $
    testParseTerm "(10 20 . 30)" @?=
    Term
      (iList
         (Term $ iAInt 10)
         [Term $ iAInt 20]
         (Term $ iAInt 30))
  , testCase "Parse singleton vector" $
    testParseTerm "#(1)" @?=
    Term (iVect [Term $ iAInt 1])
  , testCase "Parse sample vector" $
    testParseTerm "#(1 2 #t)" @?=
    Term
      (iVect
         [ Term $ iAInt 1
         , Term $ iAInt 2
         , Term $ iABool True
         ])
  ]

testExtractTerm :: Text -> Either Text SchemeExpr
testExtractTerm source =
  stripA <$> (getProgram =<< parseTerm "test" source)

isRight :: (Show a, Show b, Eq b) => Either a b -> b -> Assertion
isRight (Right x)   y = x @?= y
isRight v@(Left _)  _ = assertFailure $ "isRight failed: " ++ show v

isLeft :: (Show a, Show b) => Either a b -> Assertion
isLeft (Left _)    = return () -- success
isLeft v@(Right _) = assertFailure $ "isLeft failed: " ++ show v

extractorTests :: TestTree
extractorTests = testGroup "Extractor tests"
  [ testCase "Extract atom" $
    testExtractTerm "foo" @?= Right (Term (iSymbol "foo"))
  , testCase "Extract let" $
    isRight
      (testExtractTerm "(let ((x 1) (y 2)) (+ x y))")
      (Term
        (iLet
          [ (Symbol "x", Term (iAInt 1))
          , (Symbol "y", Term (iAInt 2))
          ]
          (Term
            (iBegin
              [ Term
                 (iApply (Term (iSymbol "+"))
                         [ Term (iSymbol "x")
                         , Term (iSymbol "y")
                         ])
              ]))))
  , testCase "Extract and" $
    isRight
      (testExtractTerm "(and foo bar)")
      (Term
        (iAnd
          (Term (iSymbol "foo"))
          (Term (iSymbol "bar"))))
  , testCase "Extract and error #1" $
    isLeft (testExtractTerm "(and foo bar baz)")
  , testCase "Extract and error #2" $
    isLeft (testExtractTerm "(and foo)")
  , testCase "Extract and error #3" $
    isLeft (testExtractTerm "(and)")
  , testCase "Extract set!" $
    isRight
      (testExtractTerm "(set! foo bar)")
      (Term (iAssign (Symbol "foo") (Term (iSymbol "bar"))))
  , testCase "Extract set! error #1" $
    isLeft (testExtractTerm "(set!)")
  , testCase "Extract set! error #2" $
    isLeft (testExtractTerm "(set! foo)")
  , testCase "Extract set! error #3" $
    isLeft (testExtractTerm "(set! foo bar baz)")
  ]

testEvalTerm :: Text -> Either Text (SchemeVal (SchemeCoreExprF :&: U Position))
testEvalTerm source =
  evalPipeline =<< parseTerm "test" source

evalTests :: TestTree
evalTests = testGroup "Eval tests"
  [ testCase "self-evaluating integers" $
    isRight
      (testEvalTerm "1")
      (Term (iAInt 1))
  , testCase "self-evaluating nil" $
    isRight
      (testEvalTerm "nil")
      (Term iNil)
  , testCase "self-evaluating double" $
    isRight
      (testEvalTerm "1.5")
      (Term (iADouble 1.5))
  , testCase "self-evaluating string" $
    isRight
      (testEvalTerm "\"foo\"")
      (Term (iAString "foo"))
  , testCase "assignment" $
    isRight
      (testEvalTerm "(begin (set! x 1) x)")
      (Term (iAInt 1))
  , testCase "define" $
    isRight
      (testEvalTerm "(begin (define x 1) x)")
      (Term (iAInt 1))
  , testCase "define function" $
    isRight
      (testEvalTerm "(begin (define (f x) (+ x 1)) (f 10))")
      (Term (iAInt 11))
  , testCase "define recursive function" $
    isRight
      (testEvalTerm "(begin (define (f x) (if (eq? x 0) x (f (- x 1)))) (f 10))")
      (Term (iAInt 0))
  , testCase "define and assignment" $
    isRight
      (testEvalTerm "(begin (define x 1) (set! x 2) x)")
      (Term (iAInt 2))
  , testCase "lambda application" $
    isRight
      (testEvalTerm "((lambda (x y) x) 1 2)")
      (Term (iAInt 1))
  , testCase "factorial" $
    isRight
      (testEvalTerm "(begin                           \
                    \  (define (factorial n)          \
                    \    (if (eq? n 0)                \
                    \      1                          \
                    \      (* n (factorial (- n 1)))))\
                    \  (factorial 6))")
      (Term (iAInt 720))
  , testCase "if #1" $
    isRight
      (testEvalTerm "(if #t 1 2)")
      (Term (iAInt 1))
  , testCase "if #2" $
    isRight
      (testEvalTerm "(if #f 1 2)")
      (Term (iAInt 2))
  , testCase "lambda counter with state" $
    isRight
      (testEvalTerm "(let ((counter              \
                    \        (let ((x 1))        \
                    \          (lambda ()        \
                    \            (set! x (+ x 1))\
                    \            x))))           \
                    \    (counter)               \
                    \    (counter)               \
                    \    (counter)               \
                    \    (counter))")
      (Term (iAInt 5))
  , testCase "global environment is mutable" $
    isRight
      (testEvalTerm "(begin \
                    \  (define (f) x)\
                    \  (define x 0)\
                    \  (f))")
      (Term (iAInt 0))
  , testCase "or" $
    isRight
      (testEvalTerm "(or #t #f)")
      (Term (iABool True))
  , testCase "and" $
    isRight
      (testEvalTerm "(and #t #f)")
      (Term (iABool False))
  , testCase "or short-circuit #1" $
    isRight
      (testEvalTerm "(begin (define foo 1) (or #t (set! foo 2)) foo)")
      (Term (iAInt 1))
  , testCase "or short-circuit #2" $
    isRight
      (testEvalTerm "(begin (define foo 1) (or #f (set! foo 2)) foo)")
      (Term (iAInt 2))
  , testCase "and short-circuit #1" $
    isRight
      (testEvalTerm "(begin (define foo 1) (and #f (set! foo 2)) foo)")
      (Term (iAInt 1))
  , testCase "and short-circuit #2" $
    isRight
      (testEvalTerm "(begin (define foo 1) (and #t (set! foo 2)) foo)")
      (Term (iAInt 2))
  , testCase "sum #1" $
    isRight
      (testEvalTerm "(+ 1 2 3 4)")
      (Term (iAInt 10))
  , testCase "sum #2" $
    isRight
      (testEvalTerm "(+)")
      (Term (iAInt 0))
  , testCase "product #1" $
    isRight
      (testEvalTerm "(* 1 2 3 4)")
      (Term (iAInt 24))
  , testCase "product #2" $
    isRight
      (testEvalTerm "(*)")
      (Term (iAInt 1))
  , testCase "difference" $
    isRight
      (testEvalTerm "(- 1 2 3 4)")
      (Term (iAInt (-8)))
  , testCase "difference err #1" $
    isLeft (testEvalTerm "(-)")
  , testCase "division" $
    isRight
      (testEvalTerm "(/ 3 2)")
      (Term (iADouble 1.5))
  , testCase "division err #1" $
    isLeft (testEvalTerm "(/ 3)")
  , testCase "division err #2" $
    isLeft (testEvalTerm "(/ 3 2 1)")
  , testCase "division err #3" $
    isLeft (testEvalTerm "(/)")
  , testCase "null? #1" $
    isRight
      (testEvalTerm "(null? #t)")
      (Term (iABool False))
  , testCase "null? #2" $
    isRight
      (testEvalTerm "(null? nil)")
      (Term (iABool True))
  , testCase "cons #1" $
    isRight
      (testEvalTerm "(cons 1 2)")
      (Term (iList (Term (iAInt 1)) V.empty (Term (iAInt 2))))
  , testCase "cons #2" $
    isRight
      (testEvalTerm "(cons 1 (cons 2 3))")
      (Term (iList (Term (iAInt 1)) (V.singleton (Term (iAInt 2))) (Term (iAInt 3))))
  , testCase "cons #3" $
    isRight
      (testEvalTerm "(cons 1 (cons 2 (cons 3 nil)))")
      (Term (iList
               (Term (iAInt 1))
               (V.fromList [Term (iAInt 2), Term (iAInt 3)])
               (Term iNil)))
  , testCase "cons err #1" $
    isLeft (testEvalTerm "(cons 1 2 3)")
  , testCase "cons err #2" $
    isLeft (testEvalTerm "(cons 1)")
  , testCase "cons err #3" $
    isLeft (testEvalTerm "(cons)")
  , testCase "car #1" $
    isRight
      (testEvalTerm "(car (cons 1 2))")
      (Term (iAInt 1))
  , testCase "car err #1" $
    isLeft (testEvalTerm "(car 1)")
  , testCase "car err #2" $
    isLeft (testEvalTerm "(car (cons 1 2) 3)")
  , testCase "car err #3" $
    isLeft (testEvalTerm "(car)")
  , testCase "cdr #1" $
    isRight
      (testEvalTerm "(cdr (cons 1 2))")
      (Term (iAInt 2))
  , testCase "cdr err #1" $
    isLeft (testEvalTerm "(cdr 1)")
  , testCase "cdr err #2" $
    isLeft (testEvalTerm "(cdr (cons 1 2) 3)")
  , testCase "cdr err #3" $
    isLeft (testEvalTerm "(cdr)")
  ]

main :: IO ()
main = defaultMain tests

