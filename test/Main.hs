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
import Test.Tasty
-- import Test.Tasty.SmallCheck as SC
-- import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

-- import Text.ParserCombinators.UU
-- import Text.ParserCombinators.UU.Utils

import ALaCarte
import MCEval
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
  , testCase "Extract and error" $
    isLeft (testExtractTerm "(and foo bar baz)")
  , testCase "Extract and error #2" $
    isLeft (testExtractTerm "(and foo)")
  , testCase "Extract and error #3" $
    isLeft (testExtractTerm "(and)")
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
  , testCase "assignment" $
    isRight
      (testEvalTerm "(begin (set! x 1) x)")
      (Term (iAInt 1))
  , testCase "define" $
    isRight
      (testEvalTerm "(begin (define x 1) x)")
      (Term (iAInt 1))
  , testCase "define and assignment" $
    isRight
      (testEvalTerm "(begin (define x 1) (set! x 2) x)")
      (Term (iAInt 2))
  , testCase "lambda application" $
    isRight
      (testEvalTerm "((lambda (x y) x) 1 2)")
      (Term (iAInt 1))
  , testCase "sum" $
    isRight
      (testEvalTerm "(+ 1 2 3 4)")
      (Term (iAInt 10))
  , testCase "product" $
    isRight
      (testEvalTerm "(* 1 2 3 4)")
      (Term (iAInt 24))
  , testCase "difference" $
    isRight
      (testEvalTerm "(- 1 2 3 4)")
      (Term (iAInt (-8)))
  ]

main :: IO ()
main = defaultMain tests

