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

{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Main where

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
tests = testGroup "Tests" [parserTests]

testParseTerm :: Text -> SchemeSexp
testParseTerm source = either error id $ parseTerm "test" $ T.unpack source

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
    Term (iVector [Term $ iAInt 1])
  , testCase "Parse sample vector" $
    testParseTerm "#(1 2 #t)" @?=
    Term
      (iVector
         [ Term $ iAInt 1
         , Term $ iAInt 2
         , Term $ iABool True
         ])
  ]

main :: IO ()
main = defaultMain tests

