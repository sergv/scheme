{
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeSynonymInstances  #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-unused-binds       #-}
{-# OPTIONS_GHC -fno-warn-unused-matches     #-}

module SexpFrontend.Lexer
  ( Alex(..)
  , runAlex
  , alexMonadScan
  , alexLexPos
  , alexGetInput
  , module SexpFrontend.LexTok
  )
where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Error
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import Text.Read (readMaybe)

import SexpFrontend.LexTok
import Utils

}

%wrapper "monadUserState"

$ws     = [\ \n\f\r\t\v]
$nonnum = [ a-z A-Z \_ \- \+ \* \/ \! \? \< \> \= \_ \: \. ]
$num    = [0-9]

$sign     = [ \+ \- ]
@integer  = $sign? $num+

@fraction = \. $num+
@exponent = [\e\E] $sign? $num+
@real     = $sign? $num+ ( @fraction | @exponent | @fraction @exponent )

@symbol   = $nonnum ( $num | $nonnum )*

:-

<0> $ws+                ;
<0> ";".*               ;

<0> \"                  { begin string }
<string> [^\"]          { \input len -> do
                          recordStringChar $ T.head $ retrieveToken input len
                          alexMonadScan
                        }
<string> \\(. | \n)     { \input len -> do
                          let c = T.head $ T.tail $ retrieveToken input len
                          recordStringChar $ lexDecodeEscapedChar c
                          alexMonadScan
                        }
<string> \n             { \_ _ ->
                          recordError "newline in string constant"
                        }
<string> \"             { \_ _ -> do
                          getStrConst <* alexSetStartCode 0
                        }

<0> "("                 { \_ _ -> return OpenParen }
<0> "#("                { \_ _ -> return HashOpenParen }
<0> ")"                 { \_ _ -> return CloseParen }
<0> "'"                 { \_ _ -> return Quote }
<0> "."                 { \_ _ -> return Dot }
<0> @integer            { \input len -> do
                          x <- retrieveRead input len "cannot read integer"
                          return $ Number x
                        }
<0> @real               { \input len -> do
                          x <- retrieveRead input len "cannot read double"
                          return $ Real x
                        }
<0> "#t"                { \_ _ -> return $ Boolean True }
<0> "#f"                { \_ _ -> return $ Boolean False }
<0> "nil"               { \_ _ -> return $ TokNil }
<0> @symbol             { \input len ->
                          return $ Symbol $ retrieveToken input len
                        }

{

-- utility definitions

instance Functor Alex where
  fmap f x = Alex $ \s -> let res = unAlex x s
                          in fmap (second f) res

instance Applicative Alex where
  pure x = Alex $ \s -> Right (s, x)
  Alex f <*> Alex x = Alex $ \s -> do
                                   (s', f')  <- f s
                                   (s'', x') <- x s'
                                   return (s'', f' x')

instance MonadError String Alex where
  throwError msg = alexError msg

  catchError (Alex action) onErr =
    Alex $ \s -> case action s of
                   Left err       -> unAlex (onErr err) s
                   res@(Right _)  -> res

-- actual lexer

data AlexUserState = AlexUserState
                   { -- string characters in reverse order
                     stringChars  :: [Char]
                   }
                   deriving (Show, Eq, Ord)

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState { stringChars  = [] }


-- alexEOF :: Alex AlexUserState
-- alexEOF = do
--   startCode <- alexGetStartCode
--   if startCode == string
--   then recordError "EOF in string constant"
--   else alexGetUserState

alexEOF :: Alex LexTok
alexEOF = do
  startCode <- alexGetStartCode
  if startCode == string
  then recordError "EOF in string constant"
  else return EOF

retrieveRead :: (Read a) => AlexInput -> Int -> Text -> Alex a
retrieveRead input@((AlexPn _ line col), _, _, _) len msg =
  maybe (recordError errorMsg) return $ readMaybe $ T.unpack tok
  where
    errorMsg = show' line <> ":" <> show' col <> ":" <> "cannot read from " <> tok <> ": " <> msg
    tok      = retrieveToken input len

retrieveToken :: AlexInput -> Int -> Text
retrieveToken ((AlexPn _pos _line _col), _prevChar, _pendingBytes, str) len =
  T.pack $ take len str

alexInputString :: AlexInput -> String
alexInputString (_, _, _, str) = str

alexLexPos :: AlexInput -> LexPos
alexLexPos ((AlexPn _ line col), _, _, _) = LexPos line col

recordError :: Text -> Alex a
recordError msg = do
  LexPos line col <- liftM alexLexPos alexGetInput
  throwError $ "Alex: " ++ show line ++ ":" ++ show col ++ ": " ++ T.unpack msg

resetStrConst :: Alex ()
resetStrConst = do
  ust <- alexGetUserState
  alexSetUserState $ ust { stringChars = [] }

getStrConst :: Alex LexTok
getStrConst = do
  ust <- alexGetUserState
  resetStrConst
  return $ String $ T.pack $ reverse $ stringChars ust

recordStringChar :: Char -> Alex ()
recordStringChar c = do
  ust <- alexGetUserState
  alexSetUserState $ ust { stringChars = c: stringChars ust }

lexDecodeEscapedChar :: Char -> Char
lexDecodeEscapedChar = \c -> M.findWithDefault c c escapeChars
  where
    escapeChars :: Map Char Char
    escapeChars =  M.fromList [ ('n',  '\n')
                              , ('b',  '\b')
                              , ('f',  '\f')
                              , ('t',  '\t')
                              , ('\n', '\n')
                              ]

}
