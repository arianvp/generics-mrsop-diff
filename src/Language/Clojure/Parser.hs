{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

module Language.Clojure.Parser
    ( parseTop
    , parse
    , parseFile
    , parseTest
    , parseAsOldExprList

    -- AST
    , OldExpr(..)
    , FormTy(..)
    , CollTy(..)
    , Term(..)
    , Tag(..)
    , SepOldExprList(..)
    , Sep(..)
    ) where

import Text.Parsec hiding (Empty)
import Text.Parsec.Token hiding (braces, parens, brackets, identifier, operator)
import Text.Parsec.Language
import Data.Char hiding (Space)
import qualified Data.Text as T
import Data.Proxy

import Language.Clojure.AST

lexer = makeTokenParser javaStyle
  { identStart = alphaNum <|> oneOf "_':*-&."
  , identLetter = alphaNum <|> oneOf ":_.'-/^?!><*#\"\\" <|> satisfy isSymbol
  }

parseSeq :: Parsec String () OldExpr
parseSeq = do
  p1 <- parseOldExpr
  whiteSpace lexer
  p2 <- (try parseSeq <|> parseEmptyProgram)
  return $ Seq p1 p2 

parseTop = whiteSpace lexer *> (try parseSeq <|> parseEmptyProgram) <* eof

parseAsOldExprList = do
  top <- parseTop
  return $ walkSeq top
  -- whiteSpace lexer *> (many parseSingleOldExpr) <* whiteSpace lexer <* eof
walkSeq (Seq a (Empty )) = a : []
walkSeq (Seq a b ) = a : walkSeq b
walkSeq (Empty ) = [Empty ]
walkSeq e = error $ "nowalk" ++ show e

parseOldExpr = choice
  [ try parseSpecial
  , try parseDispatch
  , parseCollection
  , parseComment
  , parseTerm
  ]

parseEmptyProgram = do
  return $ Empty 

parseTerm = do
    term <- parseTaggedString
    return $ Term term 

parseCollection = choice [ parseParens, parseVec, parseSet ]

parseSpecial = do
  ident <- parseSpecialIdent
  expr <- parseOldExpr
  return $ Special ident expr 

parseSpecialIdent = choice
  [ Quote <$ char '\''
  , SQuote <$ char '`'
  , UnQuote <$ char '~'
  , DeRef <$ char '@'
  , Meta <$ char '^'
  ]

parseTaggedString = choice [parseString, parseVar]

parseDispatch = do
  char '#'
  disp <- parseDispatchable
  return $ Dispatch disp
  where
    parseDispatchable = choice
      [ parseOldExpr
      , parseRegExp
      , parseTaggedLit
      ]
    --- ref: https://yobriefca.se/blog/2014/05/19/the-weird-and-wonderful-characters-of-clojure/
    -- parseParens covers the function marco
    -- parseTaggedLit covers the var macro (as identifiers can start with a quote ('))
    parseRegExp = do
      regExp <- parseString
      return $ Term regExp 

    parseTaggedLit = do
      tLit <- parseVar
      return $ Term tLit

    -- parseMeta = do
    --   start <- getPosition
    --   meta <- parseMetadata
    --   end <- getPosition
    --   return $ Term meta (mkRange start end)

parseComment = do
  char ';'
  comment <- manyTill anyChar (newline <|> eofS)
  -- single line comment, if we parse end here we have parsed newline as well
  return $ Comment (T.pack comment) 

eofS = do
  eof
  return '\n'

parens p = between (symbol lexer "(") (string ")") p
braces p = between (symbol lexer "{") (string "}") p
brackets p = between (symbol lexer "[") (string "]") p


parseSet = do
  contents <- braces parseSepOldExprList
  end <- getPosition
  return $ Collection Set contents 

parseVec = do
  contents <- brackets parseSepOldExprList
  return $ Collection Vec contents 

parseParens = do
  contents <- parens parseSepOldExprList
  return $ Collection Parens contents 

parseSepOldExprList = parseSepOldExprList1 <|> parseEmptyList

parseEmptyList = do
  return $ Nil 

parseSepOldExprList1 = do
  x <- parseOldExpr
  sep <- parseSep
  xs <- parseSepOldExprList
  return $ Cons x sep xs 

parseSep = choice
  [ Comma <$ lexeme lexer (char ',')
  , NewLine <$ lexeme lexer (many1 endOfLine)
  , Space <$ lexeme lexer (many1 (space <|> tab))
  , EmptySep <$ (lookAhead (anyChar) <|> eofS)
  ]
parseString = do
  qstring <- quotedString
  return $ TaggedString String (T.pack qstring) 
  where
    quotedString :: Parsec String () String
    quotedString = do
      char '"'
      x <- many (try (try (string "\\\\") <|> string "\\\"") <|> fmap pure (noneOf "\""))
      char '"'
      return $ concat x

parseVar = do
  vstring <- (identifier)
  return $ TaggedString Var (T.pack vstring) 

identifier = do
  c <- alphaNum <|> oneOf ":!#$%&*+./<=>?@\\^|-~_',"
  cs <- many (alphaNum <|> oneOf ":!?#$%&*+-/.<=>'?@^|~_'^\"\\" <|> satisfy isSymbol)
  return (c:cs)


parseFile :: FilePath -> IO (Either ParseError Expr)
parseFile f = fmap cannonTopLevel <$> parseFileOld f

parseFileOld :: FilePath -> IO (Either ParseError OldExpr)
parseFileOld fname = do 
  input <- readFile fname
  return (runParser parseTop () fname input)
