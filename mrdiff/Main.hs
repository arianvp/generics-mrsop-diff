{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.Functor.Const (Const(..))

import Data.Semigroup ((<>))
import Data.Text (Text)
import Data.Monoid (Sum(..))

import Data.Text.Lazy as Text
import Data.Text.Lazy.IO as Text
import Data.Type.Equality
import Options.Applicative (Parser, ParserInfo)

import qualified Generics.MRSOP.AG as AG
import Generics.MRSOP.Base
import qualified Generics.MRSOP.Diff.Annotate as Annotate
import qualified Generics.MRSOP.Diff.Annotate.Translate as Translate
import qualified Generics.MRSOP.GDiff as GDiff
import qualified Generics.MRSOP.GDiffOld as GDiffOld
import Generics.MRSOP.Util

import qualified Data.GraphViz.Printing as GraphViz
import qualified Data.GraphViz.Types.Monadic as GraphViz
import qualified Generics.MRSOP.GraphViz as GraphViz
import qualified Generics.MRSOP.GraphViz.Deep as GraphViz
import qualified Generics.MRSOP.GraphViz.Diff2 as GraphViz

import qualified Options.Applicative
import qualified System.FilePath

import Examples.Lua (FamBlock)
import qualified Language.Lua.Parser

data Language =
  Lua
  deriving (Eq)

data Cmd
  = AST FilePath
  | Diff V FilePath
         FilePath
  | Merge FilePath
          FilePath
          FilePath

getLanguage :: FilePath -> Maybe Language
getLanguage fp =
  case System.FilePath.takeExtension fp of
    ".lua" -> Just Lua
    _ -> Nothing

parserInfoCmd :: ParserInfo Cmd
parserInfoCmd =
  Options.Applicative.info
    (Options.Applicative.helper <*> parseCmd)
    (Options.Applicative.progDesc "Tree-based diff and merge tool" <>
     Options.Applicative.fullDesc)

data V = O | N

parseCmd :: Parser Cmd
parseCmd =
  subcommand "diff" "Diff two files" (diffParser N) <|>
  subcommand "olddiff" "Diff two files" (diffParser O) <|>
  subcommand "ast" "show ast of file" astParser <|>
  subcommand "merge" "Merge two files, given their common ancestor" mergeParser
  where
    subcommand name description cmdParser =
      Options.Applicative.subparser
        (Options.Applicative.command name parserInfo <>
         Options.Applicative.metavar name)
      where
        parserInfo =
          Options.Applicative.info
            parser
            (Options.Applicative.fullDesc <>
             Options.Applicative.progDesc description)
        parser = Options.Applicative.helper <*> cmdParser
    mergeParser =
      Merge <$> argument "origin" <*> argument "left" <*> argument "right"
    diffParser v = Diff v <$> argument "left" <*> argument "right"
    astParser = AST <$> argument "file"
    argument = Options.Applicative.strArgument . Options.Applicative.metavar

printAST :: FilePath -> IO ()
printAST fp = do
  x <- Language.Lua.Parser.parseFile fp
  case x of
    Left er -> fail (show er)
    Right block ->
      Text.putStrLn .
      GraphViz.dotToText fp .
      GraphViz.visualizeFix . 
      AG.mapAnn (\(Const x) -> Const (getSum x)) . AG.synthesize AG.sizeAlgebra .
      deep @FamBlock $
      block

diffLua :: V -> FilePath -> FilePath -> IO ()
diffLua v fp1 fp2 = do
  x <-
    getCompose $ do
      x <- Compose . Language.Lua.Parser.parseFile $ fp1
      y <- Compose . Language.Lua.Parser.parseFile $ fp2
      pure (deep @FamBlock x, deep @FamBlock y)
  case x of
    Left er -> fail (show er)
    Right (left, right) ->
      case v of
        N -> print (GDiff.diff' left right)
        O -> print (GDiffOld.diff' left right)
             

command :: Cmd -> IO ()
command x =
  case x of
    AST file ->
      case getLanguage file of
        Just Lua -> printAST file
        Nothing -> fail "Not a supported language"
    Diff v left right -> do
      let lang = do
            lleft <- getLanguage left
            lright <- getLanguage right
            guard $ lleft == lright
            pure lleft
      case lang of
        Just Lua -> diffLua v left right
        Nothing -> fail "Languages differ or unsupported"
    Merge origin left right -> do
      let lang = do
            lorigin <- getLanguage origin
            lleft <- getLanguage left
            lright <- getLanguage right
            guard $ lleft == lright && lleft == lorigin
            pure lleft
      case lang of
        Just Lua -> undefined
        Nothing -> fail "Languages differ or unsupported"

main :: IO ()
main = command =<< Options.Applicative.execParser parserInfoCmd
