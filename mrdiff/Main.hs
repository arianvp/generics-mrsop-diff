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
import qualified Generics.MRSOP.Diff2 as Diff
import qualified Generics.MRSOP.Diff.Annotate as Annotate
import qualified Generics.MRSOP.Diff.Merge as Merge
import qualified Generics.MRSOP.Diff.Annotate.Translate as Translate
import qualified Generics.MRSOP.GDiff as GDiff
import qualified Generics.MRSOP.GDiffCopyExperiment as GDiffOld
import Generics.MRSOP.Util

import qualified Data.GraphViz.Printing as GraphViz
import qualified Data.GraphViz.Types.Monadic as GraphViz
import qualified Generics.MRSOP.GraphViz as GraphViz
import qualified Generics.MRSOP.GraphViz.Deep as GraphViz
import qualified Generics.MRSOP.GraphViz.Diff2 as GraphViz

import qualified Options.Applicative
import qualified System.FilePath

import Examples.Lua (FamBlock)
import Language.Clojure.AST (FamExpr)
import qualified Language.Clojure.Parser
import qualified Language.Lua.Parser

data Language = Lua | Clj
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
    ".clj" -> Just Clj
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
      Merge <$> argument "left" <*> argument "origin" <*> argument "right"
    diffParser v = Diff v <$> argument "left" <*> argument "right"
    astParser = AST <$> argument "file"
    argument = Options.Applicative.strArgument . Options.Applicative.metavar

printCLJAST :: FilePath -> IO ()
printCLJAST fp = do
  x <- Language.Clojure.Parser.parseFile fp
  case x of
    Left er -> fail (show er)
    Right block ->
      Text.putStrLn .
      GraphViz.dotToText fp .
      GraphViz.visualizeFix . 
      AG.mapAnn (\(Const x) -> Const (getSum x)) . AG.synthesize AG.sizeAlgebra .
      deep @FamExpr $
      block
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

diffClj :: V -> FilePath -> FilePath -> IO ()
diffClj v fp1 fp2 = do
  x <-
    getCompose $ do
      x <- Compose . Language.Lua.Parser.parseFile $ fp1
      y <- Compose . Language.Lua.Parser.parseFile $ fp2
      pure (deep @FamBlock x, deep @FamBlock y)
  case x of
    Left er -> fail (show er)
    Right (left, right) ->
      case v of
        N -> do
          let d = GDiff.diff' left right
          let l = Annotate.annSrc left d
          let r = Annotate.annDest right d
          let s = Translate.diffAlmu 
                    (Translate.countCopies l)
                    (Translate.countCopies r)
          case Diff.applyAlmu s left of
            Just x ->
              if eq1 x right
                then pure ()
                else fail "generated diff was inconsistent"
            Nothing -> fail "generated diff  didn't apply"
        O -> undefined
             
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
        N -> do
          let d = GDiff.diff' left right
          let l = Annotate.annSrc left d
          let r = Annotate.annDest right d
          let s = Translate.diffAlmu 
                    (Translate.countCopies l)
                    (Translate.countCopies r)
          case Diff.applyAlmu s left of
            Just x ->
              if eq1 x right
                then pure ()
                else fail "generated diff was inconsistent"
            Nothing -> fail "generated diff  didn't apply"
        O -> undefined
             

mergeClj :: FilePath -> FilePath -> FilePath -> IO ()
mergeClj a o b =  do
  x <-
    getCompose $ do
      x <- Compose . Language.Clojure.Parser.parseFile $ a
      y <- Compose . Language.Clojure.Parser.parseFile $ o
      z <- Compose . Language.Clojure.Parser.parseFile $ b
      pure (deep @FamExpr x, deep @FamExpr y, deep @FamExpr z)
  case x of
    Left err -> fail (show err)
    Right (a', o', b') -> do
      let es_oa   = GDiff.diff' o' a'
      let es_ob   = GDiff.diff' o' b'
      let es_oa_o = Translate.countCopies $ Annotate.annSrc  o' es_oa
      let es_oa_a = Translate.countCopies $ Annotate.annDest a' es_oa
      let es_ob_o = Translate.countCopies $ Annotate.annSrc  o' es_ob
      let es_ob_b = Translate.countCopies $ Annotate.annDest b' es_ob
      let oa      = Translate.diffAlmu es_oa_o es_oa_a
      let ob      = Translate.diffAlmu es_ob_o es_ob_b
      let m'       = Merge.mergeAlmu oa ob
      case m' of
        Left err -> fail $ "Failed to generate merge patch: " ++ (show err)
        Right m -> 
          case Diff.applyAlmu m a' of
            Nothing -> fail "MA failed to apply"
            Just res1 ->
              case Diff.applyAlmu m  b' of
                Nothing -> fail "MB failed to apply"
                Just res2 ->
                  if eq1 res1 res2
                  then pure ()
                  else fail "MA != MB"


          


      
      


mergeLua :: FilePath -> FilePath -> FilePath -> IO ()
mergeLua a o b =  do
  x <-
    getCompose $ do
      x <- Compose . Language.Lua.Parser.parseFile $ a
      y <- Compose . Language.Lua.Parser.parseFile $ o
      z <- Compose . Language.Lua.Parser.parseFile $ b
      pure (deep @FamBlock x, deep @FamBlock y, deep @FamBlock z)
  case x of
    Left err -> fail (show err)
    Right (a', o', b') -> do
      let es_oa   = GDiff.diff' o' a'
      let es_ob   = GDiff.diff' o' b'
      let es_oa_o = Translate.countCopies $ Annotate.annSrc  o' es_oa
      let es_oa_a = Translate.countCopies $ Annotate.annDest a' es_oa
      let es_ob_o = Translate.countCopies $ Annotate.annSrc  o' es_ob
      let es_ob_b = Translate.countCopies $ Annotate.annDest b' es_ob
      let oa      = Translate.diffAlmu es_oa_o es_oa_a
      let ob      = Translate.diffAlmu es_ob_o es_ob_b
      let m'       = Merge.mergeAlmu oa ob
      case m' of
        Left err -> fail $ "Failed to generate merge patch: " ++ (show err)
        Right m -> 
          case Diff.applyAlmu m a' of
            Nothing -> fail "MA failed to apply"
            Just res1 ->
              case Diff.applyAlmu m  b' of
                Nothing -> fail "MB failed to apply"
                Just res2 ->
                  if eq1 res1 res2
                  then pure ()
                  else fail "MA != MB"

command :: Cmd -> IO ()
command x =
  case x of
    AST file ->
      case getLanguage file of
        Just Lua -> printAST file
        Just Clj -> printCLJAST file
        Nothing -> fail "Not a supported language"
    Diff v left right -> do
      let lang = do
            lleft <- getLanguage left
            lright <- getLanguage right
            guard $ lleft == lright
            pure lleft
      case lang of
        Just Lua -> diffLua v left right
        Just Clj -> diffClj v left right
        Nothing -> fail "Languages differ or unsupported"
    Merge left origin right -> do
      let lang = do
            lleft <- getLanguage left
            lorigin <- getLanguage origin
            lright <- getLanguage right
            guard $ lleft == lright && lleft == lorigin
            pure lleft
      case lang of
        Just Lua -> mergeLua left origin right
        Just Clj -> mergeClj left origin right
        Nothing -> fail "Languages differ or unsupported"

main :: IO ()
main = command =<< Options.Applicative.execParser parserInfoCmd
