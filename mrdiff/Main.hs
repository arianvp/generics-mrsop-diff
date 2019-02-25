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
import Control.Monad (guard, when)
import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.Functor.Const (Const(..))

import Data.Semigroup ((<>))
import Data.Text (Text)
import Data.Monoid (Sum(..))
import Data.Coerce
import qualified Data.List as List

import Data.Text.Lazy as Text
import Data.Text.Lazy.IO as Text
import Data.Type.Equality
import Options.Applicative 

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


data Language :: * where
  Language :: 
    (HasDatatypeInfo ki fam codes,
    Eq1 ki,
    Show1 ki,
    IsNat ix,
    TestEquality ki) =>
    (FilePath -> IO (Fix ki codes ix)) -> Language

{-data Language = Lua | Clj
  deriving (Eq)-}

parseLua x = do
  x <- Language.Lua.Parser.parseFile x
  case x of
    Left y -> fail (show y)
    Right x -> return x

parseClj x = do
  x <- Language.Clojure.Parser.parseFile x
  case x of
    Left y -> fail (show y)
    Right x -> return x

-- different kinds of stats that can be collected
data Stats
  = SourceSize
  | TargetSize
  | GDiffSize
  | STDiffSize  
  | Duration
  deriving (Bounded, Enum)

allStats :: [Stats]
allStats = [minBound..maxBound]

allStatsStr :: [String]
allStatsStr = toStr <$> allStats

toStr :: Stats -> String
toStr SourceSize = "source-size"
toStr TargetSize = "target-size"
toStr GDiffSize = "gdiff-size"
toStr STDiffSize = "stdiff-size"
toStr Duration = "duration"

data DiffMode 
  = ES      -- the edit script:w
  | Dot  -- dot-graph of the stdiff patch
  | Stats [Stats] -- CSV-formatted statistics


data MergeMode
  = MergeConflicts -- dot graph of the merge conflict
  | MergeStats

data Cmd
  = AST FilePath
  | Diff DiffMode FilePath FilePath
  | Merge FilePath
          FilePath
          FilePath



getLanguage :: FilePath -> Maybe Language
getLanguage fp = 
  case System.FilePath.takeExtension fp of
    ".lua" -> Just (Language  (\fp -> deep @FamBlock <$> parseLua fp))
    ".clj" -> Just (Language (\fp -> deep @FamExpr <$> parseClj fp))
    _ -> Nothing

parserInfoCmd :: ParserInfo Cmd
parserInfoCmd =
  Options.Applicative.info
    (Options.Applicative.helper <*> parseCmd)
    (Options.Applicative.progDesc "Tree-based diff and merge tool" <>
     Options.Applicative.fullDesc)


parseCmd :: Parser Cmd
parseCmd =
  subcommand "diff" "Diff two files and return 0 if it succeeded" diffParser <|>
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
    diffParser  =
      Diff  <$> diffModeParser
            <*> argument "left" 
            <*> argument "right" 
    diffModeParser =
      flag ES ES  (long "es" <> help "print the gdiff editscript") <|>
      flag' Dot (long "dot" <> help "print dotgraph of stdiff") <|>
      Stats <$> option  undefined (long "stats" <> metavar "STATS" <> help ("some of " ++ List.intercalate "," allStatsStr))
    astParser = AST <$> argument "file"
    argument = Options.Applicative.strArgument . Options.Applicative.metavar


printLanguage :: Language -> FilePath -> IO ()
printLanguage (Language parseFile) fp = do
  x  <- parseFile fp
  Text.putStrLn .
    GraphViz.dotToText fp .
    GraphViz.visualizeFix . 
    AG.mapAnn (\(Const x) -> Const (getSum x)) . AG.synthesize AG.sizeAlgebra $
    x

diffLanguage :: Language -> DiffMode -> FilePath -> FilePath -> IO ()
diffLanguage (Language parseFile) mode fp1 fp2 = do
  source <- parseFile fp1
  target <- parseFile fp2
  let sourceSize = getSum . getConst .  AG.sizeGeneric $ left
  let targetSize = getSum . getConst .  AG.sizeGeneric $ right
  let gdiff = GDiff.diff' source target
  let source' = Translate.countCopies $ Annotate.annSrc source gdiff
  let target' = Translate.countCopies $ Annotate.annDest target gdiff
  let stdiff = Translate.diffAlmu  source' target'
  let target' = Diff.applyAlmu stdiff source

  case mode of
    ES -> print gdiff
    Dot -> error "TODO but involves stdiff, should fix"
    Stats stats -> do
      -- TODO start measure time
      putStrLn $ intercalate "," results

      -- TODO end measure time



  {-case Diff.applyAlmu s left of
    Right x ->
      if eq1 x right
        then print "it applied"
        else fail "generated diff was inconsistent"
    Left x -> fail $ "generated diff  didn't apply : " ++ x
  -}

mergeLanguage :: Language -> FilePath -> FilePath -> FilePath -> IO ()
mergeLanguage (Language parseFile) a o b = do
  a' <- parseFile a
  o' <- parseFile o
  b' <- parseFile b
  let es_oa   = GDiff.diff' o' a'
  let es_ob   = GDiff.diff' o' b'
  let es_oa_o = Translate.countCopies $ Annotate.annSrc  o' es_oa
  let es_oa_a = Translate.countCopies $ Annotate.annDest a' es_oa
  let es_ob_o = Translate.countCopies $ Annotate.annSrc  o' es_ob
  let es_ob_b = Translate.countCopies $ Annotate.annDest b' es_ob
  let oa      = Translate.diffAlmu es_oa_o es_oa_a
  let ob      = Translate.diffAlmu es_ob_o es_ob_b
  let m'      = Merge.mergeAlmu oa ob

  case m' of
    Left err -> fail $ "Failed to generate merge patch: " ++ (show err)
    Right m -> 
      case Diff.applyAlmu m a' of
        Left ma -> fail $ "MA failed to apply : " ++  ma
        Right res1 ->
          case Diff.applyAlmu m  b' of
            Left mb -> fail $ "MB failed to apply : " ++ mb
            Right res2 ->
              if eq1 res1 res2
              then pure ()
              else fail "MA != MB"


commandHandler :: Cmd -> IO ()
commandHandler x =
  case x of
    AST file -> 
      case getLanguage file of
        Just lang -> printLanguage lang file
        Nothing -> fail "Unsupported language"
    Diff opts left right -> do
      let lang = do
            guard $ System.FilePath.takeExtension  left == System.FilePath.takeExtension right
            lleft <- getLanguage left
            pure lleft
      case lang of
        Just lang -> diffLanguage lang left right
        Nothing -> fail "not same extenstion"
    Merge left origin right -> do
      let lang = do
            guard $ System.FilePath.takeExtension left == System.FilePath.takeExtension right
                 && System.FilePath.takeExtension left == System.FilePath.takeExtension origin
            lleft <- getLanguage left
            pure lleft
      case lang of
        Just lang -> mergeLanguage lang left origin right
        Nothing -> fail "not same extenstion"

main :: IO ()
main = commandHandler =<< Options.Applicative.execParser parserInfoCmd
