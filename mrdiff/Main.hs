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
import qualified Generics.MRSOP.Diff as Diff
import qualified Generics.MRSOP.Diff.Annotate as Annotate
import qualified Generics.MRSOP.Diff.Annotate.Translate as Translate
import qualified Generics.MRSOP.GDiff as GDiff
import Generics.MRSOP.Util

import qualified Data.GraphViz.Printing as GraphViz
import qualified Data.GraphViz.Types.Monadic as GraphViz
import qualified Generics.MRSOP.GraphViz as GraphViz
import qualified Generics.MRSOP.GraphViz.Deep as GraphViz
import qualified Generics.MRSOP.GraphViz.Diff as GraphViz

import qualified Options.Applicative
import qualified System.FilePath

import Examples.Lua (FamBlock)
import Language.Clojure.AST (FamExpr)
import qualified Language.Clojure.Parser
import qualified Language.Lua.Parser

import Criterion.Measurement (measure)
import Criterion.Types (Measured(measTime))
import Criterion (nf)


data Language :: * where
  Language :: 
    (HasDatatypeInfo ki fam codes,
    Eq1 ki,
    Show1 ki,
    IsNat ix,
    TestEquality ki) =>
    (FilePath -> IO (Fix ki codes ix)) -> Language

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
  = WithDuration
  | WithoutDuration
  deriving (Bounded, Enum)

allStats :: [Stats]
allStats = [minBound..maxBound]

allStatsStr :: [String]
allStatsStr = toStr <$> allStats

toStr :: Stats -> String
toStr WithDuration = "duration"
toStr WithoutDuration = "no-duration"

fromStr :: String -> Maybe Stats
fromStr "duration" = Just WithDuration 
fromStr "no-duration" = Just WithoutDuration
fromStr _ = Nothing

data DiffMode 
  = ES      -- the edit script:w
  | Dot  -- dot-graph of the stdiff patch
  | Stats Stats


data MergeMode
  = MergeConflicts -- dot graph of the merge conflict
  | MergeStats

data Cmd
  = AST Bool FilePath
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
      -- TODO parse stats
      Stats <$> option (statsParser) (long "stats" <> metavar "STATS" <> help ("one of " ++ List.intercalate "," allStatsStr))
    statsParser = do
      x <- str
      case (fromStr x) of
        Just x -> pure x
        Nothing -> Options.Applicative.empty

    astParser = AST <$> switch (long "ann") <*> argument "file"
    argument = strArgument . metavar


printLanguage :: Bool -> Language -> FilePath -> IO ()
printLanguage ann (Language parseFile) fp = do
  x  <- parseFile fp
  if ann 
    then
      Text.putStrLn .
        GraphViz.dotToText fp .
        GraphViz.visualizeFix . 
        AG.mapAnn (\(Const x) -> Const (getSum x)) . AG.synthesize AG.sizeAlgebra $
        x
    else Text.putStrLn .  GraphViz.dotToText fp .  GraphViz.visualizeFix $ x

diffLanguage :: Language -> DiffMode -> FilePath -> FilePath -> IO ()
diffLanguage (Language parseFile) mode fp1 fp2 = do
  source <- parseFile fp1
  target <- parseFile fp2
  let sourceSize = getSum . getConst .  AG.sizeGeneric $ source
  let targetSize = getSum . getConst .  AG.sizeGeneric $ target
  let gdiff = GDiff.diff' source target
  let gdiff' = nf (show . GDiff.diff' source) target
  let source' = Translate.countCopies $ Annotate.annSrc source gdiff
  let target' = Translate.countCopies $ Annotate.annDest target gdiff
  let stdiff = Translate.diffAlmu  source' target'
  let target' = Diff.applyAlmu stdiff source

  case mode of
    ES -> print gdiff
    Dot -> Text.putStrLn . GraphViz.dotToText "lol" . GraphViz.visualizeAlmu  $ stdiff
    Stats s -> do
      x <- case s of
            WithDuration -> fmap (measTime . fst) (measure gdiff' 1)
            WithoutDuration -> pure (1.0 / 0.0)
      case target' of
        Right target' ->
          when (not (eq1 target target')) (fail "targets weren't equal")
        Left x -> fail $ "generated dif didn't apply: " ++ x
      Prelude.putStrLn . List.intercalate "," $ 
        [ show $ sourceSize
        , show $ targetSize
        , show $ x
        , fp1
        , fp2
        ]

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
  let on_a'   = Diff.mergeAlmu oa ob
  let on_b'   = Diff.mergeAlmu ob oa
  case (,) <$> on_a' <*> on_b' of
    Nothing -> Prelude.putStrLn . List.intercalate "," $ [ a , o , b , "0" ]
    Just (on_a, on_b) -> 
      case Diff.applyAlmu on_a a' of
        Left x -> fail $ "on_a failed to apply: " ++ x
        Right res1 ->
          case Diff.applyAlmu on_b  b' of
            Left x -> fail $ "on_b failed to apply: " ++ x
            Right res2 ->
              if eq1 res1 res2
              then 
                Prelude.putStrLn . List.intercalate "," $ [ a , o , b , "1" ]
              else fail "MA != MB"


commandHandler :: Cmd -> IO ()
commandHandler x =
  case x of
    AST ann file -> 
      case getLanguage file of
        Just lang -> printLanguage ann lang file
        Nothing -> fail "Unsupported language"
    Diff opts left right -> do
      let lang = do
            guard $ System.FilePath.takeExtension  left == System.FilePath.takeExtension right
            lleft <- getLanguage left
            pure lleft
      case lang of
        Just lang -> diffLanguage lang opts left right
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
