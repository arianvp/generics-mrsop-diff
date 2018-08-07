module Main where

import Control.Applicative ((<|>))
import Data.Semigroup ((<>))
import Options.Applicative (Parser, ParserInfo)

import qualified Options.Applicative

data Cmd
  = Diff FilePath
         FilePath
  | Merge FilePath
          FilePath
          FilePath


parserInfoCmd :: ParserInfo Cmd
parserInfoCmd =
    Options.Applicative.info
        (Options.Applicative.helper <*> parseCmd)
        (   Options.Applicative.progDesc "Tree-based diff and merge tool"
        <>  Options.Applicative.fullDesc
        )

parseCmd :: Parser Cmd
parseCmd =
  subcommand "diff" "Diff two files" diffParser <|>
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
    diffParser = Diff <$> argument "left" <*> argument "right"
    argument = Options.Applicative.strArgument . Options.Applicative.metavar

command :: Cmd -> IO ()
command x = putStrLn "no"

main :: IO ()
main =
  command =<<  Options.Applicative.execParser parserInfoCmd
