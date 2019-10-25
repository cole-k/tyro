module Main where

import System.IO (isEOF)
import Control.Monad (when)

import Eval
import Pretty

-- matches 'str', with optional trailing whitespace
matches :: String -> String -> Bool
matches str input = lengthOK && frontOK && backOK
  where
    lengthOK = length input >= length str
    -- The front of 'input' matches 'str'
    frontOK  = and $ zipWith (==) input str
    -- The back of 'input' is all whitespace
    backOK   = all (`elem` [' ', '\t']) $ drop (length str) input

main :: IO ()
main = putStrLn "--- tyro REPL ---" *> main'

main' :: IO ()
main' = do
  done <- isEOF
  input <- getLine
  when (not $ matches ":quit" input ||
              matches ":q" input ||
              done
       ) $ do
            case parseEval input of
              Left err -> putStrLn err
              Right term -> putStrLn $ prettyTerm term
            main'
