{-# LANGUAGE LambdaCase #-}
module Eval where

import Lang
import Typing

import Debug.Trace
import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.Except(Except(..))
import qualified Control.Monad.Except as E

type EvalM = Except String

-- type Scope = Map Varname Term
--
-- builtins :: Scope
-- builtins = M.empty
--
-- eval :: Term -> EvalM Term
-- eval = eval' builtins
--
-- resolveVar :: Scope -> Varname -> EvalM Term
-- resolveVar sc v
--   | Just tm <- M.lookup v sc = pure tm
--   | otherwise = E.throwError $ "Unbound variable " <> v <> "."

-- | Evaluate a 'Term' by beta reduction.
eval :: Term -> EvalM Term
eval tm@(Trm _ e) = case e of
  Var v       -> pure tm
  Unit        -> pure tm
  Lambda _ _  -> pure tm
  Annot tm' _ -> pure tm'
  App tm1 tm2 -> eval tm1 >>= \case
                   Trm _ (Lambda x body) -> do
                     -- call by value (evaluate the term first)
                     tm2' <- eval tm2
                     eval $ subTmVar x tm2' body
                   Trm _ tm              -> E.throwError $ "Expected function, got " <> show tm <> "."

parseEval :: String -> Either String Term
parseEval str = do
  (tm, ctx) <- parseInfer str
  E.runExcept $ eval tm
