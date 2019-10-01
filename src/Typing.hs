module Typing where

import Control.Monad (when)
import Control.Monad.Except (throwError)
import Lang

subsumes :: Context -> Type -> Type -> InferM Context
-- Var
subsumes ctx (TVar var1) (TVar var2)
  | var1 == var2 = do
      when (CtxTVar var1 `notElem` ctx) . throwError $ "variable " <> var1 <> " not in the input context " <> show ctx
      pure ctx
  | otherwise = throwError $ "TVar " <> var1 <> " and TVar " <> var2 <> " are unequal."
-- Unit
subsumes ctx TUnit TUnit = pure ctx
-- EVar
subsumes ctx (EVar var1) (EVar var2)
  | var1 == var2 = do
      when (CtxEVar var1 `notElem` ctx) . throwError $ "variable " <> var1 <> " not in the input context " <> show ctx
      pure ctx
  | otherwise = throwError $ "EVar " <> var1 <> " and EVar " <> var2 <> " are unequal."
-- Arrow
subsumes ctx (Arr a1 a2) (Arr b1 b2) = do
  ctx' <- subsumes ctx b1 a1
  subsumes ctx' (applyCtx ctx' a2) (applyCtx ctx' b2)
-- Forall left
subsumes ctx (Forall var body) t2 = do
  ev <- freshEVar
  let body'  = subTVar var (EVar ev) body
      marker = CtxMarker ev
  ctx' <- subsumes (ctx <> [marker, CtxEVar ev]) body' t2
  -- remove everything after 'marker' from the context
  pure $ dropFromCtx ctx' marker
