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
-- Forall right
subsumes ctx t1 (Forall var body) = do
  let tv = CtxTVar var
  ctx' <- subsumes (ctx <> [tv]) t1 body
  pure $ dropFromCtx ctx tv
-- InstantiateL
subsumes ctx (EVar a) t2 = do
  when (a `elem` freeEVars t2) . throwError $ "EVar " <> a <> " is free in type " <> show t2 <> "."
  instantiateL ctx a t2
-- InstantiateR
subsumes ctx t1 (EVar a) = do
  when (a `elem` freeEVars t1) . throwError $ "EVar " <> a <> " is free in type " <> show t1 <> "."
  instantiateR ctx t1 a

instantiateL :: Context -> Varname -> Type -> InferM Context
-- InstLReach
instantiateL ctx a (EVar b) = instantiateReach ctx a b
-- InstLArr
instantiateL ctx a (Arr t1 t2) = do
  a1 <- freshEVar
  a2 <- freshEVar
  -- the new context is ctx[a1, a2, a = a1 -> a2]
  let arr      = Arr (EVar a1) (EVar a2)
      newElems = [CtxEVar a1, CtxEVar a2]
  newCtx   <- assignCtxEVar a arr =<< insertBefore (CtxEVar a) newElems ctx
  newCtx'  <- instantiateR newCtx t1 a1
  instantiateL newCtx a2 t2
-- InstLAllR
instantiateL ctx a (Forall var body) = do
  let tv = CtxTVar var
  ctx' <- instantiateL (ctx <> [tv]) a body
  pure $ dropFromCtx ctx tv

instantiateR :: Context -> Type -> Varname -> InferM context
instantiateR = undefined

instantiateReach :: Context -> Varname -> Varname -> InferM Context
instantiateReach = undefined
