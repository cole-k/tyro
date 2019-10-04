module Typing where

import Utils
import Data.List (elemIndex)
import Control.Applicative (liftA2)
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
  pure $ dropFromCtx marker ctx'
-- Forall right
subsumes ctx t1 (Forall var body) = do
  let tv = CtxTVar var
  ctx' <- subsumes (ctx <> [tv]) t1 body
  pure $ dropFromCtx tv ctx
-- InstantiateL
subsumes ctx (EVar a) t2 = do
  when (a `elem` freeEVars t2) . throwError $ "EVar " <> a <> " is free in type " <> show t2 <> "."
  instantiateL ctx a t2
-- InstantiateR
subsumes ctx t1 (EVar a) = do
  when (a `elem` freeEVars t1) . throwError $ "EVar " <> a <> " is free in type " <> show t1 <> "."
  instantiateR ctx t1 a
-- Fallthrough case (failure)
subsumes ctx t1 t2 = throwError $ "Type " <> show t1 <> "does not subsume type " <> show t2 <> "."

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
  pure $ dropFromCtx tv ctx
-- InstLSolve
instantiateL ctx a tp = do
  typeWFM tp (dropFromCtx (CtxEVar a) ctx)
  assignCtxEVar a tp ctx

instantiateR :: Context -> Type -> Varname -> InferM Context
-- InstLReach
instantiateR ctx (EVar b) a = instantiateReach ctx b a
-- InstRArr
instantiateR ctx (Arr t1 t2) a = do
  a1 <- freshEVar
  a2 <- freshEVar
  -- the new context is ctx[a1, a2, a = a1 -> a2]
  let arr      = Arr (EVar a1) (EVar a2)
      newElems = [CtxEVar a1, CtxEVar a2]
  newCtx   <- assignCtxEVar a arr =<< insertBefore (CtxEVar a) newElems ctx
  newCtx'  <- instantiateL newCtx a1 t1
  instantiateR newCtx t2 a2
-- InstRAllL
instantiateR ctx (Forall var body) a = do
  ev <- freshEVar
  let body'  = subTVar var (EVar ev) body
      marker = CtxMarker ev
  ctx' <- instantiateR (ctx <> [marker, CtxEVar ev]) body' a
  -- remove everything after 'marker' from the context
  pure $ dropFromCtx marker ctx'
instantiateR ctx tp a = do
  typeWFM tp (dropFromCtx (CtxEVar a) ctx)
  assignCtxEVar a tp ctx

instantiateReach :: Context -> Varname -> Varname -> InferM Context
instantiateReach ctx ev1 ev2 = do
  -- The EVars in the right order
  (a,b) <- case liftA2 (<=) ev1Index ev2Index of
             -- At least one of the EVars is not in the context
             Nothing -> throwError $ "EVars " <> ev1 <> " and " <> ev2 <> " are not both in the context " <> show ctx <> "."
             -- Order based on where the EVars are
             Just b  -> pure $ if b then (ev1, ev2) else (ev2, ev1)
  -- Assign the later EVar to the earlier EVar
  assignCtxEVar b (EVar a) ctx
  where
    ev1Index = elemIndex (CtxEVar ev1) ctx
    ev2Index = elemIndex (CtxEVar ev2) ctx

check :: Context -> TermU -> Type -> InferM (Term, Context)
-- 1I
check ctx (Trm _ Unit) TUnit = pure (Trm TUnit Unit, ctx)
-- Forall I
check ctx e tp@(Forall var body) = do
  let tvar = CtxTVar var
  (Trm _body' e', ctx') <- check (ctx <> [tvar]) e body
  -- If we successfully check e against the TVar, we can assign e the Forall
  -- type. We then remove the TVar and everything after it from the context.
  pure $ (Trm tp e', dropFromCtx tvar ctx')
-- Arr I
check ctx (Trm _ (Lambda x body)) (Arr a b) = do
  let var = CtxVar x a
  (body', ctx') <- check (ctx <> [var]) body b
  -- Use the new type in the arrow. Remove everything after and including the
  -- variable assignment.
  pure $ (Trm (Arr a b) (Lambda x body'), dropFromCtx var ctx')
check ctx e b = do
  (e', ctx') <- infer ctx e
  let a = getType e'
  ctx'' <- subsumes ctx' (applyCtx ctx' a) (applyCtx ctx' b)
  pure (setType e' b, ctx'')

infer :: Context -> TermU -> InferM (Term, Context)
-- Var
infer ctx (Trm _ (Var v)) = case findWith matchVarType ctx of
  Just tp -> pure (Trm tp (Var v), ctx)
  Nothing -> throwError $ "No type associated with variable " <> v <> " in context " <> show ctx <> "."
  where
    matchVarType (CtxVar var tp)
      | v == var  = Just tp
    matchVarType _ = Nothing
-- Anno
infer ctx (Trm _ (Annot e tp)) = do
  typeWFM tp ctx
  check ctx e tp
-- 1I=>
infer ctx (Trm _ Unit) = pure (Trm TUnit Unit, ctx)
-- Arr I =>
infer ctx (Trm _ (Lambda x body)) = do
  a <- freshEVar
  b <- freshEVar
  let ev1 = CtxEVar a
      ev2 = CtxEVar b
      var = CtxVar x (EVar a)
      arr = (Arr (EVar a) (EVar b))
  (body', ctx')<- check (ctx <> [ev1, ev2, var]) body (EVar b)
  pure (Trm arr (Lambda x body'), dropFromCtx var ctx')
-- Arr E
infer ctx (Trm _ (App e1 e2)) = do
  (e1', ctx')  <- infer ctx e1
  let a = getType e1'
  (e2', c, ctx'') <- inferApp ctx' (applyCtx ctx' a) e2
  pure (Trm c (App e1' e2'), ctx'')

-- | The triple returned is the typed 'Term' resulting from the input 'TermU',
-- the overall 'Type' of the application, and the new 'Context'.
inferApp :: Context -> Type -> TermU -> InferM (Term, Type, Context)
inferApp ctx (Forall var body) e = do
  ev <- freshEVar
  inferApp (ctx <> [CtxEVar ev]) (subTVar var (EVar ev) body) e
inferApp ctx (EVar a) e = do
  a1 <- freshEVar
  a2 <- freshEVar
  let newElems = [CtxEVar a1, CtxEVar a2]
      arr      = (Arr (EVar a1) (EVar a2))
  newCtx <- assignCtxEVar a arr =<< insertBefore (CtxEVar a) newElems ctx
  (e', ctx') <- check newCtx e (EVar a1)
  pure (e', EVar a2, ctx')
