module Typing where

import Lang

subsumes :: Context -> Type -> Type -> InferM Context
-- Var
subsumes ctx var1 var2
  | var1 == var2 = undefined
-- Unit
subsumes ctx TUnit TUnit = pure ctx

{-# INLINE (<:) #-}
(<:) :: Context -> Type -> Type -> InferM Context
(<:) = subsumes
