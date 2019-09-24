module Lang where
-- qualified exports...

-- Ideas/Notes
--
-- 1. Would it work to have a new type CompleteContext that is produced as a
-- result of applying functions that solve EVars? Then we could have a "proof"
-- that the typing terminates and perhaps that it is correct without using
-- LiquidHaskell.

import Utils
import qualified Control.Monad.Trans.State.Lazy as ST

type Varname = String

data TermF a
  = Var Varname
  | Unit
  | Lambda Varname (TermF a)
  | App (TermF a) (TermF a)
  | Annot (TermF a) Type

data Type
  = TVar Varname
  | EVar Varname
  | Forall Varname Type
  | Arr Type Type
  | TUnit
  deriving (Show, Eq)

data Trm tp = Trm tp (TermF (Trm tp))

type TermU = Trm ()
type Term = Trm Type

data CtxElem
  = CtxEVar Varname
  | CtxEVarAssignment Varname Type
  | CtxMarker Varname
  | CtxTVar Varname
  | CtxVar Varname Type
  deriving (Show, Eq)

type Context = [CtxElem]

data InferCtx
  = InferCtx
  { nextEVar :: Int }

type InferM = ST.State InferCtx

-- | Checks if the 'Varname' given is present in the context.
ctxVarElem :: Varname -> Context -> Bool
-- should the vars each have their own newtypes and this instead be a bunch of
-- separate functions? If we Skolemize I think this isn't a problem...
ctxVarElem v (CtxTVar tv:_)
  | v == tv = True
ctxVarElem v (CtxVar var _:_)
  | v == var = True
ctxVarElem v (CtxEVar ev:_)
  | v == ev = True
ctxVarElem v (CtxEVarAssignment ev _:_)
  | v == ev = True
ctxVarElem v (_:ctx) = ctxVarElem v ctx

-- Is this ugly (as in, should this helper function not exist, should the type
-- be changed overall? I want the State for Skolemization...)
ctxVarElemM :: Varname -> Context -> InferM Bool
ctxVarElemM v c = pure $ ctxVarElem v c

-- | Checks if a type is well-formed, i.e. its EVars occur in the context, they
-- aren't out of order, etc.
typeWF :: Type -> Context -> Bool
typeWF = undefined

typeWFM :: Type -> Context -> InferM Bool
typeWFM tp ctx = pure $ typeWF tp ctx

-- | Checks if a context is well-formed, i.e. no repeated elements, no
-- out-of-order elements, etc.
ctxWF :: Context -> Bool
ctxWF [] = True
ctxWF (CtxTVar tv:ctx) = not (tv `ctxVarElem` ctx) && ctxWF ctx
ctxWF (CtxVar v tp:ctx) = not (v `ctxVarElem` ctx) && typeWF tp ctx && ctxWF ctx
ctxWF (CtxEVar ev:ctx) = not (ev `ctxVarElem` ctx) && ctxWF ctx
ctxWF (CtxEVarAssignment ev tp:ctx) = not (ev `ctxVarElem` ctx) && typeWF tp ctx && ctxWF ctx
ctxWF (marker@(CtxMarker ev):ctx) = not (ev `ctxVarElem` ctx) && not (marker `elem` ctx) && ctxWF ctx

ctxWFM :: Context -> InferM Bool
ctxWFM = pure . ctxWF

-- | Generates a fresh EVar from the given 'Varname', ensuring that it doesn't
-- conflict with other EVars that may have its same name.
freshEVar' :: Varname -> InferM Varname
freshEVar' ev = do
  ind <- ST.gets nextEVar
  ST.modify $ \st -> st{nextEVar = nextEVar st + 1}
  -- it should be invalid to name variables with numbers after them... if not,
  -- we can add some special character.
  pure $ ev <> show ind

-- | Generates a fresh EVar, named 'ev#', where '#' is a counter kept in the
-- state used to distinguish EVars.
freshEVar :: InferM Varname
freshEVar = freshEVar' "ev"

-- | Applies a 'Context' to a given 'Type', substituting any solved EVars for
-- their 'Type's.
applyCtx :: Context -> Type -> Type
applyCtx ctx tp = case tp of
  TVar tv       -> tp
  TUnit         -> tp
  EVar ev       -> case findWith (getType ev) ctx of
                     Just evTp -> evTp
                     Nothing   -> tp
  Arr tp1 tp2   -> Arr (applyCtx ctx tp1) (applyCtx ctx tp2)
  Forall v body -> Forall v (applyCtx ctx body)
  where
    getType v (CtxEVarAssignment ev tp)
      | v == ev = Just tp
    getType _ _ = Nothing
