module Lang where
-- qualified exports...

type Varname = String

data TermF a
  = Var Varname
  | Unit
  | Lambda Varname (TermF a)
  | App (TermF a) (TermF a)
  | Annot (TermF a) Type

data Type
  = TVar Varname
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

-- should the vars each have their own newtypes and this instead be a bunch of
-- separate functions?
ctxVarElem :: Varname -> Context -> Bool
ctxVarElem v (CtxTVar tv:_)
  | v == tv = True
ctxVarElem v (CtxVar var _:_)
  | v == var = True
ctxVarElem v (CtxEVar ev:_)
  | v == ev = True
ctxVarElem v (CtxEVarAssignment ev _:_)
  | v == ev = True
ctxVarElem v (_:ctx) = ctxVarElem v ctx

typeWF :: Context -> Type -> Bool
typeWF = undefined

ctxWF :: Context -> Bool
ctxWF [] = True
ctxWF (CtxTVar tv:ctx) = not (tv `ctxVarElem` ctx) && ctxWF ctx
ctxWF (CtxVar v tp:ctx) = not (v `ctxVarElem` ctx) && typeWF ctx tp && ctxWF ctx
ctxWF (CtxEVar ev:ctx) = not (ev `ctxVarElem` ctx) && ctxWF ctx
ctxWF (CtxEVarAssignment ev tp:ctx) = not (ev `ctxVarElem` ctx) && typeWF ctx tp && ctxWF ctx
ctxWF (marker@(CtxMarker ev):ctx) = not (ev `ctxVarElem` ctx) && not (marker `elem` ctx) && ctxWF ctx
