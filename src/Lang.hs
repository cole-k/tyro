{-# LANGUAGE DeriveFunctor #-}
module Lang where
-- qualified exports...

-- Ideas/Notes
--
-- 1. Would it work to have a new type CompleteContext that is produced as a
-- result of applying functions that solve EVars? Then we could have a "proof"
-- that the typing terminates and perhaps that it is correct without using
-- LiquidHaskell.

import Utils

import Data.Foldable (find)
import Data.Maybe (isJust)
import Data.Map (Map)
import qualified Data.Map as M
import Control.Applicative ((<|>))
import Control.Monad (when)
import qualified Control.Monad.State.Lazy as ST
import qualified Control.Monad.Except as E

type Varname     = String
type Label       = String
type TailVarname = String

data Row e
  = Row
    { rowMap  :: Map Label e
    , rowTail :: Maybe TailVarname
    }
  deriving (Show, Eq, Functor)

data TermF e
  = Var Varname
  | Unit
  | Lambda Varname e
  | App e e
  | Annot e Type
  | Rcd (Row e)
  | Prj e Label
  deriving (Show, Functor)

data Type
  = TVar Varname
  | EVar Varname
  | Forall Varname Type
  | Arr Type Type
  | TUnit
  | TRcd (Row Type)
  deriving (Show, Eq)

-- | Terms are annotated with their types
data Trm tp = Trm tp (TermF (Trm tp))
  deriving (Show, Functor)

-- | Untyped terms
type TermU = Trm ()
-- | Typed terms
type Term = Trm Type

data CtxElem
  = CtxEVar Varname
  | CtxTailVar TailVarname
  | CtxEVarAssignment Varname Type
  | CtxTailVarAssignment TailVarname (Row Type)
  | CtxMarker Varname
  | CtxTVar Varname
  | CtxVar Varname Type
  deriving (Show, Eq)

type Context = [CtxElem]

data InferCtx
  = InferCtx
  { nextEVar :: Int }

type InferM = E.ExceptT String (ST.State InferCtx)

initialCtx :: InferCtx
initialCtx = InferCtx { nextEVar = 0 }

updateRow :: Row a -> Row a -> Row a
updateRow Row{rowMap=rm1, rowTail=rt1} Row{rowMap=rm2, rowTail=rt2} =
  -- precedence goes to the items in the first row
  Row{rowMap=rm1 <> rm2, rowTail =rt1 <|> rt2}

-- | Gets the 'Type' of a typed 'Term'.
getType :: Term -> Type
getType (Trm tp _) = tp

-- | Sets the type annotation of a 'Term'.
setType :: Trm tp -> tp -> Trm tp
setType (Trm _ tm) tp = Trm tp tm

-- | Checks if the 'Varname' given is present in the context.
ctxVarElem :: Varname -> Context -> Bool
-- should the vars each have their own newtypes and this instead be a bunch of
-- separate functions? If we Skolemize I think this isn't a problem...
ctxVarElem _ [] = False
ctxVarElem v (CtxTVar tv:_)
  | v == tv = True
ctxVarElem v (CtxVar var _:_)
  | v == var = True
ctxVarElem v (CtxEVar ev:_)
  | v == ev = True
ctxVarElem v (CtxEVarAssignment ev _:_)
  | v == ev = True
ctxVarElem v (_:ctx) = ctxVarElem v ctx

-- | Checks if the 'TailVarname' given is present in the context.
ctxTailVarElem :: TailVarname -> Context -> Bool
ctxTailVarElem _ [] = False
ctxTailVarElem v (CtxTailVar tailV:_)
  | v == tailV = True
ctxTailVarElem v (_:ctx) = ctxVarElem v ctx

-- Is this ugly (as in, should this helper function not exist, should the type
-- be changed overall?)
ctxVarElemM :: Varname -> Context -> InferM Bool
ctxVarElemM v c = pure $ ctxVarElem v c

-- | Assigns an EVar with name 'Varname' to the 'Type' in the 'Context',
-- returning the new 'Context' (throwing an error if assignment is impossible).
assignCtxEVar :: Varname -> Type -> Context -> InferM Context
assignCtxEVar a tp [] = E.throwError $ "EVar " <> a <> " not present in the context."
assignCtxEVar a tp (CtxEVarAssignment ev _:_)
  | ev == a = E.throwError $ "EVar " <> a <> "already assignd in the context."
assignCtxEVar a tp (CtxEVar ev:ctx)
  | ev == a = pure $ CtxEVarAssignment ev tp : ctx
assignCtxEVar a tp (ctxElem:ctx) = (ctxElem:) <$> assignCtxEVar a tp ctx

-- | Assigns a TailVar with name 'TailVarName' to the 'Row' in the 'Context',
-- returning the new 'Context' (throwing an error if assignment is impossible).
assignCtxTailVar :: Varname -> Row Type -> Context -> InferM Context
assignCtxTailVar v _ [] = E.throwError $ "Row Tail " <> v <> " not present in the context."
assignCtxTailVar v _ (CtxTailVarAssignment tailV _:_)
  | tailV == v = E.throwError $ "Row Tail " <> v <> "already assignd in the context."
assignCtxTailVar v row (CtxTailVar tailV:ctx)
  | tailV == v = pure $ CtxTailVarAssignment v row : ctx
assignCtxTailVar v row (ctxElem:ctx) = (ctxElem:) <$> assignCtxTailVar v row ctx

-- | Attempts to insert the given '[CtxElem]' before the 'CtxElem', throwing an
-- error if the 'CtxElem' is not found.
insertBefore :: CtxElem -> [CtxElem] -> Context -> InferM Context
insertBefore e newEs [] = E.throwError $ "Element " <> show e <> " not present in context."
insertBefore e newEs ctx@(ctxElem:ctx')
  | ctxElem == e = pure $ newEs <> ctx
  | otherwise    = (ctxElem:) <$> insertBefore e newEs ctx'

-- | Removes the the context after and including the 'CtxElem' given.
dropFromCtx :: CtxElem -> Context -> Context
dropFromCtx e ctx = fst $ span (/= e) ctx

-- | Checks if a type is well-formed, i.e. its EVars occur in the context, they
-- aren't out of order, etc.
typeWF :: Type -> Context -> Bool
typeWF (EVar a) ctx = isJust $ find matchEVar ctx
  where
    matchEVar (CtxEVar ev) = a == ev
    matchEVar (CtxEVarAssignment ev _) = a == ev
    matchEVar _ = False
typeWF (TVar a) ctx = CtxTVar a `elem` ctx
typeWF TUnit _ = True
typeWF (Arr t1 t2) ctx = typeWF t1 ctx && typeWF t2 ctx
typeWF (Forall var body) ctx = typeWF body (ctx <> [CtxTVar var])
typeWF (TRcd Row{rowMap=rm, rowTail=rt}) ctx =
  let mapWF = and $ flip typeWF ctx <$> M.elems rm
  in case rt of
    Nothing      -> mapWF
    (Just tailV) -> mapWF && isJust (find (matchTailVar tailV) ctx)
  where
    matchTailVar tailV (CtxTailVar tailV') = tailV == tailV'
    matchTailVar tailV (CtxTailVarAssignment tailV' _) = tailV == tailV'
    matchTailVar _ _ = False

typeWFM :: Type -> Context -> InferM ()
typeWFM tp ctx = when (not $ typeWF tp ctx) $
  E.throwError $ "Type " <> show tp <> " not well-formed in context " <> show ctx <> "."

-- | Checks if a context is well-formed, i.e. no repeated elements, no
-- out-of-order elements, etc.
ctxWF :: Context -> Bool
ctxWF [] = True
ctxWF (CtxTVar tv:ctx) = not (tv `ctxVarElem` ctx) && ctxWF ctx
ctxWF (CtxVar v tp:ctx) = not (v `ctxVarElem` ctx) && typeWF tp ctx && ctxWF ctx
ctxWF (CtxEVar ev:ctx) = not (ev `ctxVarElem` ctx) && ctxWF ctx
ctxWF (CtxEVarAssignment ev tp:ctx) = not (ev `ctxVarElem` ctx) && typeWF tp ctx && ctxWF ctx
ctxWF (marker@(CtxMarker ev):ctx) = not (ev `ctxVarElem` ctx) && not (marker `elem` ctx) && ctxWF ctx
ctxWF (CtxTailVar tailV:ctx) = not (tailV `ctxTailVarElem` ctx) && ctxWF ctx
ctxWF (CtxTailVarAssignment tailV row:ctx) = not (tailV `ctxTailVarElem` ctx) && ctxWF ctx -- && typeWF (TRcd row) ctx

ctxWFM :: Context -> InferM ()
ctxWFM ctx = when (not $ ctxWF ctx) $
  E.throwError $ "Context " <> show ctx <> " not well-formed."

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
                     Just evTp -> applyCtx ctx evTp
                     Nothing   -> tp
  Arr tp1 tp2   -> Arr (applyCtx ctx tp1) (applyCtx ctx tp2)
  Forall v body -> Forall v (applyCtx ctx body)
  TRcd Row{rowMap=rm, rowTail=Just rt}
    | Just newRow <- findWith (getRowTail rt) ctx ->
      -- remove the tail from the first row so that it doesn't take precedence
      -- (maybe it would make sense to just make updateRow overwrite the tail of
      -- the first row...)
      TRcd (updateRow Row{rowMap=applyCtx ctx <$> rm, rowTail = Nothing} newRow)
  TRcd Row{rowMap=rm, rowTail=rt} ->
    TRcd Row{rowMap=applyCtx ctx <$> rm, rowTail=rt}
  where
    getType v (CtxEVarAssignment ev tp)
      | v == ev = Just tp
    getType _ _ = Nothing
    getRowTail rt (CtxTailVarAssignment tail row)
      | rt == tail = Just row
    getRowTail _ _ = Nothing

-- | Gets all of the unbound 'EVar's in a type.
freeEVars :: Type -> [Varname]
freeEVars TUnit = []
freeEVars (TVar _) = []
freeEVars (EVar ev) = [ev]
-- the foralls should be binding tvars
freeEVars (Forall _ body) = freeEVars body
freeEVars (Arr t1 t2) = freeEVars t1 ++ freeEVars t2
freeEVars (TRcd Row{rowMap=rm, rowTail=rt}) = foldMap freeEVars rm <> maybe [] pure rt

-- | Substitute a TVar for a 'Type' in the given 'Type'.
subTVar :: Varname -> Type -> Type -> Type
subTVar var subType tp@(TVar v)
  | var == v  = subType
  | otherwise = tp
subTVar var subType tp@(Forall v body)
  -- we want to respect scoping when substituting a type variable, so we don't
  -- enter the scope of the body if we have another forall binding the same name
  | var == v  = tp
  | otherwise = Forall v $ subTVar var subType body
subTVar var subType (Arr t1 t2) = Arr (subTVar var subType t1) (subTVar var subType t2)
subTVar var subType (TRcd Row{rowMap=rm, rowTail=rt}) = TRcd Row{rowMap=subTVar var subType <$> rm, rowTail=rt}
subTVar _ _ tp = tp

-- | Substitute a Var for a 'Term'
subTmVar :: Varname -> Term -> Term -> Term
subTmVar var subTm (Trm tp e) = case e of
  Var v | v == var  -> subTm
        | otherwise -> Trm tp $ Var v
  -- do we keep the same type? (doesn't matter really)
  Annot tm tp'      -> Trm tp $ Annot (subTmVar var subTm tm) tp'
  App tm1 tm2       -> Trm tp $ App (subTmVar var subTm tm1) (subTmVar var subTm tm2)
  Lambda v body
    -- don't do anything if the substitution gets shadowed
    | v == var      -> Trm tp e
    | otherwise     -> Trm tp $ Lambda v (subTmVar var subTm body)
  Unit              -> Trm tp Unit
  Rcd Row{rowMap=rm, rowTail=rt} -> Trm tp $ Rcd Row{rowMap=subTmVar var subTm <$> rm, rowTail=rt}
  Prj tm lbl -> Trm tp $ Prj (subTmVar var subTm tm) lbl

unitU :: TermU
unitU = Trm () Unit

lamU :: Varname -> TermU -> TermU
lamU x e = Trm () (Lambda x e)

multiLamU :: [Varname] -> TermU -> TermU
multiLamU xs e = foldr lamU e xs

appU :: TermU -> TermU -> TermU
appU e1 e2 = Trm () (App e1 e2)

varU :: Varname -> TermU
varU = Trm () . Var

rcdU :: Map Label TermU -> TermU
-- concrete records have no tails
rcdU = Trm () . Rcd . (\rm -> Row rm Nothing)

prjU :: TermU -> Label -> TermU
prjU tm lbl = Trm () (Prj tm lbl)
