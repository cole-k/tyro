module Pretty where

import Lang
import Data.List (intercalate)
import qualified Data.Map as M

-- TODO 1. clean this up
--      2. use an actual pretty printer
--      3. generalize the functions more

-- | Renders a 'Term' as a multiline tree, showing the type and subterm at each
-- depth.
prettyTerm :: Term -> String
prettyTerm = unlines . prettyTerm' 0

prettyTerm' :: Int -> Term -> [String]
prettyTerm' depth tm@(Trm tp e) =
  format [ "Type: " <> prettyType tp
         , "Term: " <> prettyTrmFlat tm]
  <>
  case e of
    Lambda _ tm -> prettyTerm' (depth + 1) tm
    App tm1 tm2 -> prettyTerm' (depth + 1) tm1 <> prettyTerm' (depth + 1) tm2
    _           -> []
  where
    -- indent by 2 spaces each iteration
    padding = replicate (depth*2) ' '
    format  = map (padding <>)

-- | Renders a 'Row a' as a string on a single line, using the provided function
-- to render the values. Low-tech typeclasses.
prettyRowWith :: (a -> String) -> Row a -> String
prettyRowWith render Row{rowMap=rm, rowTail=rt}=
  intercalate ", " (renderAtom <$> M.toList rm) <> renderedTail
  where
    renderAtom (label, value) = label <> ": " <> render value
    renderedTail = maybe "" (" | "<>) rt

prettyRowTrm :: Row (Trm a) -> String
prettyRowTrm = prettyRowWith prettyTrmFlat

prettyRowType :: Row Type -> String
prettyRowType = prettyRowWith prettyType

-- | Renders a 'Trm a' as a string on a single line without the annotation.
prettyTrmFlat :: Trm a -> String
prettyTrmFlat (Trm _ e) = case e of
  Var v -> v
  Unit  -> "()"
  Lambda x tm -> "(\\" <> x <> " -> " <> prettyTrmFlat tm <> ")"
  App tm1 tm2 -> "(" <> prettyTrmFlat tm1 <> " " <> prettyTrmFlat tm2 <> ")"
  Annot tm tp -> "(" <> prettyTrmFlat tm <> " :: " <> prettyType tp <> ")"
  Rcd row     -> "{" <> prettyRowTrm row <> "}"

prettyType :: Type -> String
prettyType (TVar v) = v
prettyType (EVar v) = v
prettyType (Forall v tp) = "∀" <> v <> ". " <> prettyType tp
-- The parens are to avoid ambiguity between higher order functions.
-- TODO only add parens when needed (track depth)
prettyType (Arr tp1 tp2) = "(" <> prettyType tp1 <> ") -> " <> prettyType tp2
prettyType TUnit = "()"
prettyType (TRcd row) = "{" <> prettyRowType row <> "}"
