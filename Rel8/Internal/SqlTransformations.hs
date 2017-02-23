{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
module Rel8.Internal.SqlTransformations where

import Control.Applicative
import Control.Arrow (first)
import Data.Foldable (toList)
import Data.Functor.Identity
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as M

import Data.Maybe (mapMaybe)
import Data.Semigroup ((<>))
import qualified Data.Set as S
import Opaleye.Internal.HaskellDB.Sql
       (SqlExpr, SqlColumn(..), SqlExpr(..), SqlRangeBound(..))
import Opaleye.Internal.Sql as O

--------------------------------------------------------------------------------
-- | Traversal suitable for use with @Control.Lens.Plate@. Selects the immediate
-- Selects within a Select.

selectPlate :: Applicative f => (O.Select -> f O.Select) -> O.Select -> f O.Select
selectPlate f (SelectFrom From {..}) =
  SelectFrom <$>
    (From <$> pure attrs
          <*> traverse f tables
          <*> pure criteria
          <*> pure groupBy
          <*> pure orderBy
          <*> pure limit
          <*> pure offset)
selectPlate f (SelectJoin Join {..}) =
  SelectJoin <$> (Join <$> pure jJoinType
                       <*> both f jTables
                       <*> pure jCond)
selectPlate f (SelectBinary Binary {..}) =
  SelectBinary <$> (Binary <$> pure bOp
                           <*> f bSelect1
                           <*> f bSelect2)
selectPlate f (SelectLabel Label {..}) =
  SelectLabel <$> (Label <$> pure lLabel
                         <*> f lSelect)
selectPlate _ other = pure other


--------------------------------------------------------------------------------
-- | Traverse all SqlExprs in a Select

selectExprs :: Applicative f => (SqlExpr -> f SqlExpr) -> O.Select -> f O.Select
selectExprs f (SelectFrom From{..}) =
  SelectFrom <$>
    (From <$> traverseAttrs f attrs
          <*> (traverse . selectExprs) f tables
          <*> traverse f criteria
          <*> (traverse . traverse) f groupBy
          <*> (traverse . _1) f orderBy
          <*> pure limit
          <*> pure offset)
  where
selectExprs f (SelectJoin Join{..}) =
  SelectJoin <$> (Join <$> pure jJoinType
                       <*> (both . selectExprs) f jTables
                       <*> f jCond)
selectExprs f (SelectBinary Binary {..}) =
  SelectBinary <$> (Binary <$> pure bOp
                           <*> selectExprs f bSelect1
                           <*> selectExprs f bSelect2)
selectExprs f (SelectLabel Label {..}) =
  SelectLabel <$> (Label <$> pure lLabel
                         <*> selectExprs f lSelect)
selectExprs f (RelExpr expr) = RelExpr <$> f expr
selectExprs f (SelectValues (Values{..})) =
  SelectValues <$> (Values <$> traverseAttrs f vAttrs
                           <*> (traverse . traverse) f vValues)
selectExprs _ other = pure other


--------------------------------------------------------------------------------
-- | Traverse all SqlExprs in SelectAttrs

traverseAttrs :: Applicative f => (SqlExpr -> f SqlExpr) -> SelectAttrs -> f SelectAttrs
traverseAttrs f (SelectAttrs a) = SelectAttrs <$> (traverse._1) f a
traverseAttrs f (SelectAttrsStar a) = SelectAttrsStar <$> (traverse._1) f a
traverseAttrs _ other = pure other


--------------------------------------------------------------------------------
both :: Applicative f => (t -> f b) -> (t, t) -> f (b, b)
both f (a,b) = liftA2 (,) (f a) (f b)

_1 :: Applicative f => (t -> f a) -> (t, b) -> f (a, b)
_1 f (a, b) = liftA2 (,) (f a) (pure b)


--------------------------------------------------------------------------------
-- | Traversal suitable for use with @Control.Lens.Plate@. Selects the immediate
-- SqlExprs within a SqlExpr.

traverseExpr :: (SqlExpr -> Identity SqlExpr) -> SqlExpr -> Identity SqlExpr
traverseExpr f (CompositeSqlExpr expr s) = CompositeSqlExpr <$> f expr <*> pure s
traverseExpr f (BinSqlExpr a b c) = BinSqlExpr <$> pure a <*> f b <*> f c
traverseExpr f (PrefixSqlExpr a b) = PrefixSqlExpr <$> pure a <*> f b
traverseExpr f (PostfixSqlExpr a b) = PostfixSqlExpr <$> pure a <*> f b
traverseExpr f (FunSqlExpr a b) = FunSqlExpr <$> pure a <*> traverse f b
traverseExpr f (AggrFunSqlExpr a b c d) = AggrFunSqlExpr <$> pure a <*> traverse f b <*> (traverse._1) f c <*> pure d
traverseExpr f (CaseSqlExpr a b) = CaseSqlExpr <$> (traverse.both) f a <*> f b
traverseExpr f (ListSqlExpr b) = ListSqlExpr <$> traverse f b
traverseExpr f (ParamSqlExpr a b) = ParamSqlExpr <$> pure a <*> f b
traverseExpr f (ParensSqlExpr a) = ParensSqlExpr <$> f a
traverseExpr f (CastSqlExpr a b) = CastSqlExpr <$> pure a <*> f b
traverseExpr f (ArraySqlExpr a) = ArraySqlExpr <$> traverse f a
traverseExpr f (RangeSqlExpr a b) =
  RangeSqlExpr <$> traverseRangeBound a <*> traverseRangeBound b
  where
    traverseRangeBound (Inclusive e) = Inclusive <$> f e
    traverseRangeBound (Exclusive e) = Exclusive <$> f e
    traverseRangeBound other = pure other
traverseExpr _ other = pure other


--------------------------------------------------------------------------------
--
-- Simplify a SELECT query. The following optimisations are applied:
--
-- 1. SELECT a, b, c FROM (SELECT .. ) is rewritten to just the inner select.
--    Any outer predicates are pushed into the inner select.
--    The outer projections are rewritten in terms of the inner most columns.
--
-- 2. SELECT * FROM inner is rewritten to just the inner query. Like (1), but
--    applies to VALUES expressions.
--
--------------------------------------------------------------------------------

simplifySelect :: O.Select -> O.Select
simplifySelect =
  unselectRedundantColumns
  . rewriteOf selectPlate (\s -> removeNeedlessSelects s <|> dropOffset0 s)
  . over selectExprs (rewriteOf traverseExpr dropColumnParens)
  . unselectRedundantColumns

--------------------------------------------------------------------------------
-- Turns ("a") = ("b") into just "a" = "b".
dropColumnParens :: SqlExpr -> Maybe SqlExpr
dropColumnParens (BinSqlExpr op (ParensSqlExpr (ColumnSqlExpr a)) right) =
  Just (BinSqlExpr op (ColumnSqlExpr a) right)
dropColumnParens (BinSqlExpr op left (ParensSqlExpr (ColumnSqlExpr a))) =
  Just (BinSqlExpr op left (ColumnSqlExpr a))
dropColumnParens _ = Nothing

--------------------------------------------------------------------------------
removeNeedlessSelects :: O.Select -> Maybe O.Select
removeNeedlessSelects
  (SelectFrom From { attrs = outerAttrs
                   , tables = [SelectFrom inner@From { attrs = innerAttrs }]
                   , criteria = []
                   , groupBy = Nothing
                   , orderBy = []
                   , limit = Nothing
                   , offset = Nothing
                   }) =
  let newAttrs =
        case outerAttrs of
          -- SELECT * FROM (SELECT attrs FROM ...) -> SELECT attrs FROM
          Star ->
            innerAttrs

          SelectAttrs outerAttrs' ->
            case innerAttrs of
              Star ->
                SelectAttrs outerAttrs'
              SelectAttrs innerAttrs' ->
                SelectAttrs (fmap (first (substitute innerAttrs')) outerAttrs')
              SelectAttrsStar innerAttrs' ->
                SelectAttrs (fmap (first (substitute innerAttrs')) outerAttrs')

          SelectAttrsStar outerAttrs' ->
            case innerAttrs of
              Star ->
                SelectAttrsStar outerAttrs'
              SelectAttrs innerAttrs' ->
                SelectAttrs (fmap (first (substitute innerAttrs')) outerAttrs' <>
                            innerAttrs')
              SelectAttrsStar innerAttrs' ->
                SelectAttrsStar (fmap (first (substitute innerAttrs')) outerAttrs' <>
                                  innerAttrs')

  in Just (SelectFrom inner {attrs = newAttrs})

removeNeedlessSelects _ = Nothing

--------------------------------------------------------------------------------
unselectRedundantColumns :: O.Select -> O.Select
unselectRedundantColumns =
  \s ->
    case s of
      SelectFrom f@From {tables} ->
        SelectFrom f {tables = fmap (compact (dependencies s)) tables}
      other -> other

  where

    dependencies :: O.Select -> S.Set String
    dependencies (SelectFrom From { attrs
                                  , criteria
                                  , groupBy
                                  , orderBy
                                  }) =
      mconcat
        [ foldMap exprReferences (attrExprs attrs)
        , foldMap exprReferences criteria
        , foldMap (foldMap exprReferences) groupBy
        , foldMap (exprReferences . fst) orderBy
        ]
    dependencies (SelectJoin Join{..}) = exprReferences jCond
    dependencies _ = mempty

    attrExprs :: SelectAttrs -> [SqlExpr]
    attrExprs Star = []
    attrExprs (SelectAttrs attrs) = map fst (toList attrs)
    attrExprs (SelectAttrsStar attrs) = map fst (toList attrs)

    exprReferences :: SqlExpr -> S.Set String
    exprReferences (ColumnSqlExpr (SqlColumn a)) = S.singleton a
    exprReferences (CompositeSqlExpr a _) = exprReferences a
    exprReferences (BinSqlExpr _ a b) = exprReferences a <> exprReferences b
    exprReferences (PrefixSqlExpr _ a) = exprReferences a
    exprReferences (PostfixSqlExpr _ a) = exprReferences a
    exprReferences (FunSqlExpr _ args) = foldMap exprReferences args
    exprReferences (ConstSqlExpr _) = mempty
    exprReferences (CaseSqlExpr a b) =
      foldMap exprReferences (fmap fst a) <> foldMap exprReferences (fmap snd a) <>
      exprReferences b
    exprReferences (ListSqlExpr a) = foldMap exprReferences a
    exprReferences (ParamSqlExpr _ a) = exprReferences a
    exprReferences (ParensSqlExpr a) = exprReferences a
    exprReferences (CastSqlExpr _ a) = exprReferences a
    exprReferences (ArraySqlExpr a) = foldMap exprReferences a

    unColumn (SqlColumn name) = name

    filterAttrsKeeping :: S.Set String -> SelectAttrs -> SelectAttrs
    filterAttrsKeeping _ Star = Star
    filterAttrsKeeping retain (SelectAttrs attrs) =
      case filter (maybe False ((`S.member` retain) . unColumn) . snd) (toList attrs) of
        [] -> SelectAttrs ((ConstSqlExpr "true", Nothing) :| [])
        (a:as) -> SelectAttrs (a :| as)
    filterAttrsKeeping retain (SelectAttrsStar attrs) =
      case filter (maybe False ((`S.member` retain) . unColumn) . snd) (toList attrs) of
        [] -> Star
        (a:as) -> SelectAttrsStar (a :| as)

    compact :: S.Set String -> O.Select -> O.Select
    compact keep (SelectFrom f2@From {attrs, tables}) =
      let reducedAttrs = f2 {attrs = filterAttrsKeeping keep attrs}
          keep' = mappend keep (dependencies (SelectFrom reducedAttrs))
      in SelectFrom reducedAttrs {tables = fmap (compact keep') tables}
    compact keep s@(SelectJoin j@Join {jTables = (l, r)}) =
      let keep' = mappend keep (dependencies s)
      in SelectJoin j {jTables = (compact keep' l, compact keep' r)}
    compact keep s@(SelectBinary b@Binary {bSelect1 = l, bSelect2 = r}) =
      let keep' = mappend keep (dependencies s)
      in SelectBinary b {bSelect1 = compact keep' l, bSelect2 = compact keep' r}
    compact keep s@(SelectLabel l@Label { lSelect }) =
      let keep' = mappend keep (dependencies s)
      in SelectLabel l {lSelect = compact keep' lSelect}
    compact _ other = other


--------------------------------------------------------------------------------
dropOffset0 :: O.Select -> Maybe O.Select
dropOffset0 (SelectFrom f@From {offset = Just 0}) =
  Just (SelectFrom f {offset = Nothing})
dropOffset0 _ = Nothing

--------------------------------------------------------------------------------
--
-- Given a 'SqlExpr' and environment mapping column names to 'SqlExpr's,
-- perform substitution of column names to their underlying expressions.
--
--------------------------------------------------------------------------------

substitute
  :: NonEmpty (SqlExpr, Maybe SqlColumn)
  -> SqlExpr
  -> SqlExpr
substitute exprs expr = transformOf traverseExpr expand expr
  where
    expand :: SqlExpr -> SqlExpr
    expand free@(ColumnSqlExpr (SqlColumn sqlColumn)) =
      case M.lookup sqlColumn env of
        Just a -> a
        Nothing -> free -- Not in the environment, free variable supplied by
                        -- another query?
    expand other = other

    env :: M.Map String SqlExpr
    env =
      M.fromList
        (mapMaybe
           (\(a, mcol) -> fmap (\(SqlColumn str) -> (str, a)) mcol)
           (toList exprs))

transformOf :: ((a -> Identity a) -> a -> Identity a) -> (a -> a) -> a -> a
transformOf l f = go where
  go = f . over l go
{-# INLINE transformOf #-}

rewriteOf :: ((a -> Identity a) -> a -> Identity a) -> (a -> Maybe a) -> a -> a
rewriteOf l f = go where
  go = transformOf l (\x -> maybe x go (f x))

over :: ((a2 -> Identity a1) -> a -> Identity c) -> (a2 -> a1) -> a -> c
over l f = runIdentity . l (Identity . f)
