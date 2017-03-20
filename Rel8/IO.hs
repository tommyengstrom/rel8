{-# LANGUAGE RankNTypes #-}
module Rel8.IO
  (
    -- * @SELECT@
    select

    -- * @INSERT@
  , insert
  , insertReturning
  , insert1Returning

    -- * @UPDATE@
  , update
  , updateReturning

    -- * @DELETE@
  , delete
  ) where

import Control.Arrow
import Control.Foldl
import Data.ByteString (ByteString)
import Data.Int (Int64)
import qualified Data.List.NonEmpty as NEL
import Data.Text (pack)
import Data.Text.Encoding (encodeUtf8)
import qualified Hasql.Decoders as Hasql
import qualified Hasql.Encoders as Encode
import qualified Hasql.Query as Hasql
import qualified Opaleye as O
import qualified Opaleye.Internal.Column as O
import qualified Opaleye.Internal.HaskellDB.PrimQuery as O
import qualified Opaleye.Internal.HaskellDB.Sql as O
import qualified Opaleye.Internal.HaskellDB.Sql.Default as O
import qualified Opaleye.Internal.HaskellDB.Sql.Generate as O
import qualified Opaleye.Internal.HaskellDB.Sql.Print as O
import qualified Opaleye.Internal.Optimize as O
import qualified Opaleye.Internal.PrimQuery as O
import qualified Opaleye.Internal.Print as O
import qualified Opaleye.Internal.QueryArr as O
import qualified Opaleye.Internal.Sql as O (sql)
import qualified Opaleye.Internal.Sql as Sql
import qualified Opaleye.Internal.Table as O
import qualified Opaleye.Internal.Tag as O
import qualified Opaleye.Internal.Unpackspec as O
import Rel8.Internal.Expr
import Rel8.Internal.Operators
import Rel8.Internal.Table hiding (columns)
import Rel8.Internal.Types

--------------------------------------------------------------------------------
-- | Transform a Rel8 query (that may contain parameters) into a Hasql 'Query'.
--
-- The supplied 'Fold' instructs how multiple rows are combined into the final
-- Haskell query result - if you just want a list of all rows, use 'list' or
-- 'vector'.
--
-- To run the resulting 'Hasql.Query', use @Hasql.Sesison.query@ or
-- @Hasql.Transaction.query@.
select
  :: (Table row result)
  => O.Query row -> Fold result results -> Hasql.Query () results
select q (Fold step begin done) =
  case prepareQuery unpackColumns q of
    Nothing -> arr (const (done begin))
    Just sql ->
      Hasql.statement
        sql
        Encode.unit
        (fmap done (Hasql.foldlRows step begin rowParser))
        True

-- | Insert rows into a 'BaseTable'. This runs a @INSERT@ statement.
insert
  :: (BaseTable table)
  => [table Insert] -> Hasql.Query () Int64
insert rows =
  case NEL.nonEmpty rows of
    Nothing ->
      -- Inserting the empty list is just the same as returning 0
      arr (const 0)
    Just columns' ->
      Hasql.statement
        (encodeUtf8 (pack (arrangeInsertManySql tableDefinition columns')))
        Encode.unit
        Hasql.rowsAffected
        False

-- | Insert rows into a 'BaseTable', and return the inserted rows. This runs a
-- @INSERT ... RETURNING@ statement, and be useful to immediately retrieve
-- any default values (such as automatically generated primary keys).
insertReturning
  :: (BaseTable table)
  => [table Insert]
  -> Fold (table QueryResult) results
  -> Hasql.Query () results
insertReturning rows (Fold step begin done) =
  case NEL.nonEmpty rows of
    Nothing -> arr (const (done begin))
    Just columns' ->
      Hasql.statement
        (encodeUtf8
           (pack
              (arrangeInsertManyReturningSql
                 unpackColumns
                 tableDefinition
                 columns'
                 id)))
        Encode.unit
        (done <$> Hasql.foldlRows step begin rowParser)
        False

-- | Insert a single row 'BaseTable', and return the inserted row. This runs a
-- @INSERT ... RETURNING@ statement, and be useful to immediately retrieve
-- any default values (such as automatically generated primary keys).
--
-- *WARNING* - it is assumed that the @INSERT@ will insert a row assuming
-- no exception happens. This assumption can be violated with triggers on
-- tables that prevent the row from being inserted. If this could happen,
-- consider 'insertReturning'.
insert1Returning
  :: (BaseTable table)
  => table Insert -> Hasql.Query () (table QueryResult)
insert1Returning row =
  Hasql.statement
    (encodeUtf8
       (pack
          (arrangeInsertManyReturningSql
             unpackColumns
             tableDefinition
             (pure row)
             id)))
    Encode.unit
    (Hasql.singleRow rowParser)
    False

-- | Update rows in a 'BaseTable'. Corresponds to @UPDATE@.
update
  :: (BaseTable table, Predicate bool)
  => (table Expr -> Expr bool)
     -- ^ A predicate specifying which rows should be updated.
  -> (table Expr -> table Expr)
     -- ^ The transformation to apply to each row. This function is given the
     -- rows current value as input.
  -> Hasql.Query () Int64
     -- ^ The amount of rows updated.
update f up =
  Hasql.statement
    (encodeUtf8
       (pack
          (arrangeUpdateSql
             tableDefinitionUpdate
             up
             (exprToColumn . toNullable . f))))
    Encode.unit
    Hasql.rowsAffected
    False

-- | Update rows in a 'BaseTable' and return the results. Corresponds to
-- @UPDATE ... RETURNING@.
updateReturning
  :: (BaseTable table, Predicate bool)
  => (table Expr -> Expr bool)
  -> (table Expr -> table Expr)
  -> Fold (table QueryResult) results
  -> Hasql.Query () results
updateReturning f up (Fold step begin done) =
  Hasql.statement
    (encodeUtf8
       (pack
          (arrangeUpdateSql
             tableDefinitionUpdate
             up
             (exprToColumn . toNullable . f))))
    Encode.unit
    (done <$> Hasql.foldlRows step begin rowParser)
    False

-- | Given a 'BaseTable' and a predicate, @DELETE@ all rows that match.
delete
  :: (BaseTable table, Predicate bool)
  => (table Expr -> Expr bool) -> Hasql.Query () Int64
delete f =
  Hasql.statement
    (encodeUtf8 (pack (arrangeDeleteSql tableDefinition (exprToColumn . toNullable . f))))
    Encode.unit
    Hasql.rowsAffected
    False

--------------------------------------------------------------------------------

prepareQuery :: O.Unpackspec columns a
             -> O.Query columns
             -> Maybe ByteString
prepareQuery u q = fmap (encodeUtf8 . pack) sql
  where
    (_, sql) = showSqlExplicit u q

showSqlExplicit :: O.Unpackspec s t -> O.QueryArr () s -> (s, Maybe String)
showSqlExplicit up q =
  case O.runSimpleQueryArrStart q () of
    (x, y, z) -> (x, (formatAndShowSQL (O.collectPEs up x, O.optimize y, z)))

formatAndShowSQL
  :: ([O.PrimExpr],O.PrimQuery' a,O.Tag) -> Maybe String
formatAndShowSQL =
  fmap (show . O.ppSql . O.sql) . traverse2Of3 O.removeEmpty
  where
        -- Just a lens
        traverse2Of3
          :: Functor f
          => (a -> f b) -> (x,a,y) -> f (x,b,y)
        traverse2Of3 f (x,y,z) =
          fmap (\y' -> (x,y',z))
               (f y)

arrangeInsertMany :: O.Table columns a -> NEL.NonEmpty columns -> O.SqlInsert
arrangeInsertMany table columns = insert'
  where
    writer = O.tablePropertiesWriter (O.tableProperties table)
    (columnExprs, columnNames) = O.runWriter' writer columns
    insert' =
      O.sqlInsert
        O.defaultSqlGenerator
        (O.tiToSqlTable (O.tableIdentifier table))
        columnNames
        columnExprs

arrangeInsertManySql :: O.Table columns a -> NEL.NonEmpty columns -> String
arrangeInsertManySql t cs = show (O.ppInsert (arrangeInsertMany t cs))

arrangeInsertManyReturning
  :: O.Unpackspec columnsReturned ignored
  -> O.Table columnsW columnsR
  -> NEL.NonEmpty columnsW
  -> (columnsR -> columnsReturned)
  -> Sql.Returning O.SqlInsert
arrangeInsertManyReturning unpackspec table columns returningf =
  Sql.Returning insert' returningSEs
  where
    insert' = arrangeInsertMany table columns
    O.View columnsR = O.tablePropertiesView (O.tableProperties table)
    returningPEs = O.collectPEs unpackspec (returningf columnsR)
    returningSEs = Sql.ensureColumnsGen id (map Sql.sqlExpr returningPEs)

arrangeInsertManyReturningSql
  :: O.Unpackspec columnsReturned ignored
  -> O.Table columnsW columnsR
  -> NEL.NonEmpty columnsW
  -> (columnsR -> columnsReturned)
  -> String
arrangeInsertManyReturningSql a b c d =
  show (O.ppInsertReturning (arrangeInsertManyReturning a b c d))

arrangeUpdate
  :: O.Table columnsW columnsR
  -> (columnsR -> columnsW)
  -> (columnsR -> O.Column O.PGBool)
  -> O.SqlUpdate
arrangeUpdate table updateF cond =
  O.sqlUpdate
    O.defaultSqlGenerator
    (O.tiToSqlTable (O.tableIdentifier table))
    [condExpr]
    (update' tableCols)
  where
    O.TableProperties writer (O.View tableCols) = O.tableProperties table
    update' = map (\(x, y) -> (y, x)) . O.runWriter writer . updateF
    O.Column condExpr = cond tableCols

arrangeUpdateSql
  :: O.Table columnsW columnsR
  -> (columnsR -> columnsW)
  -> (columnsR -> O.Column O.PGBool)
  -> String
arrangeUpdateSql a b c = show (O.ppUpdate (arrangeUpdate a b c))

arrangeDelete :: O.Table a columnsR
              -> (columnsR -> O.Column O.PGBool)
              -> O.SqlDelete
arrangeDelete table cond =
  O.sqlDelete
    O.defaultSqlGenerator
    (O.tiToSqlTable (O.tableIdentifier table))
    [condExpr]
  where
    O.Column condExpr = cond tableCols
    O.View tableCols = O.tablePropertiesView (O.tableProperties table)

arrangeDeleteSql :: O.Table a columnsR
                 -> (columnsR -> O.Column O.PGBool)
                 -> String
arrangeDeleteSql a b = show (O.ppDelete (arrangeDelete a b))
