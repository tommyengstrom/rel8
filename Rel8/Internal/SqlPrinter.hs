{-# LANGUAGE OverloadedStrings #-}

module Rel8.Internal.SqlPrinter where

import Data.Foldable (foldl', toList)
import qualified Data.List.NonEmpty as NEL
import qualified Data.Text as ST
import Data.Text.Lazy (pack)
import Opaleye.Internal.HaskellDB.Sql
import Opaleye.Internal.Sql hiding (empty)
import Text.PrettyPrint.Leijen.Text
       (Doc, group, hang, vsep, empty, fillSep, punctuate, comma, hsep,
        dquotes, text, equals, parens, align, indent, hcat, brackets, vcat)
import Data.Monoid ((<>))

-- Silliness to avoid "ORDER BY 1" etc. meaning order by the first
-- column.  We need an identity function, but due to
-- https://github.com/tomjaguarpaw/haskell-opaleye/issues/100 we need
-- to be careful not to be over enthusiastic.  Just apply COALESCE to
-- literals.
deliteral :: SqlExpr -> SqlExpr
deliteral expr@(ConstSqlExpr _) = FunSqlExpr "COALESCE" [expr]
deliteral expr = expr

-- | Attempt to render a series of Docs on one line, but if that can't be
-- done, fall back to rendering each Doc on a new line, with all but the first
-- Doc indentend by 2 spaces.
oneLineOrHang :: [Doc] -> Doc
oneLineOrHang = group . hang 2 . vsep

ppWhere :: [SqlExpr] -> Doc
ppWhere [] = empty
ppWhere (e:es) =
  oneLineOrHang ["WHERE", ppSqlExpr (foldl' (BinSqlExpr "AND") e es)]

ppGroupBy :: [SqlExpr] -> Doc
ppGroupBy es = oneLineOrHang ["GROUP BY", ppGroupAttrs es]
  where
    ppGroupAttrs :: [SqlExpr] -> Doc
    ppGroupAttrs cs = fillSep (punctuate comma (map (ppSqlExpr . deliteral) cs))

ppOrderBy :: [(SqlExpr, SqlOrder)] -> Doc
ppOrderBy [] = mempty
ppOrderBy ord =
  oneLineOrHang
    ["ORDER BY", fillSep (punctuate comma (map ppOrd ord))]
  where
    ppOrd (e, o) =
      hsep [ppSqlExpr (deliteral e), ppSqlDirection o, ppSqlNulls o]

ppSqlDirection :: SqlOrder -> Doc
ppSqlDirection x = case sqlOrderDirection x of
  SqlAsc  -> "ASC"
  SqlDesc -> "DESC"

ppSqlNulls :: SqlOrder -> Doc
ppSqlNulls x =
  case sqlOrderNulls x of
    SqlNullsFirst -> "NULLS FIRST"
    SqlNullsLast -> "NULLS LAST"

ppAs :: Maybe String -> Doc -> Doc
ppAs Nothing      expr = expr
ppAs (Just alias) expr = hsep [expr, "as", dquotes (text (pack alias))]

ppUpdate :: SqlUpdate -> Doc
ppUpdate (SqlUpdate table assigns predicate) =
  group
    (vsep
       [ oneLineOrHang ["UPDATE", ppTable table]
       , oneLineOrHang
           ["SET", group (vsep (punctuate comma (map ppAssign assigns)))]
       , ppWhere predicate
       ])
  where
    ppAssign (c, e) = hsep [ppSqlColumn c, equals, ppSqlExpr e]

ppDelete :: SqlDelete -> Doc
ppDelete (SqlDelete table predicate) =
  group (vsep [hsep ["DELETE FROM", ppTable table], ppWhere predicate])

ppInsert :: SqlInsert -> Doc
ppInsert (SqlInsert table names vs) =
  group
    (vsep
       [ oneLineOrHang
           [ "INSERT INTO"
           , oneLineOrHang [ppTable table, compactTuple (map ppSqlColumn names)]
           ]
       , oneLineOrHang
           [ "VALUES"
           , group
               (vsep
                  (punctuate
                     comma
                     (map (compactTuple . map ppSqlExpr) (toList vs))))
           ]
       ])

compactTuple :: [Doc] -> Doc
compactTuple = parens . align . fillSep . punctuate comma

ppSqlColumn :: SqlColumn -> Doc
ppSqlColumn (SqlColumn s) = dquotes (text (pack s))

-- Postgres treats schema and table names as lower case unless quoted.
ppTable :: SqlTable -> Doc
ppTable st =
  case sqlTableSchemaName st of
    Just sn -> dquotes (text (pack sn)) <> "." <> tname
    Nothing -> tname
  where
    tname = dquotes (text (pack (sqlTableName st)))

ppStartBound :: SqlRangeBound -> Doc
ppStartBound (Inclusive a) = "'[" <> ppSqlExpr a
ppStartBound (Exclusive a) = "'(" <> ppSqlExpr a
ppStartBound (PosInfinity) = "'(infinity"
ppStartBound (NegInfinity) = "'(-infinity"

ppEndBound :: SqlRangeBound -> Doc
ppEndBound (Inclusive a) = ppSqlExpr a <> "]'"
ppEndBound (Exclusive a) = ppSqlExpr a <> ")'"
ppEndBound (PosInfinity) = "infinity)'"
ppEndBound (NegInfinity) = "-infinity)'"

ppSqlExpr :: SqlExpr -> Doc
ppSqlExpr expr =
  case expr of
    ColumnSqlExpr c -> ppSqlColumn c
    CompositeSqlExpr s x -> parens (ppSqlExpr s) <> "." <> text (pack x)
    ParensSqlExpr e -> parens (align (ppSqlExpr e))
    BinSqlExpr op e1 e2 ->
      group (vsep [hsep [ppSqlExpr e1, text (pack op)], ppSqlExpr e2])
    PrefixSqlExpr op e -> hsep [text (pack op), ppSqlExpr e]
    PostfixSqlExpr op e -> hsep [ppSqlExpr e, text (pack op)]
    ConstSqlExpr c -> text (pack c)
    CaseSqlExpr cs el ->
      group
        (align
           (vsep
              [ "CASE"
              , indent 2 (vsep (toList (fmap ppWhen cs)))
              , indent 2 (oneLineOrHang ["ELSE", ppSqlExpr el])
              , "END"
              ]))
      where ppWhen (w, t) =
              oneLineOrHang [hsep ["WHEN", ppSqlExpr w, "THEN"], ppSqlExpr t]
    ListSqlExpr es -> compactTuple (map ppSqlExpr (toList es))
    ParamSqlExpr _ v -> ppSqlExpr v
    PlaceHolderSqlExpr -> "?"
    CastSqlExpr typ e ->
      hcat ["CAST", parens (hsep [ppSqlExpr e, "AS", text (pack typ)])]
    DefaultSqlExpr -> "DEFAULT"
    ArraySqlExpr es ->
      hcat
        [ "ARRAY"
        , brackets (align (fillSep (punctuate comma (map ppSqlExpr es))))
        ]
    RangeSqlExpr start end ->
      hsep (punctuate comma [ppStartBound start, ppEndBound end])
    FunSqlExpr f es -> text (pack f) <> compactTuple (map ppSqlExpr es)
    AggrFunSqlExpr f es ord distinct ->
      hcat
        [ text (pack f)
        , parens
            (align
               (hsep
                  [ ppSqlDistinct distinct
                  , fillSep (punctuate comma (map ppSqlExpr es))
                  , ppOrderBy ord
                  ]))
        ]

ppSqlDistinct :: SqlDistinct -> Doc
ppSqlDistinct SqlDistinct = text "DISTINCT"
ppSqlDistinct SqlNotDistinct = mempty

-- | Top-level pretty printer.
ppSelect :: Select -> Doc
ppSelect (SelectFrom s) = ppSelectFrom s
ppSelect (Table table) =
  ppSelectFrom
    (From
     { tables = [Table table]
     , attrs = Star
     , criteria = []
     , groupBy = Nothing
     , orderBy = []
     , limit = Nothing
     , offset = Nothing
     })
ppSelect (SelectValues v) = ppSelectValues v
ppSelect (SelectBinary v) = ppSelectBinary v
ppSelect (SelectLabel v)  = ppSelectLabel v
ppSelect (RelExpr expr) =
  ppSelectFrom
    (From
     { tables = []
     , attrs = (SelectAttrs ((expr, Nothing) NEL.:| []))
     , criteria = []
     , groupBy = Nothing
     , orderBy = []
     , limit = Nothing
     , offset = Nothing
     })
ppSelect (SelectJoin j) =
  ppSelectFrom
    (From
     { tables = [SelectJoin j]
     , attrs = Star
     , criteria = []
     , groupBy = Nothing
     , orderBy = []
     , limit = Nothing
     , offset = Nothing
     })
ppSelect (SelectAntijoin aj) = ppSelectAntijoin aj

ppSelectAntijoin :: Antijoin -> Doc
ppSelectAntijoin (Antijoin a b) =
  vsep
    [ ppSelect
        (SelectFrom
           From
           { tables = [a]
           , attrs = Star
           , criteria = []
           , groupBy = Nothing
           , orderBy = []
           , limit = Nothing
           , offset = Nothing
           })
    , hsep ["WHERE", "NOT", "EXISTS", parens (align (ppSql b))]
    ]

ppSql :: Select -> Doc
ppSql (SelectFrom s)     = ppSelectFrom s
ppSql (Table table)      = ppTable table
ppSql (RelExpr expr)     = ppSqlExpr expr
ppSql (SelectJoin j)     = ppSelectJoin j
ppSql (SelectValues v)   = ppSelectValues v
ppSql (SelectBinary v)   = ppSelectBinary v
ppSql (SelectLabel v)    = ppSelectLabel v
ppSql (SelectAntijoin a) = ppSelectAntijoin a

ppSelectFrom :: From -> Doc
ppSelectFrom s =
  group
    (vsep
       [ oneLineOrHang ["SELECT", ppAttrs (attrs s)]
       , ppTables (tables s)
       , ppWhere (criteria s)
       , ppGroupByOptional (groupBy s)
       , ppOrderBy (orderBy s)
       , ppLimit (limit s)
       , ppOffset (offset s)
       ])

asterisk :: Doc
asterisk = "*"

ppSelectJoin :: Join -> Doc
ppSelectJoin j =
  group
    (vsep
       [ ppTableAlias (tableAlias 1 s1)
       , oneLineOrHang
           [ ppJoinType (jJoinType j)
           , ppTableAlias (tableAlias 2 s2)
           , oneLineOrHang ["ON", ppSqlExpr (jCond j)]
           ]
       ])
  where
    (s1, s2) = jTables j

ppSelectValues :: Values -> Doc
ppSelectValues v =
  group
    (vsep
       [ oneLineOrHang ["SELECT", ppAttrs (vAttrs v)]
       , oneLineOrHang ["FROM", ppValues (vValues v)]
       ])

ppSelectBinary :: Binary -> Doc
ppSelectBinary b =
  vsep [ppSql (bSelect1 b), ppBinOp (bOp b), ppSql (bSelect2 b)]

ppSelectLabel :: Label -> Doc
ppSelectLabel l =
  vcat
    [ hsep ["/*", text (pack (defuseComments (lLabel l))), "*/"]
    , ppSql (lSelect l)
    ]
  where
    defuseComments =
      ST.unpack .
      ST.replace (ST.pack "--") (ST.pack " - - ") .
      ST.replace (ST.pack "/*") (ST.pack " / * ") .
      ST.replace (ST.pack "*/") (ST.pack " * / ") . ST.pack

ppJoinType :: JoinType -> Doc
ppJoinType LeftJoin  = "LEFT OUTER JOIN"
ppJoinType RightJoin = "RIGHT OUTER JOIN"
ppJoinType FullJoin  = "FULL OUTER JOIN"

ppAttrs :: SelectAttrs -> Doc
ppAttrs Star                 = asterisk
ppAttrs (SelectAttrs xs)     = fillSep (punctuate comma (map nameAs (toList xs)))
ppAttrs (SelectAttrsStar xs) = fillSep (punctuate comma (map nameAs (toList xs) ++ [asterisk]))

-- This is pretty much just nameAs from HaskellDB
nameAs :: (SqlExpr, Maybe SqlColumn) -> Doc
nameAs (expr, name) = ppAs (fmap unColumn name) (ppSqlExpr expr)
  where unColumn (SqlColumn s) = s

ppTables :: [Select] -> Doc
ppTables [] = empty
ppTables ts =
  oneLineOrHang
    ("FROM" : punctuate comma (map ppTableAlias (zipWith tableAlias [1 ..] ts)))

type TableAlias = String

tableAlias :: Int -> Select -> (TableAlias, Select)
tableAlias i select = ("T" ++ show i, select)

-- TODO: duplication with ppSql
ppTableAlias :: (TableAlias, Select) -> Doc
ppTableAlias (alias, select) = ppAs (Just alias) $ case select of
  Table table           -> ppTable table
  RelExpr expr          -> ppSqlExpr expr
  SelectFrom selectFrom -> parens (align (ppSelectFrom selectFrom))
  SelectJoin slj        -> parens (align (ppSelectJoin slj))
  SelectValues slv      -> parens (align (ppSelectValues slv))
  SelectBinary slb      -> parens (align (ppSelectBinary slb))
  SelectLabel sll       -> parens (align (ppSelectLabel sll))
  SelectAntijoin aj     -> parens (align (ppSelectAntijoin aj))

ppGroupByOptional :: Maybe (NEL.NonEmpty SqlExpr) -> Doc
ppGroupByOptional Nothing   = empty
ppGroupByOptional (Just xs) = ppGroupBy (NEL.toList xs)

ppLimit :: Maybe Int -> Doc
ppLimit Nothing = empty
ppLimit (Just n) = hsep ["LIMIT", text (pack (show n))]

ppOffset :: Maybe Int -> Doc
ppOffset Nothing = empty
ppOffset (Just n) = hsep ["OFFSET", text (pack (show n))]

ppValues :: [[SqlExpr]] -> Doc
ppValues v =
  ppAs
    (Just "V")
    (oneLineOrHang
       ["VALUES", group (vsep (punctuate comma (map ppValuesRow v)))])

ppValuesRow :: [SqlExpr] -> Doc
ppValuesRow = compactTuple . map ppSqlExpr

ppBinOp :: BinOp -> Doc
ppBinOp o = text $ case o of
  Union        -> "UNION"
  UnionAll     -> "UNION ALL"
  Except       -> "EXCEPT"
  ExceptAll    -> "EXCEPT ALL"
  Intersect    -> "INTERSECT"
  IntersectAll -> "INTERSECT ALL"

ppInsertReturning :: Returning SqlInsert -> Doc
ppInsertReturning (Returning insert returnExprs) =
  vsep
    [ ppInsert insert
    , oneLineOrHang
        [ "RETURNING"
        , fillSep (punctuate comma (map ppSqlExpr (toList returnExprs)))
        ]
    ]

ppUpdateReturning :: Returning SqlUpdate -> Doc
ppUpdateReturning (Returning update returnExprs) =
  vsep
    [ ppUpdate update
    , oneLineOrHang
        [ "RETURNING"
        , fillSep (punctuate comma (map ppSqlExpr (toList returnExprs)))
        ]
    ]
