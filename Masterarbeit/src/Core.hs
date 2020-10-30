module Core where

-- TODO: get rid of this small import
import Data.List (find)

-- Cedille Core (Aaron's Type Theory)
--
--   Nam   Hex   Syntax     Desc                                                 
-- ,-----,-----,----------,--------------------------------------------------,
-- | Typ | 0   | *        | type of types                                    |
-- | Kin | 1   | +        | type of type of types                            |
-- | Var | 2   |          | variable                                         |
-- | All | 3   | @x T t   | forall                                           |
-- | All | 3   | &x T t   | forall (erased)                                  |
-- | Lam | 4   | #x T t   | lambda                                           |
-- | Lam | 4   | %x T t   | lambda (erased)                                  |
-- | App | 5   | /f x     | application                                      |
-- | App | 5   | \f x     | application (erased)                             |
-- | Let | 6   | $x t u   | local definition                                 |
-- | Dep | 7   | ^x T U   | dependent intersection theorem                   |
-- | Bis | 8   | |x t U u | dependent intersection proof                     |
-- | Fst | 9   | <t       | first element of dependent intersection          |
-- | Snd | A   | >t       | second element of dependent intersection         |
-- | Eql | B   | =t u     | equality (t == u) theorem                        |
-- | Rfl | C   | :t u     | equality (t == t) proof, erases to u             |
-- | Sym | D   | ~e       | symmetry of equality (t == u implies u == t)     |
-- | Cst | E   | !e t u   | if (t == u) and (t : T), cast (u : U) to (u : T) |
-- | Rwt | F   | ?e T p   | if (t == u), cast (p : T[t/x]) to (p : U[t/x])   |
-- '-----'-----'----------'--------------------------------------------------'

-- Primitive constructors
data Prim r b
  = Typ
  | Kin
  | Var String
  | All Bool String r (b -> r)
  | Lam Bool String r (b -> r)
  | App Bool r r
  | Let String r (b -> r)
  | Dep String r (b -> r)
  | Bis String r (b -> r) r
  | Fst r
  | Snd r
  | Eql r r
  | Rfl r r
  | Sym r
  | Cst r r r
  | Rwt String r (b -> r) r
  | Err

-- Terms are layers of primitive constructors
newtype TermP
  = Term (Prim TermP TermP)

-- Anns are terms with type, normal-form and context annotations on each constructor
data Ann
  = Ann {
    valOf :: Prim Ann TermP,
    norOf :: TermP,
    typOf :: TermP
  }

-- Converts an ASCII String to a TermP
fromString :: String -> TermP
fromString src = snd (parseTerm src) [] where
  parseTerm :: String -> (String, [(String,TermP)] -> TermP)

  -- Whitespace
  parseTerm (' ' : src) =
    parseTerm src

  -- Newlines
  parseTerm ('\n' : src) =
    parseTerm src

  -- Type
  parseTerm ('*' : src) =
    (src, \ ctx -> Term Typ)

  -- Kind
  parseTerm ('+' : src) =
    (src, \ ctx -> Term Kin)

  -- Forall
  parseTerm ('@' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (All False nam (typ ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Forall (erased)
  parseTerm ('&' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (All True nam (typ ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Lambda
  parseTerm ('#' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Lam False nam (typ ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Lambda (erased)
  parseTerm ('%' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Lam True nam (typ ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Application
  parseTerm ('/' : src) = let
    (src0, fun) = parseTerm src
    (src1, arg) = parseTerm src0
    in (src1, \ ctx -> Term (App False (fun ctx) (arg ctx)))

  -- Application (erased)
  parseTerm ('\\' : src) = let
    (src0, fun) = parseTerm src
    (src1, arg) = parseTerm src0
    in (src1, \ ctx -> Term (App True (fun ctx) (arg ctx)))

  -- Local definition
  parseTerm ('$' : src) = let
    (src0, nam) = parseName src
    (src1, val) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Let nam (val ctx) (\ var -> bod ((nam,var) : ctx))))

  -- Dependent intersection
  parseTerm ('^' : src) = let
    (src0, nam) = parseName src
    (src1, fty) = parseTerm src0
    (src2, sty) = parseTerm src1
    in (src2, \ ctx -> Term (Dep nam (fty ctx) (\ var -> sty ((nam,var) : ctx))))

  -- Dependent intersection proof
  parseTerm ('|' : src) = let
    (src0, nam) = parseName src
    (src1, fst) = parseTerm src0
    (src2, typ) = parseTerm src1
    (src3, snd) = parseTerm src2
    in (src3, \ ctx -> Term (Bis nam (fst ctx) (\ var -> typ ((nam,var) : ctx)) (snd ctx)))

  -- First projection
  parseTerm ('<' : src) = let
    (src0, bis) = parseTerm src
    in (src0, \ ctx -> Term (Fst (bis ctx)))

  -- Second projection
  parseTerm ('>' : src) = let
    (src0, bis) = parseTerm src
    in (src0, \ ctx -> Term (Snd (bis ctx)))

  -- Equality
  parseTerm ('=' : src) = let
    (src0, fst) = parseTerm src
    (src1, snd) = parseTerm src0
    in (src1, \ ctx -> Term (Eql (fst ctx) (snd ctx)))

  -- Reflexivity
  parseTerm (':' : src) = let
    (src0, prf) = parseTerm src
    (src1, ret) = parseTerm src0
    in (src1, \ ctx -> Term (Rfl (prf ctx) (ret ctx)))

  -- Symmetry
  parseTerm ('~' : src) = let
    (src0, eql) = parseTerm src
    in (src0, \ ctx -> Term (Sym (eql ctx)))

  -- Cast
  parseTerm ('!' : src) = let
    (src0, eql) = parseTerm src
    (src1, fst) = parseTerm src2
    (src2, snd) = parseTerm src1
    in (src2, \ ctx -> Term (Cst (eql ctx) (fst ctx) (snd ctx)))

  -- Rewrite
  parseTerm ('?' : src) = let
    (src0, nam) = parseName src
    (src1, eql) = parseTerm src0
    (src2, typ) = parseTerm src1
    (src3, ret) = parseTerm src2
    in (src3, \ ctx -> Term (Rwt nam (eql ctx) (\ var -> typ ((nam,var) : ctx)) (ret ctx)))

  -- Error
  parseTerm ('_' : src) =
    (src, \ ctx -> Term Err)

  -- Variables
  parseTerm src = let
    (src', nam) = parseName src
    in (src', \ ctx ->
      case find ((nam ==) . fst) ctx of
        Nothing    -> Term (Var nam)
        Just (_,t) -> t)

  -- Names
  parseName :: String -> (String, String)
  parseName "" = ("", "")
  parseName (' ' : src) = (src, "")
  parseName ('\n' : src) = (src, "")
  parseName (chr : src) = let
    (src0, nam) = parseName src
    in (src0, chr : nam)

  parseBool :: String -> (String, Bool)
  parseBool ('\'' : src) = (src, True)
  parseBool src = (src, False)