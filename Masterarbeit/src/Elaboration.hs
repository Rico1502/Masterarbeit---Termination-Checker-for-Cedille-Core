{-# LANGUAGE FlexibleInstances, DeriveFunctor, PatternSynonyms, DeriveFoldable, DeriveTraversable #-}

module Elaboration where

import Core
import qualified Text.Show.Unicode
import StrictType
import Data.List

data VariableE
    = Alpha Int
    | Beta Int Int deriving (Eq, Ord)

getUniqueID :: VariableE -> Int
getUniqueID (Beta x y) = (div ((x + y)* (x + y + 1)) 2)  + y
getUniqueID (Alpha x)  = -x

fromUniqueID :: Int -> VariableE
fromUniqueID z | z <= 0  = Alpha (-z)
fromUniqueID z          = let 
    wC  = toInteger (8 * z + 1)
    wSQ = (sqrt . fromInteger) wC - 1.0
    w   = floor (wSQ / 2)
    t   = div (w^2 + w) 2
    y   = z - t
    x   = w - y in
    Beta x y

instance Show VariableE where
    showsPrec d (Alpha x)  = showString "\945" . showString "_" . showsPrec d x
    showsPrec d (Beta x y) = showString "\946" . showString "_" . showsPrec d x . showString "'" . showsPrec d y

data SplTrm x
    = VarP String
    | LamP String x
    | AppP x x deriving Eq

instance Show x => Show (SplTrm x) where
    showsPrec d (VarP nam)       = 
        showString nam
    showsPrec d (LamP nam bod)   = 
        showString "(" . 
        showString "\955" . 
        showString nam . 
        showString ". " . 
        showsPrec d bod . 
        showString ")"
    showsPrec d (AppP ftr str)   =
        showString "(" .
        showsPrec d ftr . showString " " .
        showsPrec d str .
        showString ")"

newtype TrmP
    = TrmP (SplTrm TrmP) deriving Eq

instance Show TrmP where
    showsPrec d (TrmP trm) =
        showsPrec d trm

newtype Decoration x =
    Decoration (Intersection x)

unMkDec :: Decoration x -> Intersection x
unMkDec (Decoration i) = i

instance (Show a) => Show (Decoration a) where
    showsPrec d (Decoration x) = showString "<" . showsPrec d x .showString ">"

data Elaboration x =
    Elaboration (SplTrm (Elaboration x)) (Decoration x)

instance Show x => Show (Elaboration x) where
    showsPrec d (Elaboration trm sTyp) =
        showsPrec d trm . showsPrec d sTyp
    -- showsPrec d (Elaboration (LamP nam bod) sTyp) =
        -- showString "(" .
        -- showString "\955" .
        -- showString nam .
        -- showString ". " .
        -- showsPrec d bod .
        -- showString ")" .
        -- showsPrec d sTyp
    -- showsPrec d (Elaboration (AppP fun arg) sTyp) =
        -- showString "(" .
        -- showsPrec d fun . showString " " .
        -- showsPrec d arg .
        -- showString ")" .
        -- showsPrec d sTyp

getDeco :: Elaboration x -> Decoration x
getDeco (Elaboration _ d) = d

    

-- Computes the Size of an Term for a given Elaboration
sizeET :: Elaboration x -> Int
sizeET (Elaboration trm styp) = case trm of
    VarP _               -> 0
    LamP nam bod -> 1 + sizeET bod 
    AppP fun arg     -> 1 + sizeET fun + sizeET arg

-- computes an erased Cedille Term
-- only needed for hand written tests of old Cedille Core environment: INCOMPLETE!
erasTrm :: TermP -> TrmP
erasTrm (Term trm) = case trm of
    Var nam             -> TrmP $ VarP nam 
    Lam era nam typ bod -> if era 
        then erasTrm( bod (Term (Var nam)) )
        else TrmP $ LamP nam $ erasTrm (bod (Term (Var nam)))
    App era fun arg     -> if era
        then erasTrm fun
        else TrmP $ AppP (erasTrm fun) (erasTrm arg)
    Let nam typ bod     -> TrmP $ AppP (TrmP (LamP nam $ erasTrm (bod (Term (Var nam))) ) ) (erasTrm typ)
    
-- counts Decorations of given Term
countDec :: Elaboration VariableE -> Int
countDec (Elaboration (VarP x) dec)         = 1
countDec (Elaboration (LamP nam bod) dec)   = 1 + countDec bod
countDec (Elaboration (AppP ftr str) dec)   = 1 + countDec ftr + countDec str

clearDuplicateDeco :: Ord x => Decoration x -> Decoration x
clearDuplicateDeco deco = (Decoration . clearDuplicateInt . unMkDec) deco
