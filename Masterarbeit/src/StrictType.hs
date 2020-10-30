{-# LANGUAGE FlexibleInstances, DeriveFunctor, PatternSynonyms, DeriveFoldable, DeriveTraversable #-}

module StrictType where

import Data.List
import Data.Foldable
import qualified Text.Show.Unicode

-- Strict Intersection Types.
-- Empty Intersection Type is possible, but not wanted (at the moment)
newtype Intersection x
    = ITyp [StrictType x] deriving (Functor, Foldable, Traversable, Ord)


unMkInt :: Intersection x -> [StrictType x]
unMkInt (ITyp x) = x

instance (Show a) => Show (Intersection a) where
    showsPrec d (ITyp []) = showString " \969"
    showsPrec d (ITyp (x:[])) = showParen (d > 5) $ showsPrec d x
    showsPrec d (ITyp xs) = showParen (d > intrPrec) $  
        showString "[" . foldr (\el st -> st . showString " , " . showsPrec intrPrec el) (showsPrec intrPrec (head xs)) (tail xs) . showString "]"
        -- (case xs of
            -- [] -> showsPrec (d+1) x . showString "]"
            -- this shows the intersect symbol. Is not correct in comparison to paper
            -- _  -> showsPrec (d+1) x . showString " \8745 " . showsPrec intrPrec (ITyp xs)) 
            -- _ -> showsPrec (d+1) x . showString " , " . showsPrec intrPrec (ITyp xs))
        where intrPrec = 5

instance (Eq a, Ord a) => Eq (Intersection a) where
    ITyp [] == ITyp []= True -- Three cases for omega
    ITyp [] == ITyp y = True
    ITyp x  == ITyp []= True
    -- Checks, if every type in x is in y.
    -- Therefore considers associativity, commutativity and idempotence
    ITyp x  == ITyp y = (map head . group . sort) y == (map head . group . sort) x
        --all (flip elem y) x

-- Strict Types
data StrictType x
    = STyp x
    | CTyp (Intersection x) (StrictType x) deriving (Functor, Foldable, Traversable, Ord)

instance (Show a) => Show (StrictType a) where
    showsPrec d (STyp x) =
        showsPrec d x
    showsPrec d (CTyp x y) = showParen (d > typFuncPrec) $ 
        showsPrec typFuncPrec x . 
        showString " \8594 " . 
        showsPrec typFuncPrec y 
        where typFuncPrec = 10

instance (Eq a, Ord a) => Eq (StrictType a) where
    STyp x     == STyp y     = x == y
    CTyp x1 x2 == CTyp y1 y2 = (x1 == y1) && (x2 == y2)
    CTyp _ _   == STyp _     = False
    STyp _     == CTyp _ _   = False

clearDuplicateInt :: Ord x => Intersection x -> Intersection x
clearDuplicateInt (ITyp st) = (ITyp . map clearDuplicateStT . map head . group . sort) st

clearDuplicateStT :: Ord x => StrictType x -> StrictType x
clearDuplicateStT (CTyp its st) = CTyp (clearDuplicateInt its) (clearDuplicateStT st)
clearDuplicateStT (STyp v)      = STyp v