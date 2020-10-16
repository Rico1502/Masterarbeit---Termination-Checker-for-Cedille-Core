{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
module Intersection where

import Control.Unification
import Elaboration
import Control.Monad.Logic
import Control.Monad.Except
import Control.Monad.List
import Control.Monad.Trans.Maybe
import Control.Unification.IntVar
import Data.IntMap.Strict
import Control.Unification.Types
import Control.Monad.Identity (Identity)

data IT 
    = Var Int
    | Arrow IT IT
    | Intersection IT IT

data IT2 x
    = Var2 Int
    | Arrow2 x x
    | Intersection2 x x

data Fix f
    = MkFix (f (Fix f))

type IT3
    = Fix IT2

test :: IT3
test = MkFix (Arrow2 (MkFix (Var2 42)) (MkFix (Var2 42)) )

data IT4 x
    = Arrow4 x x
    | Intersection4 x x deriving (Eq, Functor, Foldable, Traversable, Show)

instance Unifiable IT4 where
    zipMatch (Arrow4 _ _) (Intersection4 _ _)                   = Nothing
    zipMatch (Intersection4 _ _) (Arrow4 _ _)                   = Nothing
    zipMatch (Arrow4 ls1 rs1) (Arrow4 ls2 rs2)                  = Just( Arrow4 ((\l r -> Right(l,r)) ls1 ls2) ((\l r -> Right(l,r)) rs1 rs2))
    zipMatch (Intersection4 ls1 rs1) (Intersection4 ls2 rs2)    = Just( Intersection4 ((\l r -> Right(l,r)) ls1 ls2) ((\l r -> Right(l,r)) rs1 rs2 ))
 
type IT5
    = UTerm IT4 IntVar

int2 :: IT5
int2 = UTerm (Arrow4 (UVar (IntVar 42)) (UVar (IntVar 42)))

int3 :: IT5
int3 = UTerm (Arrow4 (UVar (IntVar 22)) (UVar (IntVar 42)))

int4 :: IT5
int4 = UTerm (Arrow4 (UVar (IntVar 22)) (UVar (IntVar 22)))

int5 :: IT5
int5 = UTerm (Arrow4 (UVar (IntVar 42)) (UVar (IntVar 22)))

foo :: BindingMonad t v m => UTerm t v -> UTerm t v -> m (IntMap Int)
foo a b = (a =~= b) >>= \x -> case x of Nothing -> return empty; Just y -> return y

foo2 :: (Monad m, BindingMonad t v (IntBindingT t m)) => UTerm t v -> UTerm t v -> m (IntMap Int)
foo2 a b = runIntBindingT (foo a b) >>= \x -> (return . fst) x

--type Blubb f x = ExceptT String (f x)

bar ::  IT5 -> IT5 -> ExceptT (UFailure IT4 IntVar) (IntBindingT IT4 Identity) IT5 
bar a b = do 
     uni <- a =:= b;
     return uni

bar2 :: IT5 -> IT5 -> Identity (Either (UFailure IT4 IntVar) IT5, IntBindingState IT4 )
bar2 a b = (runIntBindingT . runExceptT) (bar a b) -- >>= \x -> (return . fst) x
    
