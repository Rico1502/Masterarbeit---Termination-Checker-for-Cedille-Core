{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module StrictTypeTransform where

import Elaboration
import StrictType
import Control.Unification.IntVar 
import Control.Unification.Types
import Control.Monad.Trans.Except
import Control.Monad.Identity
import Control.Monad.Except
import Control.Unification
import Control.Monad.Logic
import Data.List
import Data.Foldable
import Control.Monad.State.Class (MonadState(put))
import Control.Monad.State (modify)
import Debug.Trace (traceShow, trace)

-- Conversion VariableE to IntVar
varToIntVar :: VariableE -> IntVar
varToIntVar v = (IntVar . getUniqueID) v

intVarToVar :: IntVar -> VariableE
intVarToVar (IntVar v) = fromUniqueID v

-- UTerm. It is not much different compared to the normal StrictType and Intersection Type Construction,
-- but lacks the certainty that the right hand side of an Arrow is Strict.
-- Will be no problem, since the algorithm only defines Stricttypes up to this step and only has Stricttypes in constraints
data StrictType2 x
    = ITyp2 [x]
    | CTyp2 x x deriving (Eq, Functor, Foldable, Traversable, Show)

instance Unifiable StrictType2 where
    zipMatch (ITyp2 _) (CTyp2 _ _)              = Nothing
    zipMatch (CTyp2 _ _) (ITyp2 _)              = Nothing
    zipMatch (CTyp2 ls1 rs1) (CTyp2 ls2 rs2)    = Just (CTyp2 ((\l r -> Right(l,r)) ls1 ls2 ) ((\l r -> Right(l,r)) rs1 rs2 ))
    -- check for commutative, associative and idempotence is performed before converting Decoration to StrictType2
    zipMatch x@(ITyp2 ls) y@(ITyp2 rs)          = --if equivUT x y
            -- Should zip each list to the end!
                Just (ITyp2 (zipWith (\l r -> Right(l,r)) ls rs ) )
            --else Nothing

-- checks equivalence modulo commutativity, associativity and idempotence
-- equivUT :: StrictType2 x -> StrictType2 x -> Bool
-- equivUT x y = undefined

type UStrictType
    = UTerm StrictType2 IntVar

-- Conversion Functions:

-- Intersection Type (and StrictType) to UTerm
-- assumes there is no empty list, therefore no omega
--intToUST :: Intersection VariableE -> UStrictType
--intToUST (ITyp (x:[]))      = stToUST x
--intToUST (ITyp (x:y:[]))    = UTerm (ITyp2 (stToUST x) (stToUST y))
--intToUST (ITyp (x:xs))      = UTerm (ITyp2 (stToUST x) (intToUST (mkInt xs)))
--
--stToUST :: StrictType VariableE -> UStrictType
--stToUST (STyp x)    = UVar (varToIntVar x)
--stToUST (CTyp x xs) = UTerm (CTyp2 (intToUST x) (stToUST xs))
--
---- UTerm to Intersection Type (and StrictType)
--uSTToIntr :: UStrictType -> Intersection VariableE
--uSTToIntr (UTerm (ITyp2 x y))    = 
--    ITyp ((uSTToSt x) : uSTToIntHelper y)
--uSTToIntr x    =
--    ITyp [uSTToSt x]
--
--uSTToIntHelper :: UStrictType -> [StrictType VariableE]
--uSTToIntHelper y = case y of
--    UTerm (ITyp2 x2 y2)     -> 
--        uSTToSt x2 : uSTToIntHelper y2
--    otherwise               -> 
--        [uSTToSt y]
--
--uSTToSt :: UStrictType -> StrictType VariableE
--uSTToSt (UTerm (CTyp2 x y)) = 
--    CTyp (uSTToIntr x) (uSTToSt y)
--uSTToSt (UVar (IntVar x))   =
--    (STyp . fromUniqueID) x



-- Conversion Functions if ITyp2 has List instead of x x:

-- Intersection Type (and StrictType) to UTerm
intToUST :: Intersection VariableE -> UStrictType
intToUST (ITyp xs)      = UTerm $ ITyp2 (map (\xx -> stToUST xx) xs)

stToUST :: StrictType VariableE -> UStrictType
stToUST (STyp x)    = UVar (varToIntVar x)
stToUST (CTyp x xs) = UTerm (CTyp2 (intToUST x) (stToUST xs))

-- UTerm to Intersection Type (and StrictType)
uSTToIntr :: UStrictType -> Intersection VariableE
uSTToIntr (UTerm (ITyp2 x))    = 
    ITyp (map (\xx -> uSTToSt xx) x)
--uSTToIntr x    =
    --ITyp [uSTToSt x]

uSTToIntHelper :: UStrictType -> [StrictType VariableE]
uSTToIntHelper y = case y of
    UTerm (ITyp2 x)     -> 
        map (\xx -> uSTToSt xx) x
    otherwise               -> 
        [uSTToSt y]

uSTToSt :: UStrictType -> StrictType VariableE
uSTToSt (UTerm (CTyp2 x y)) = 
    CTyp (uSTToIntr x) (uSTToSt y)
uSTToSt (UVar x)   =
    (STyp . intVarToVar) x


unifyTrm :: UStrictType -> UStrictType -> IntBindingT StrictType2 Logic (Either (UFailure StrictType2 IntVar) UStrictType)
unifyTrm a b = runExceptT $ a =:= b
    
res :: UStrictType -> UStrictType -> (UStrictType, IntBindingState StrictType2)
res a b = case observe $ runIntBindingT $ unifyTrm a b of
    x -> case fst x of
        Right z -> (z, snd x)
        Left z  -> (UVar $ IntVar 0, snd x) -- 0 could be viable, too, since we do not use it anywhere (e.g. Alpha 0 or Beta 0 0)


-- take constraints, bind everything according to them
-- then apply these bindings on all terms (i.e. all Decorations)
-- (map (\constrG -> map (\const -> ((stToUST . fst) const, (stToUST . snd) const)) constrG) (groupBy (\a b -> fst a == fst b) constr))
unifyDeco :: MonadLogic m => [Decoration VariableE] -> [(StrictType VariableE, StrictType VariableE)] -> m [Decoration VariableE]
unifyDeco xs constr = (evalMonadic (map (\dec -> (intToUST . unMkDec) dec) xs) (map (\const -> ((stToUST . fst) const, (stToUST . snd) const)) constr)) >>- \res ->
    return $ map (\x -> (clearDuplicateDeco . Decoration . uSTToIntr) x ) res


-- Same results as the old function...
bindAndApplyGroupN :: [UStrictType] -> [(UStrictType, UStrictType)] -> IntBindingT StrictType2 Logic (Either (UFailure StrictType2 IntVar) [UStrictType])
bindAndApplyGroupN [] constr = mzero
bindAndApplyGroupN xs constr = do
    mapM_ (\x -> unifyTrm (fst x) (snd x)) constr
    (runExceptT . applyBindingsAll) xs

-- It seems this is way to much clutter and unification-fd does exactly, what it is supposed to do in a few tiny steps
bindAndApplyGroup :: [UStrictType] -> [(UStrictType, UStrictType)] -> IntBindingT StrictType2 Logic (Either (UFailure StrictType2 IntVar) [UStrictType])
bindAndApplyGroup [] constr = mzero
bindAndApplyGroup xs constr = do
    mapM_ (\x -> case fst x of
        UVar z -> do
            (fix (\rec a -> do
                d <- lookupVar a
                case d of
                    Nothing -> bindVar a (snd x)
                    Just y  -> do
                        ret <- y === (snd x)
                        if not ret 
                        then
                            case y of
                            UVar t  -> rec t
                            UTerm t -> do
                                bindVar a (snd x); 
                                case (snd x) of UVar tt -> bindVar tt y
                        else
                            return ()
                ) z )
        UTerm z -> case snd x of
            UVar zz -> do
                (fix (\rec a -> do
                    d <- lookupVar a
                    case d of
                        Nothing -> bindVar a (fst x)
                        Just y -> do
                            ret <- y === (fst x)
                            if not ret
                            then
                                case y of
                                UVar t -> rec t
                                UTerm t -> do 
                                    unifyTrm y (fst x); return ()
                            else
                                return ()
                    ) zz)
        ) constr
    (runExceptT . applyBindingsAll) xs

bindAndApplyGroups :: [UStrictType] -> [(UStrictType, UStrictType)] -> [UStrictType]
bindAndApplyGroups xs constr =
    case observe $ evalIntBindingT $ bindAndApplyGroupN xs constr of
            Right z -> z
            Left z  -> []--traceShow z []

evalMonadic :: MonadLogic m => [UStrictType] -> [(UStrictType, UStrictType)] -> m [UStrictType]
evalMonadic xs constr =
    case fix (\rec times resC ->
        let res = bindAndApplyGroups resC constr in 
            if (times == 1) || (null res) || (map uSTToIntr resC) == (map uSTToIntr res)
            then res
            else rec (times - 1) res) 1 xs of
                [] -> mzero
                x  -> return x 
