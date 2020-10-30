{-# LANGUAGE FlexibleInstances, DeriveFunctor, PatternSynonyms, DeriveFoldable #-}

module ElaborationCheckerMP where

-- external packages:
import Criterion.Measurement
import Control.Monad
--import Control.Monad.Logic
import Control.Monad.Identity
import Control.Monad.Except (runExceptT)
import Control.Unification.IntVar
import Control.Unification
import Control.Unification.Types
import Data.List
import Data.Foldable
import Data.Function
import Text.Show.Unicode
import Text.Printf

-- own imports:
import Core
import Elaboration
import StrictType
import StrictTypeTransform


prsAndElabMP :: MonadPlus m => String -> Int -> m (Elaboration VariableE)
prsAndElabMP cTrm dim = elaborateMP ((erasTrm . fromString) cTrm) dim

    -- Algorithm 2 -> Main algorithm!
elaborateMP :: MonadPlus m => TrmP -> Int -> m (Elaboration VariableE)
elaborateMP term dim = 
    firstElab term dim >>=
    secondElab2 dim >>=
    --fourthElab >>=
    fifthElab >>=
    sixthElab >>=
    seventhElab >>=
    return


------------------------------ STEP 1 -----------------------------------------


-- Optimized by Krüger

-- Step 1 in algorithm
firstElab :: MonadPlus m => TrmP -> Int -> m (Elaboration VariableE)
firstElab term dim = (firstElabOnce term 0 dim 1 >>= \x -> if (length . unMkInt . unMkDec . getDeco . fst) x /= 1 then mzero else
    case fst x of
        Elaboration (LamP nam bod) dec   -> if (length . unMkInt . unMkDec . getDeco) bod /= 1 then mzero else (return . fst) x
        Elaboration (AppP ftr str) dec       -> if (length . unMkInt . unMkDec . getDeco) ftr /= 1 then mzero else (return . fst) x
        _                                       -> (return . fst) x)

-- Step 1 recursive (on term). Produces a state monad to remember minimal alpha to ensurce fresh naming
firstElabOnce :: (MonadPlus m) => TrmP -> Int -> Int -> Int -> m ( (Elaboration VariableE), Int)
firstElabOnce (TrmP term) min dim mDim = case term of
    VarP x               ->  
        prodAlphaDec mDim min dim >>= 
        \dec        -> return ((Elaboration (VarP x) (fst dec)),snd dec) 
    LamP nam bod ->
        firstElabOnce bod min dim mDim >>= 
        \elabBod    -> prodAlphaDec (( length . unMkInt . unMkDec . getDeco . fst) elabBod) (snd elabBod) dim >>= 
        \dec        -> return ((Elaboration (LamP nam (fst elabBod) ) (fst dec)), snd dec)
    AppP ftr str     -> 
        firstElabOnce ftr min dim mDim >>=
        \elabFtr    -> firstElabOnce str (snd elabFtr) dim mDim >>=
        \elabStr    -> prodAlphaDec mDim (snd elabStr) ((length . unMkInt . unMkDec . getDeco . fst) elabFtr) >>=
        \dec        -> return ((Elaboration (AppP (fst elabFtr) (fst elabStr)) (fst dec)), snd dec)


------------------------------ STEP 2 & 3 -------------------------------------


-- Naive

-- -- Step 2 in algorithm.
-- -- secondElabOnce be executed for every monadic computation given by x and returns the composition of all these computations
-- secondElab :: (MonadPlus m) => m (Elaboration VariableE) -> Int -> m (Elaboration VariableE,[(StrictType VariableE, StrictType VariableE)])
-- secondElab x dim =
--     x >>= \z -> secondElabOnce z dim (sizeET z)

-- -- Step 2 recursive (on one(!) Elaboration).
-- -- Returns Tuple of: Elaboration and set of constraints C
-- secondElabOnce :: (MonadPlus m) => Elaboration VariableE -> Int -> Int -> m (Elaboration VariableE,[(StrictType VariableE, StrictType VariableE)])
-- secondElabOnce tr@(Elaboration trm decA) dim sizeM = case trm of
--     VarP z               ->
--         prodBetaDec decA dim sizeM >>=
--         \dec        -> return ((Elaboration (VarP z) (fst dec)), snd dec )
--     LamP nam bod ->
--         secondElabOnce bod dim sizeM >>= 
--         \elabBod    -> prodBetaDec decA dim sizeM >>= 
--         \dec        -> return (Elaboration (LamP nam (fst elabBod) ) (fst dec),  (snd elabBod) ++ (snd dec) )
--     AppP ftr str     -> 
--         secondElabOnce ftr dim sizeM >>=
--         \elabFtr    -> secondElabOnce str dim sizeM >>= 
--         \elabStr    -> prodBetaDec decA dim sizeM >>= 
--         \dec        -> return (Elaboration (AppP (fst elabFtr) (fst elabStr)) (fst dec), (snd elabFtr) ++ (snd elabStr) ++ (snd dec))


-- Optimized by Krüger

-- Step 2 in algorithm.
-- secondElabOnce be executed for every monadic computation given by x and returns the composition of all these computations
secondElab2 :: (MonadPlus m) => Int -> (Elaboration VariableE) -> m (Elaboration VariableE,[(StrictType VariableE, StrictType VariableE)])
secondElab2 dim x =
    secondElabOnce2 x (-1) (dim * sizeET x) False

-- Step 2 recursive (on one(!) Elaboration).
-- Returns Tuple of: Elaboration and set of constraints C
secondElabOnce2 :: (MonadPlus m) => Elaboration VariableE -> Int -> Int -> Bool -> m (Elaboration VariableE,[(StrictType VariableE, StrictType VariableE)])
secondElabOnce2 tr@(Elaboration trm decA) lMin lMax b = case trm of
    VarP z          ->
        prodBetaDec2 decA lMin lMax >>=
        \dec        -> return ((Elaboration (VarP z) (fst dec)), snd dec )
    LamP nam bod    -> 
        secondElabOnce2 bod (-1) lMax False >>=
        \elabBod    -> (case ((length . unMkInt . unMkDec) decA) of
            1           -> if b 
                then prodBetaDec2 decA (max lMin (length (collectLargestDec nam (fst elabBod))) )  (max 1 (min lMax (length (collectDec nam (fst elabBod)) ))) 
                else prodBetaDec2 decA (length (collectLargestDec nam (fst elabBod)))   (max 1 (length (collectDec nam (fst elabBod)) ))
            otherwise   -> if b
                then prodBetaDec2 decA (max lMin 0) (max 1 (min lMax (length (collectDec nam (fst elabBod)) ))) 
                else prodBetaDec2 decA 0 (max 1 (length (collectDec nam (fst elabBod)) )))
            >>=
                \dec -> return (Elaboration (LamP nam (fst elabBod) ) (fst dec), (snd elabBod) ++ (snd dec) )
    AppP ftr str    -> 
        secondElabOnce2 str (-1) lMax False >>=
        \elabStr    -> let lDecStr = ((length . unMkInt . unMkDec . getDeco . fst) elabStr) in (case ((length . unMkInt . unMkDec . getDeco) ftr) of
            1           -> case ftr of 
                Elaboration (LamP _ _) _ -> secondElabOnce2 ftr lDecStr lDecStr True
                otheriwse                   -> secondElabOnce2 ftr lDecStr lDecStr False
            otherwise   -> case ftr of
                Elaboration (LamP _ _) _ -> secondElabOnce2 ftr 0 lDecStr True
                otherwise                   -> secondElabOnce2 ftr 0 lDecStr False)
            >>=
        \elabFtr    -> prodBetaDec2 decA lMin lMax >>=
        \dec        -> return (Elaboration (AppP (fst elabFtr) (fst elabStr)) (fst dec), (snd elabFtr) ++ (snd elabStr) ++ (snd dec))


------------------------------ STEP 4 -----------------------------------------


-- -- Choose EVERY possibility intelligent
-- fourthElab :: MonadPlus m => (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)]) -> m (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)])
-- fourthElab x = fourthElabOnce x

-- fourthElabOnce :: MonadPlus m => (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)]) -> m (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)])
-- fourthElabOnce this@(elab@(Elaboration trm deco), constr) = case trm of
--     VarP x       -> 
--         return this
--     LamP nam bod -> 
--         fourthElabOnce (bod, constr) >>=
--         \elabBod    -> return (Elaboration (LamP nam (fst elabBod)) deco , snd elabBod)
--     AppP ftr str -> 
--         fourthElabOnce (ftr, []) >>=
--         \constrFtr  -> fourthElabOnce (str, []) >>=
--         \constrStr  -> 
--         return (elab, foldr (\x -> \state -> case x of 
--         CTyp xs s   -> ((head . unMkInt . unMkDec) deco,s) : (zipBoth ((unMkInt . unMkDec . getDeco) str) ((unMkInt) xs) ) ++ state
--         otherwise   -> state) (constr ++ (snd constrFtr) ++ (snd constrStr)) ((unMkInt . unMkDec . getDeco) ftr))


------------------------------ STEP 5 -----------------------------------------


fifthElab :: MonadPlus m => (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)]) -> m (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)])
fifthElab x = fifthElabOnce x >>= \zz -> return (fst zz, ( (filter (\d -> (fst d) /= (snd d)))) (snd zz))

-- In naive solution, this is the first time we want mzero to be returned!
fifthElabOnce :: MonadPlus m => (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)]) -> m (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)])
fifthElabOnce this@(elab@(Elaboration trm deco), constr) = case (length . unMkInt . unMkDec) deco of
    1                               -> case trm of
        VarP x       -> return this
        LamP nam bod -> if (length . unMkInt . unMkDec . getDeco) bod /= 1 then mzero else case (head . unMkInt . unMkDec) deco of
            CTyp xxs s  -> let constr2 = ((head . unMkInt . unMkDec . getDeco) bod,s) : constr in
                case collectDec nam bod of
                    []  ->
                        fifthElabOnce (bod, constr2) >>=
                        \elabBod    -> return (elab, snd elabBod)
                    x   -> buildWholeMap x (unMkInt xxs) >>=
                        \mapAB      -> fifthElabOnce (bod, mapAB ++ constr2) >>=
                        \elabBod    -> return (elab, snd elabBod)
            otherwise       -> mzero
        AppP ftr str -> if (length . unMkInt . unMkDec . getDeco) ftr /= 1 then mzero else case (head . unMkInt . unMkDec . getDeco) ftr of
            CTyp xxs s  -> let constr2 = ((head . unMkInt . unMkDec) deco,s) : constr in
                buildWholeMap ((unMkInt . unMkDec . getDeco) str) (unMkInt xxs) >>=
                \mapAB      -> fifthElabOnce (ftr, mapAB ++ constr2) >>=
                \elabFtr    -> fifthElabOnce (str, snd elabFtr) >>=
                \elabStr    -> return (elab, snd elabStr)
            otherwise   -> mzero
    otherwise  -> decomposeDecoration elab >>= \decompCand -> return $ (elab, (map head . group . sort) $ foldr' (\el st -> fifthElabOnce (el,constr) >>= \sol -> snd sol ++ st ) constr decompCand)


------------------------------ STEP 6 -----------------------------------------


-- Compute Unifier
sixthElab :: MonadPlus m => (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)]) -> m (Elaboration VariableE)
sixthElab e = sixthElabOnce e

sixthElabOnce :: MonadPlus m => (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)]) -> m (Elaboration VariableE)
sixthElabOnce e = computeUnifiers e >>= \res -> 
    checkElaboration res


------------------------------ STEP 7 -----------------------------------------


-- Renaming
-- monadGen may be suitable
seventhElab :: MonadPlus m => (Elaboration VariableE) -> m (Elaboration VariableE)
seventhElab = return 


-------------------------- HELPER FUNCTIONS -----------------------------------

-------------------------- HELPER STEP 1 --------------------------------------


-- creates elaborations with dimensions d to dim, named by  alpha_minV to alpha_(minV + dim - d) with d <= dim!
prodAlphaDec :: MonadPlus m => Int -> Int -> Int -> m ( (Decoration VariableE), Int)
prodAlphaDec d minV dim =
     (fmap (\y -> (Decoration $ ITyp $ fmap (\x -> STyp $ Alpha (x+minV)) ( [1..y]),(minV+y)) ) (foldToLogic [d..dim]))


-------------------------- HELPER STEP 2 & 3 ----------------------------------


-- Naive: get d and |M| as explained in algorithm to produce Betas

-- produces Beta functions (beta \cap beta \cap beta -> beta) from given Alphas.
prodBetaDec :: MonadPlus m => Decoration VariableE -> Int -> Int -> m (Decoration VariableE,[(StrictType VariableE, StrictType VariableE)])
prodBetaDec dec dim sizeM =
    foldr (\alph -> \state -> state >>= \beta -> fmap (\z -> beta ++ [z]) (prodBetaStT alph dim sizeM) ) (return []) ((unMkInt . unMkDec) dec) >>=
    \betas -> return ( (Decoration $ ITyp $ (map (\z -> snd z) betas)) ,betas)
        

-- produces a Beta function (beta \cap beta \cap beta -> beta) for a given Alpha and all possible l's.
prodBetaStT :: MonadPlus m => StrictType VariableE -> Int -> Int -> m (StrictType VariableE , StrictType VariableE)
prodBetaStT dec@(STyp (Alpha n)) dim sizeM =
    mplus 
        (mplus (return (dec, dec)) (return (dec, (STyp $ Beta 0 n) )))
        (fmap (\l -> (dec, (CTyp (ITyp $ (fmap (\x -> STyp $ Beta x n) (foldToLogic [1..l])) ) (STyp $ Beta 0 n)) ) ) (foldToLogic [1..(dim*sizeM)]))
prodBetaStT _ _ _ = mzero

-- Optimized: Gets a min and max for l to produce Betas

-- produces Beta functions (beta \cap beta \cap beta -> beta) from given Alphas.
prodBetaDec2 :: MonadPlus m => Decoration VariableE -> Int -> Int -> m (Decoration VariableE,[(StrictType VariableE, StrictType VariableE)])
prodBetaDec2 dec min max = if min > max then mzero else
    foldr (\alph state -> state >>= \beta -> fmap (\z -> z : beta ) (prodBetaStT2 alph min max) ) (return []) ((unMkInt . unMkDec) dec) >>=
    \betas -> return ( (Decoration $ ITyp $ (map (\z -> snd z) betas)) ,betas)

-- produces a Beta function (beta \cap beta \cap beta -> beta) for a given Alpha and all possible l's.
prodBetaStT2 :: MonadPlus m => StrictType VariableE -> Int -> Int -> m (StrictType VariableE , StrictType VariableE)
prodBetaStT2 dec@(STyp (Alpha n)) (-1) _    = return (dec, dec)
prodBetaStT2 dec@(STyp (Alpha n)) 0 0       = return (dec, (STyp $ Beta 0 n) )
prodBetaStT2 dec@(STyp (Alpha n)) 0 max     = mplus
    (return (dec, (STyp $ Beta 0 n) ))
    (fmap (\l -> (dec, (CTyp (ITyp $ (fmap (\x -> STyp $ Beta x n) (foldToLogic [1..l])) ) (STyp $ Beta 0 n)) ) ) (foldToLogic [1..max]))
prodBetaStT2 dec@(STyp (Alpha n)) min max   =
        (fmap (\l -> (dec, (CTyp (ITyp $ (fmap (\x -> STyp $ Beta x n) (foldToLogic [1..l])) ) (STyp $ Beta 0 n)) ) ) (foldToLogic [min..max]))



-------------------------- HELPER STEP 5 --------------------------------------


-- Computes "packages" of decompositions.
decomposeDecoration :: MonadPlus m => Elaboration VariableE -> m [Elaboration VariableE]
decomposeDecoration (Elaboration trm deco) = let lDeco = (unMkInt . unMkDec) deco in case trm of
    VarP nam        -> return $ map (\el -> Elaboration (VarP nam) (Decoration $ ITyp [el]) ) lDeco
    LamP nam bod    -> do
        decomposedBod <- decomposeDecorationRec bod (length lDeco)
        guard $ all (\x -> (length . unMkInt . unMkDec . getDeco) x == 1) decomposedBod
        guard $ all (\(decoEl, decompBod) -> case decoEl of CTyp xs s -> (length (collectLargestDec nam decompBod)) <= length xs && length xs <= length (collectDec nam decompBod); _ -> False ) (zip lDeco decomposedBod)
        return $ map (\(dDeco, dBod) -> Elaboration (LamP nam dBod) (Decoration $ ITyp [dDeco])) (zip lDeco decomposedBod)
    AppP ftr str    -> do
        decomposedFtr <- decomposeDecorationRec ftr (length lDeco)
        decomposedStr <- decomposeDecorationRec str (length lDeco)
        guard $ all (\x -> (length . unMkInt . unMkDec . getDeco) x == 1) decomposedFtr
        guard $ all (\(decompFtr, decompStr) -> 
           case (head . unMkInt . unMkDec . getDeco) decompFtr of 
               CTyp xs s -> length xs == (length . unMkInt . unMkDec . getDeco) decompStr
               _ -> False) 
               (zip decomposedFtr decomposedStr)
        return $ map (\(dDeco, dFtr, dStr) -> Elaboration (AppP dFtr dStr) (Decoration $ ITyp [dDeco]) ) (zip3 lDeco decomposedFtr decomposedStr)

decomposeDecorationRec :: MonadPlus m => Elaboration VariableE -> Int -> m [Elaboration VariableE]
decomposeDecorationRec (Elaboration trm deco) ctP = do
    case trm of
        VarP nam             -> foldToLogic $ map (\partCand -> map (\partCandAlpha -> Elaboration (VarP nam) (Decoration $ ITyp partCandAlpha) ) partCand ) $ filter (\el -> (map head . group . sort) (concatMap id el) == (unMkInt . unMkDec) deco) $ foldl' (\st el -> concatMap (\elL -> map (\elR -> elR : elL) el ) st ) [[]] $ replicate ctP (filter ((/=) []) ((subsequences . unMkInt . unMkDec) deco))   
        
        LamP nam bod -> do
            combDec <- foldToLogic $ filter (\el -> (map head . group . sort) (concatMap id el) == (unMkInt . unMkDec) deco) $ foldl' (\st el -> concatMap (\elL -> map (\elR -> elR : elL) el ) st ) [[]] $ replicate ctP (filter ((/=) []) ((subsequences . unMkInt . unMkDec) deco))
            decomposedBod <- decomposeDecorationRec bod ctP
            guard $ all (\(decoEl, decompBod) -> 
                (length . unMkInt . unMkDec . getDeco) decompBod <= length decoEl &&
                all (\decTyp -> 
                    (case decTyp of 
                        CTyp xs s -> 
                            (if length decoEl == 1 
                                then length (collectLargestDec nam decompBod)
                                else 0) <= length xs &&
                            ((length . unMkInt) xs <= length (collectDec nam decompBod))
                        _ -> False)                     
                    ) decoEl &&
                length (collectLargestDec nam decompBod) <= sum (map (\el -> case el of CTyp xs s -> (length . unMkInt) xs; _ -> 0) decoEl) ) (zip combDec decomposedBod)
            return $ map (\el -> Elaboration (LamP nam (snd el)) (Decoration $ ITyp (fst el))) (zip combDec decomposedBod) 
        
        AppP ftr str     -> do
            combDec <- foldToLogic $ filter (\el -> (map head . group . sort) (concatMap id el) == (unMkInt . unMkDec) deco) $ foldl' (\st el -> concatMap (\elL -> map (\elR -> elR : elL) el ) st ) [[]] $ replicate ctP (filter ((/=) []) ((subsequences . unMkInt . unMkDec) deco))
            decomposedFtr <- decomposeDecorationRec ftr ctP
            guard $ all (\(combDecEl, decompFtr) -> length combDecEl <= (length . unMkInt . unMkDec . getDeco) decompFtr) (zip combDec decomposedFtr)
            decomposedStr <- decomposeDecorationRec str ctP
            guard $ all (\(decompFtr,decompStr) -> all (\decompFtrDecEl -> case decompFtrDecEl of
                CTyp xs s   -> 
                    (if ((length . unMkInt . unMkDec . getDeco) decompFtr) == 1 
                        then (length . unMkInt . unMkDec . getDeco) decompStr 
                        else 0) <= (length . unMkInt) xs &&
                    (length . unMkInt) xs <= (length . unMkInt . unMkDec . getDeco) decompStr 
                _           -> False) ((unMkInt . unMkDec . getDeco) decompFtr) &&
                (length . unMkInt . unMkDec . getDeco) str <= sum (map (\el -> case el of CTyp xs s -> (length . unMkInt) xs; _ -> 0) ((unMkInt . unMkDec . getDeco) ftr)) ) (zip decomposedFtr decomposedStr)
            return $ map (\(dDeco,dFtr,dStr) -> Elaboration (AppP dFtr dStr) (Decoration $ ITyp dDeco) ) (zip3 combDec decomposedFtr decomposedStr)


-- Map on both permutations. Ensure that we got BetAlpMap for every AlpBetMap.
-- Clear duplicates (inside one map and between any map)
-- Adjust, that you are not getting 2^xs maps!
buildWholeMap :: (MonadPlus m, Eq x, Ord x) => [x] -> [x] -> m [(x,x)]
buildWholeMap xs ys =
    buildAlpBetMap xs ys 
    >>= \abE -> case (\\) ys (foldr (\el st -> snd el : st) [] abE) of
        []      -> return abE
        ret     -> buildBetAlpMap xs ret >>= \baE -> return $ abE ++ baE

-- builds all possible constraints for Step 5.4.2 and Step 5.5.2
buildAlpBetMap :: (MonadPlus m, Eq x, Ord x) => [x] -> [x] -> m [(x, x)]
buildAlpBetMap xs ys =
    foldToLogic (foldr' (\bet -> \state -> case bet of 
        []  -> mzero
        _   -> (zipLeft xs bet) : state  ) mzero ( (filter (\yy -> length yy <= length xs) . powerset) ys >>= permutations))

-- Find alpha for each non taken beta!
-- builds all possible constraints for Step 5.4.3 and Step 5.5.3
buildBetAlpMap :: (MonadPlus m, Eq x, Ord x) => [x] -> [x] -> m [(x, x)]
buildBetAlpMap xs ys =
    foldToLogic (foldr' (\bet -> \state -> case bet of 
        []  -> mzero
        _   -> (zipRight bet ys) : state ) mzero ((filter (\xx -> length xx <= length ys) . powerset) xs >>= permutations))

-- -- Map on both permutations. Ensure that we got BetAlpMap for every AlpBetMap.
-- -- Clear duplicates (inside one map and between any map)
-- -- Adjust, that you are not getting 2^xs maps!
-- buildWholeMapMP :: (MonadPlus m, Eq x, Ord x) => [x] -> [x] -> m [(x,x)]
-- buildWholeMapMP xs ys =
--     buildAlpBetMapMP xs ys 
--     >>= \abE -> case (\\) ys (foldr (\el st -> snd el : st) [] abE) of
--         []      -> return abE
--         ret     -> buildBetAlpMapMP xs ret >>= \baE -> return $ abE ++ baE
--     -- let
--         --alpBetSet = buildAlpBetMap xs ys in
--         --foldr (\abS state -> buildBetAlpMap xs (filter (\el -> notElem el ys) $ foldr (\el st -> snd el : st) [] abS ) >>= \baS -> mplus state (return $ baS ++ abS) ) (foldToLogic alpBetSet) alpBetSet

-- -- builds all possible constraints for Step 5.4.2 and Step 5.5.2
-- buildAlpBetMapMP :: (MonadPlus m, Eq x, Ord x) => [x] -> [x] -> m [(x, x)]
-- buildAlpBetMapMP xs ys =
--     (foldr' (\bet -> \state -> case bet of 
--         []  -> mzero
--         _   -> mplus (return (zipLeft xs bet)) state  ) mzero ( (filter (\yy -> length yy <= length xs) . powerset) ys >>= permutations))

-- Find alpha for each non taken beta!
-- builds all possible constraints for Step 5.4.3 and Step 5.5.3
buildBetAlpMapMP :: (MonadPlus m, Eq x, Ord x) => [x] -> [x] -> m [(x, x)]
buildBetAlpMapMP xs ys =
    (foldr' (\bet -> \state -> case bet of 
        []  -> mzero
        _   -> mplus (return $ zipRight bet ys) state ) mzero ((filter (\xx -> length xx <= length ys) . powerset) xs >>= permutations))

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs


-------------------------- HELPER STEP 6 --------------------------------------


-- gets all Decorations of a given term
getDecorations :: Elaboration VariableE -> [Decoration VariableE]
getDecorations (Elaboration (VarP x) deco)          = [deco]
getDecorations (Elaboration (LamP nam bod) deco)    = deco : getDecorations bod
getDecorations (Elaboration (AppP ftr str) deco)    = deco : (getDecorations ftr) ++ (getDecorations str)

-- changes all Decorations of a given term to the refered list of decorations
putDecorations :: Elaboration VariableE -> [Decoration VariableE] -> Elaboration VariableE
putDecorations (Elaboration (VarP x) deco) decL         =
    (Elaboration (VarP x) (head decL))
putDecorations (Elaboration (LamP nam bod) deco) decL   =
    (Elaboration (LamP nam (putDecorations bod (tail decL))) (head decL))
putDecorations (Elaboration (AppP ftr str) deco) decL   =
    let lftr = countDec ftr in
    (Elaboration (AppP (putDecorations ftr (tail decL)) (putDecorations str ((drop lftr . tail) decL)) ) (head decL) )


computeUnifiers :: MonadPlus m => (Elaboration VariableE, [(StrictType VariableE, StrictType VariableE)]) -> m (Elaboration VariableE)
computeUnifiers (elab, constr) = (unifyDecoMP (getDecorations elab) constr) >>= return . putDecorations elab


-- Too further check results:
--  - check, if Abstraction has all required Types (i.e. e.g. if \omega has the type \alpha \cap \alpha -> \beta), esp. if it has all the needed Intersection Types
--  - check, if it possible to apply Application, i.e. if the right term has at least every type from the left term
--  -> can (and hopefully will) restrict the solutions in such sense, that wrong answers won't be in result space anymore!
--      - e.g. (\x -> x x) y with dim 1. Here the Lambda case does not have all the Intersection Types needed
--      - in this solution !!beta -> alpha is equal to beta!!, because \beta_1_4 = \beta_1_1 and \beta_1_1 -> \beta_0_1 = \beta_1_4, which is partly correct,
--          since \beta_1_1 -> \beta_0_1 is one of the types for x!

--

checkElaboration :: MonadPlus m => Elaboration VariableE -> m (Elaboration VariableE)
checkElaboration this@(Elaboration (VarP nam) deco) = return this
checkElaboration (Elaboration (LamP nam bod) deco)  = if case collectDec nam bod of
    []  -> 
        any (\decEl -> case decEl of
            CTyp xs s   -> any ((==) s) ((unMkInt . unMkDec . getDeco) bod)
            STyp s      -> False) ((unMkInt . unMkDec) deco)
    _   ->
        all (\varTyp -> any (\decEl -> case decEl of
            CTyp xs s   -> elem varTyp (unMkInt xs) && any ((==) s) ((unMkInt . unMkDec . getDeco) bod)
            STyp s      -> False ) ((unMkInt . unMkDec) deco) ) (collectDec nam bod)
        then
            checkElaboration bod >>= 
            \bodRes -> return $ Elaboration (LamP nam bodRes ) deco
        else 
            mzero
checkElaboration (Elaboration (AppP ftr str) deco)  = 
    if all (\ftrTyp -> case ftrTyp of
        CTyp xs s  -> null ((\\) (unMkInt xs) ((unMkInt . unMkDec . getDeco) str)) && any ((==) s) ((unMkInt . unMkDec) deco)
        STyp s     -> False) ((unMkInt . unMkDec . getDeco) ftr)
    then
        checkElaboration ftr >>= 
        \ftrRes -> checkElaboration str >>=
        \strRes -> return $ Elaboration (AppP ftrRes strRes) deco
    else
        mzero
-- checkElaboration (Elaboration (App era ftr str) deco)       = 
    -- if (length . unMkInt . unMkDec) deco == 1 then
        -- if any (\ftrTyp -> case ftrTyp of
            -- CTyp xs s  -> if (head . unMkInt . unMkDec) deco == s
                -- then
                    -- all (\strTyp -> elem strTyp ((unMkInt . unMkDec . getDeco) str) ) (unMkInt xs)
                -- else
                    -- False
            -- STyp s     -> False) ((unMkInt . unMkDec . getDeco) ftr)
        -- then
            -- checkElaboration ftr >>= 
            -- \ftrRes -> checkElaboration str >>=
            -- \strRes -> return $ Elaboration (App era ftrRes strRes) deco
        -- else
            -- mzero
    -- else
        -- mzero

-------------------------- HELPER undef ---------------------------------------

-- Collects all Decorations for given free VariableE in a Term and returns them in a list
-- This is T_x(P) = {A_1,...,A_k}
collectDec :: String -> Elaboration x -> [StrictType x]
collectDec s (Elaboration (VarP x) xs)          = if s == x then (unMkInt . unMkDec) xs else []
collectDec s (Elaboration (LamP nam bod) xs)    = if s == nam then [] else collectDec s bod
collectDec s (Elaboration (AppP ftr str) xs)    = collectDec s ftr ++ collectDec s str

-- Collects largest Decorations for given free VariableE in a Term and returns it
collectLargestDec :: String -> Elaboration x -> [StrictType x]
collectLargestDec s (Elaboration (VarP x) xs )      = if s == x then (unMkInt.unMkDec) xs else []
collectLargestDec s (Elaboration (LamP nam bod) xs) = if s == nam then [] else collectLargestDec s bod
collectLargestDec s (Elaboration (AppP ftr str) xs) = let x = collectLargestDec s ftr; y = collectLargestDec s str in
    if length x >= length y then x else y

foldToLogic :: (Foldable f, MonadPlus m) => f a -> m a
foldToLogic = foldr' (flip mplus.return) mzero

zipLeft :: [a] -> [b] -> [(a,b)]
zipLeft [] _            = []
zipLeft _ []            = []
zipLeft (a:[]) (b:[])   = (a,b) : []
zipLeft (a:[]) (b:bs)   = (a,b) : []
zipLeft (a:as) (b:[])   = (a,b) : zipLeft as (b:[])
zipLeft (a:as) (b:bs)   = (a,b) : zipLeft as bs

zipRight :: [a] -> [b] -> [(a,b)]
zipRight [] _            = []
zipRight _ []            = []
zipRight (a:[]) (b:[])   = (a,b) : []
zipRight (a:[]) (b:bs)   = (a,b) : zipRight (a:[]) bs
zipRight (a:as) (b:[])   = (a,b) : []
zipRight (a:as) (b:bs)   = (a,b) : zipRight as bs