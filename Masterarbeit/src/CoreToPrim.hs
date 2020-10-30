module CoreToPrim where

import Types
import Norm
import ElaborationCheckerN
import Output
import Control.Monad.Logic
import Elaboration

inferTrm :: Ctxt -> Term -> Int -> IO (Maybe (Elaboration VariableE))
inferTrm ctx trm 2   = return Nothing
inferTrm ctx trm dim = case observeT $ once $ elaborateN (coreToPrim ctx trm) dim of
    Nothing      -> inferTrm ctx trm (dim+1)
    res     -> return res

inferTrmV :: Ctxt -> Term -> Int -> IO (Maybe (Elaboration VariableE))
inferTrmV ctx trm dim = do
    putStrLn ""
    putStrLn "Try to infer term:"
    (putStrLn . show . coreToPrim ctx) trm
    putStrLn ""
    memCheckTrmP (coreToPrim ctx trm) dim


coreToPrim :: Ctxt -> Term -> TrmP
coreToPrim ctx = (primCoreToPrim ctx [] . eraseTerm)

-- refs will be inserted as the lambda term given by the context
-- this will most likely lead to memory overflow when testing for Omega
-- Therefore: dimension is locked at 1!
primCoreToPrim :: Ctxt -> [String] -> PrTerm -> TrmP
primCoreToPrim ctx con (PrVar var)      = 
    if var > 1 + length con 
        then TrmP $ VarP $ (return . toEnum ) (97 + var)
        else TrmP $ VarP $ con !! (0 + var)
primCoreToPrim ctx con (PrRef ref)      = 
    case ctxtLookupTermDef ctx ref of
        Nothing -> TrmP $ VarP $ "FR_" ++ ref
        Just x  -> primCoreToPrimRef ctx con (fst x)    
primCoreToPrim ctx con (PrLam bod)      = 
    let var = (return . toEnum) (97 + length con) in
    TrmP $ LamP var (primCoreToPrim ctx (var : con) bod)
primCoreToPrim ctx con (PrApp ftr str)  =
    TrmP $ AppP (primCoreToPrim ctx con ftr) (primCoreToPrim ctx con str)

primCoreToPrimRef :: Ctxt -> [String] -> PrTerm -> TrmP
primCoreToPrimRef ctx con (PrVar var)   =
    if var > 1 + length con 
        then TrmP $ VarP $ (return . toEnum ) (97 + var)
        else TrmP $ VarP $ con !! (0 + var)
primCoreToPrimRef ctx con (PrRef ref)   =
    case ctxtLookupTermDef ctx ref of
        Nothing -> TrmP $ VarP $ "FR_" ++ ref
        Just x  -> primCoreToPrimRef ctx con (fst x)
primCoreToPrimRef ctx con (PrLam bod)      = 
    let var = "R_" ++ (return . toEnum) (97 + length con) in
    TrmP $ LamP var (primCoreToPrim ctx (var : con) bod)
primCoreToPrimRef ctx con (PrApp ftr str)  =
    TrmP $ AppP (primCoreToPrimRef ctx con ftr) (primCoreToPrimRef ctx con str)
