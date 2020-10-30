module Output where

import Elaboration
import StrictType
import ElaborationCheckerN
import ElaborationCheckerMP
import ElaborationCheckerListN
import Control.Monad.Logic (observeT, LogicT, MonadLogic(once))
import Criterion.Measurement (getTime, initializeTime)
import Text.Printf (printf)

-- memCheck for Cedille Core

memCheckTrmP :: TrmP -> Int -> IO ([Elaboration VariableE])
memCheckTrmP trm 3 = do
    putStrLn "Computing farther than dimension 2 is beyond any time constraint."
    putStrLn "Done."
    return []
memCheckTrmP trm i = do
    putStrLn $ "Trying Dimension: " ++ (show i) 
    initializeTime
    start <- getTime
    chk <- showIfSixN ( ((once (elaborateN trm i)) :: [Elaboration VariableE]))
    end <- getTime
    putStrLn $ "Elapsed time for dimension " ++ show i ++ ": " ++ printf "%.4f secs (%.4f min)." (end - start) ((end - start)/60)
    putStrLn ""
    case chk of
        []  -> do 
            putStrLn "Runing algorithm for next dimension."
            memCheckTrmP trm (i+1)
        _   -> do 
            putStrLn "Done."
            return chk

-- ElaborationCheckerN

memCheckN :: String -> Int -> IO ()
memCheckN trm 3 = do
    putStrLn "MLLN: Computing farther than dimension 2 is beyond any time constraint."
    putStrLn "MLLN: Done."
memCheckN trm i = do
    putStrLn $ "MLLN: Trying Dimension: " ++ (show i) 
    initializeTime
    start <- getTime
    chk <- showIfSixN ( (( once (prsAndElabN trm i)) :: [Elaboration VariableE]) )
    end <- getTime
    putStrLn $ "MLLN: Elapsed time for dimension " ++ show i ++ ": " ++ printf "%.4f secs (%.4f min)." (end - start) ((end - start)/60)
    putStrLn ""
    case chk of
        [] -> do 
            putStrLn "MLLN: Runing algorithm for next dimension."
            memCheckN trm (i+1)
        _   -> 
            putStrLn "MLN: Done."

showIfSixN :: [Elaboration VariableE] -> IO ([Elaboration VariableE])
showIfSixN trm = 
    if null trm then do
        putStrLn "MLLN: No type for this dimension."
        putStrLn ""
        return trm
    else do
        putStrLn "MLLN: Elaborates to:"
        (putStrLn . show . head) trm
        putStrLn ""
        return trm


-- ElaborationCheckerListN

memCheckLN :: String -> Int -> IO ()
memCheckLN trm 2 = do
    putStrLn "MLN: Computing farther than dimension 2 is beyond any time constraint."
    putStrLn "MLN: Done."
memCheckLN trm i = do
    putStrLn $ "MLN: Trying Dimension: " ++ (show i) 
    initializeTime
    start <- getTime
    chk <- showIfSixLN ( observeT ((once (prsAndElabLN trm i)) :: LogicT Maybe (Elaboration VariableE)) )
    end <- getTime
    putStrLn $ "MLN: Elapsed time for dimension " ++ show i ++ ": " ++ printf "%.4f secs (%.4f min)." (end - start) ((end - start)/60)
    putStrLn ""
    case chk of
        Nothing -> do 
            putStrLn "MLN: Runing algorithm for next dimension."
            memCheckLN trm (i+1)
        _   -> 
            putStrLn "MLN: Done."


showIfSixLN :: Maybe (Elaboration VariableE) -> IO (Maybe (Elaboration VariableE))
showIfSixLN trm = 
    if null trm then do
        putStrLn "MLN: No type for this dimension."
        putStrLn ""
        return trm
    else do
        putStrLn "MLN: Elaborates to:"
        mapM_ (putStrLn . show) trm
        putStrLn ""
        return trm


memCheckMP :: String -> Int -> IO ()
memCheckMP trm 2 = do
    putStrLn "MP: Computing farther than dimension 2 is beyond any time constraint ."
    putStrLn "MP: Done."
memCheckMP trm i = do
    putStrLn $ "MP: Trying Dimension: " ++ (show i)
    initializeTime
    start <- getTime
    chk <- showIfSixMP ( (( (prsAndElabMP trm i)) :: [(Elaboration VariableE)] ) )
    end <- getTime
    putStrLn $ "MP: Elapsed time for dimension " ++ show i ++ ": " ++ printf "%.4f secs (%.4f min)." (end - start) ((end - start)/60)
    putStrLn ""
    case chk of
        [] -> do 
            putStrLn "MP: Runing algorithm for next dimension."
            memCheckMP trm (i+1)
        _   -> 
            putStrLn "MP: Done."

showIfSixMP :: [Elaboration VariableE] -> IO ([(Elaboration VariableE)])
showIfSixMP trm = 
    if null trm then do
        putStrLn "MP: No type for this dimension."
        --putStrLn "Retrying computation with \969 (empty intersection) type."
        --putStrLn ""
        --putStrLn "Elaborates with \969 to:"
        --putStrLn "WIP"
        putStrLn ""
        return trm
    else do
        putStrLn "MP: Elaborates to:"
        (putStrLn . show . head) trm
        putStrLn ""
        --putStrLn "Result Size:"
        --putStrLn $ (show . length) trm
        return trm