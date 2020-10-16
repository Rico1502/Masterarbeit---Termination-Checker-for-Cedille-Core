import System.Environment
import ElaborationChecker
import Elaboration
import StrictType
import Control.Monad.Logic
import Criterion.Measurement
import Text.Printf (printf)
import Core
import qualified Text.Show.Unicode

main :: IO ()
main = do 
    
    args <- System.Environment.getArgs

    case args of
        [] -> 
            do putStrLn "Insert Cedille Term as String and dimension as Integer!"

        trm : dim : _ -> do

            --trm <- readFile file

            -- Right now just shows one solution, since we are just interested in a termination checker!
            putStrLn ""
            putStrLn "Initialize Elaboration Checker for Term:"
            (putStrLn . show . erasTrm . fromString) trm
            putStrLn ""
            initializeTime
            start <- getTime
            chk <- memCheck trm (read dim)
            --showIfSix ((prsAndElab2 trm (read dim)) :: [Elaboration VariableE])
            --showIf ( (prsAndElab trm (read dim)) :: [(Elaboration VariableE,[(StrictType VariableE, StrictType VariableE)])])
            end <- getTime
            --putStrLn ""
            putStrLn "Elapsed total time:"
            putStrLn $ printf "%.4f secs (%.4f min)." (end - start) ((end - start)/60)

        _ -> do putStrLn "Insert Cedille Term as String and dimension as Integer!"