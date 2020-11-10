import System.Environment
import Output
import Elaboration
import StrictType
import Control.Monad.Logic
import Criterion.Measurement
import Text.Printf (printf)
import Core
import qualified Text.Show.Unicode
import Control.Concurrent.ParallelIO (parallel_)

main :: IO ()
main = do 
    
    args <- System.Environment.getArgs

    case args of
        [] -> 
            do putStrLn "Insert Cedille Term as String and dimension as Integer!"

        trm : dim : _ -> do

            putStrLn ""
            putStrLn "Initialize Elaboration Checker for Term:"
            (putStrLn . show . erasTrm . fromString) trm
            putStrLn ""
            initializeTime
            start <- getTime
            (memCheckLN trm (read dim))
            end <- getTime
            putStrLn "Elapsed total time:"
            putStrLn $ printf "%.4f secs (%.4f min)." (end - start) ((end - start)/60)

        _ -> do putStrLn "Insert Cedille Term as String and dimension as Integer!"