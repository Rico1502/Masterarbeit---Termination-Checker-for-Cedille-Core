import Test.Hspec
import ElaborationCheckerN
import ElaborationCheckerMP
import ElaborationCheckerListN
import Control.Monad.Logic (LogicT, once, observeT)
import Elaboration
import Data.Maybe (isJust)

main :: IO ()
main = hspec $ do
    describe "Elaboration Checker" $ do
        describe "infers types for Lambda Terms with dimension:" $ do
            it "x" $ do
                chkElabAll "x" 1 `shouldBe` True
            it "I = \\x. x, dim 1" $ do
                chkElabAll "#x * x" 1 `shouldBe` True
            it "K = \\x. \\y. x, dim 1" $ do
                chkElabAll "#x * #y * x" 1 `shouldBe` True
            it "S = \\x. \\y. \\z. ((x z) (y z)), dim 1" $ do
                chkElabAll "#x * #y * #z * //x z /y z" 1 `shouldBe` True
            it "omega = \\x. x x, dim 1 " $ do
                chkElabAll "#x * /x x" 1 `shouldBe` True
            it "omega = \\x. x x, dim 2 " $ do
                chkElabAll "#x * /x x" 2 `shouldBe` True
            it "(\\x. \\y. y (x x)) z, dim 2" $ do
                chkElabAll "/#x * #y * /y /x x z" 2 `shouldBe` True
        describe "does not infer types for Lambda Terms with dimension:" $ do
            it "(\\x. \\y. y (x x)) z, dim 1" $ do
                chkElabAll "/#x * #y * /y /x x z" 1 `shouldBe` False
            it "Omega = omega omega" $ do
                chkElabAll "/#x * /x x #x * /x x" 1  `shouldBe` False
            it "(\\x. x x x) i, dim 2" $ do
                chkElabAll "/#x * /x /x x i" 2 `shouldBe` False
        -- describe "erases terms correctly" $ do
            

chkElabAll :: String -> Int -> Bool
chkElabAll trm dim = 
    chkElabMP trm dim && 
    chkElabN trm dim &&
    chkElabListN trm dim

chkElabN :: String -> Int -> Bool
chkElabN trm dim = isJust ( observeT ( (once (prsAndElabN trm dim)) :: LogicT Maybe (Elaboration VariableE)) )

chkElabMP :: String -> Int -> Bool
chkElabMP trm dim = not $ null ( ( (prsAndElabMP trm dim)) :: [Elaboration VariableE])

chkElabListN :: String -> Int -> Bool
chkElabListN trm dim = not $ null ( (once (prsAndElabLN trm dim)) :: [Elaboration VariableE] )