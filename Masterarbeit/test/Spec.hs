import Test.Hspec
import ElaborationChecker
import ElaborationCheckerN
import ElaborationCheckerMP
import Control.Monad.Logic (observeT)
import Elaboration
import Data.Maybe (isJust)

main :: IO ()
main = hspec $ do
    describe "Elaboration Checker" $ do
        describe "infers types for Lambda Terms with dimension:" $ do
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
                chkElabAll "/#x * /x x #f * /f f" 1  `shouldBe` False
            it "(\\x. x x x) i, dim 2" $ do
                chkElabAll "/#x * /x /x x i" 2 `shouldBe` False
        -- describe "erases terms correctly" $ do
            

chkElabAll :: String -> Int -> Bool
chkElabAll trm dim = chkElab trm dim && chkElabMP trm dim && chkElabN trm dim

chkElabN :: String -> Int -> Bool
chkElabN trm dim = isJust (observeT (ElaborationCheckerN.prsAndElab trm dim))

chkElab :: String -> Int -> Bool
chkElab trm dim = isJust (observeT (ElaborationChecker.prsAndElab trm dim))

chkElabMP :: String -> Int -> Bool
chkElabMP trm dim = isJust (observeT (ElaborationCheckerMP.prsAndElab trm dim))

