import Test.Hspec
import ElaborationCheckerN
import ElaborationCheckerMP
import Core
import Control.Monad.Logic (observeAllT, LogicT, once, observeT)
import Elaboration
import Data.Maybe (isJust)

main :: IO ()
main = hspec $ do
    describe "Elaboration Checker" $ do
        describe "infers types for Lambda Terms with dimension:" $ do
            it "x, dim 1" $ do
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
            it "(λx. ((λy. (y y)) (λz. z))), dim 2" $ do
                chkElabAll "#x * /#y * /y y #z * z" 2 `shouldBe` True
            it "(\\x. (x x)) ((\\i. i) (t t)), dim 2" $ do
                chkElabAll "/#x * /x x /#i * i /t t" 2 `shouldBe` True
        describe "does not infer types for Lambda Terms with dimension:" $ do
            it "(\\x. \\y. y (x x)) z, dim 1" $ do
                chkElabAll "/#x * #y * /y /x x z" 1 `shouldBe` False
            it "Omega = omega omega, dim 1" $ do
                chkElabAll "/#x * /x x #x * /x x" 1  `shouldBe` False
            it "(\\x. x x x) i, dim 2" $ do
                chkElabAll "/#x * /x /x x i" 2 `shouldBe` False
            it "(\\x. (x x)) (\\j. \\i. i), dim 2" $ do
                chkElabAll "/#x * /x x #j * #i * i" 2 `shouldBe` False
        describe "erases terms correctly" $ do
            it "Let and erased Lambda - $ITrue IBool %P @ CBool * #T /P CTrue #F /P CFalse T erased to True" $ do
                (erasTrm . fromString) "$ITrue IBool %P @ CBool * #T /P CTrue #F /P CFalse T" `shouldBe` TrmP (AppP ( TrmP $ LamP "ITrue" (TrmP (LamP "T" (TrmP $ LamP "F" (TrmP $ VarP "T")))) ) (TrmP $ VarP "IBool"))
            it "Erased Application - #x * \\x. \\x x to \\x. x" $ do
                (erasTrm . fromString) "#x * \\x \\x x" `shouldBe` TrmP (LamP "x" (TrmP $ VarP "x"))
        describe "prints elaborations correct (only for coverage)" $ do
            it "correct elaboration for (\\x. \\y. y (x x)) z" $ do
                (show . head) ( (( once (prsAndElabN "/#x * #y * /y /x x z" 2)) :: [Elaboration VariableE]) ) `shouldBe` "((λx. (λy. (y<(β_1'1) → β_0'7> (x<(β_2'2) → β_1'1> x<β_2'2>)<β_1'1>)<β_0'7>)<((β_1'1) → β_0'7) → β_0'7>)<([β_2'2 , (β_2'2) → β_1'1]) → ((β_1'1) → β_0'7) → β_0'7> z<[β_2'2 , (β_2'2) → β_1'1]>)<((β_1'1) → β_0'7) → β_0'7>"
            it "correct elaboration for x" $ do
                (show . head) ( (( once (prsAndElabN "x" 1)) :: [Elaboration VariableE]) ) `shouldBe` "x<α_1>"


            

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
chkElabListN trm dim = not $ null ( (once (prsAndElabN trm dim)) :: [Elaboration VariableE] )