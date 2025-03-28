\begin{code}
module SemanticsKLSpec where

import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)

import qualified Data.Map as Map
import qualified Data.Set as Set

import SemanticsKL -- tested module
import SyntaxKL    -- types used in tests
import Generators  -- helper functions for testing

\end{code}

The following tests are for the semantics of $\mathcal{KL}$, which are defined in the SemanticsKL module. The tests are written using the Hspec testing framework and QuickCheck for property-based testing. The tests cover the evaluation of terms, formulas, and models, as well as model checking function. The Generators file provides helper functions for generating implementing testing, but have been omitted for brevity.


\begin{code}
spec :: Spec
spec =  describe "evalTerm - Unit Tests" $ do
        it "evalTerm returns the StdName after applying all functions (depth 2)" $ do
            let n1 = StdName "n1"
                n2 = StdName "n2"
                n3 = StdName "n3"
                n4 = StdName "n4"
                w = WorldState Map.empty (Map.fromList [
                                            (FuncAppTerm "f" [StdNameTerm n1, StdNameTerm n2],  n3),
                                            (FuncAppTerm "g" [StdNameTerm n4], n1)
                                        ])
                t = FuncAppTerm "f" [FuncAppTerm "g" [StdNameTerm n4], StdNameTerm n2]
            evalTerm w t `shouldBe` StdName "n3"

        describe "evalTerm - Property Tests" $ do
            it "evalTerm errors for all variables passed" $ do
                property $ \ w x -> evaluate (evalTerm w (VarTerm x)) `shouldThrow` anyException
            it "evalTerm returns the StdName for StdNameTerm" $ do
                property $ \w n -> evalTerm w (StdNameTerm n) == n


        describe "isGround - Unit Tests" $ do
            it "isGround returns True for StdNameTerm" $ do
                isGround (StdNameTerm $ StdName "n1") `shouldBe` True
            it "isGround returns False for VarTerm" $ do
                isGround (VarTerm $ Var "x") `shouldBe` False
            it "isGround returns True for FuncAppTerm with all ground arguments" $ do
                isGround (FuncAppTerm "f" [StdNameTerm $ StdName "n1"]) `shouldBe` True
            it "isGround returns False for complex FuncAppTerm with at least one non-ground argument" $ do
                let term = FuncAppTerm "f" [FuncAppTerm "g" [VarTerm $ Var "x", StdNameTerm $ StdName "n1"]]
                isGround term `shouldBe` False


        describe "isGroundFormula - Unit Tests" $ do
            it "isGroundFormula returns False for Atom with a non-ground term" $ do
                isGroundFormula (Atom (Pred "P" [VarTerm $ Var "x"])) `shouldBe` False
            it "isGroundFormula returns False for Equal with a non-ground term" $ do
                isGroundFormula (Equal (VarTerm $ Var"x") (StdNameTerm $ StdName "n1")) `shouldBe` False

        describe "isGroundFormula - Property Tests" $ do
            it "isGroundFormula returns True for groundFormula" $ do
                property $ forAll genGroundFormula $ \f -> isGroundFormula (f :: Formula)
            --todo fix this test
            it "isGroundFormula returns False for Exists" $ do
                property $ \n f -> not $ isGroundFormula (Exists (Var n) (f :: Formula))


        describe "substTerm - Unit Tests" $ do
            it "substTerm replaces the variable with the StdName" $ do
                let term = FuncAppTerm "f" [VarTerm $ Var "x", StdNameTerm $ StdName "n1"]
                substTerm (Var "x") (StdName "n2") term `shouldBe` FuncAppTerm "f" [StdNameTerm $ StdName "n2", StdNameTerm $ StdName "n1"]
            it "substTerm does not replace the wrong variable" $ do
                let term = FuncAppTerm "f" [VarTerm $ Var "y", StdNameTerm $ StdName "n1"]
                substTerm (Var "x") (StdName "n2") term `shouldBe` term


        describe "subst - Unit Tests" $ do
            it "subst replaces the variable with the StdName in an Atom" $ do
                let atom = Atom (Pred "P" [VarTerm $ Var "x"])
                show (subst (Var "x") (StdName "n1") atom) `shouldBe` show (Atom (Pred "P" [StdNameTerm $ StdName "n1"]))
            it "subst replaces the variable with the StdName in an Equal" $ do
                let formula = Equal (VarTerm $ Var "x") (StdNameTerm $ StdName "n1")
                show (subst (Var "x") (StdName "n2") formula) `shouldBe` show (Equal (StdNameTerm $ StdName "n2") (StdNameTerm $ StdName "n1"))
            it "subst replaces the variable with the StdName in a Not formula" $ do
                let formula = Not (Atom (Pred "P" [VarTerm $ Var "x"]))
                show (subst (Var "x") (StdName "n1") formula) `shouldBe` show (Not (Atom (Pred "P" [StdNameTerm $ StdName "n1"])))
            it "subst replaces the variable with the StdName in an Or formula" $ do
                let formula = Or (Atom (Pred "P" [VarTerm $ Var "x"])) (Atom (Pred "Q" [VarTerm $ Var "y"]))
                show (subst (Var "x") (StdName "n1") formula) `shouldBe` show (Or (Atom (Pred "P" [StdNameTerm $ StdName "n1"])) (Atom (Pred "Q" [VarTerm $ Var "y"])))
            it "subst replaces the variable with the StdName in an Exists if the variable not in Exists scope" $ do
                let formula = Exists (Var "x") (Atom (Pred "P" [VarTerm $ Var "x", VarTerm $ Var "y"]))
                -- replaces y with n2
                show (subst (Var "y") (StdName "n2") formula) `shouldBe` show (Exists (Var "x") (Atom (Pred "P" [VarTerm $ Var "x", StdNameTerm $ StdName "n2"])))
            it "subst does not replace the variable with the StdName in Exists if the variable is in the Exists scope" $ do
                let formula = Exists (Var "x") (Atom (Pred "P" [VarTerm $ Var "x", VarTerm $ Var "y"]))
                -- does not replace x with n2
                show (subst (Var "x") (StdName "n2") formula) `shouldBe` show formula
            it "subst replaces the variable with the StdName in a K formula" $ do
                let formula = K (Atom (Pred "P" [VarTerm $ Var "x"]))
                show (subst (Var "x") (StdName "n2") formula) `shouldBe` show (K (Atom (Pred "P" [StdNameTerm $ StdName "n2"])))


        describe "isTrueModel - Property Tests" $ do
            -- test fixtures
            let x = Var "x"
                n1 = StdNameTerm $ StdName "n1"
                n2 = StdNameTerm $ StdName "n2"
                p = Atom (Pred "P" [])
                px = Atom (Pred "P" [VarTerm x])
                py = Atom (Pred "P" [VarTerm $ Var "y"])
                pt = Atom (Pred "P" [n1])
            context "isTrueModel satisfies validities when atoms are ground" $ do
                it "isTrueModel satisfies P -> ~~ P" $ do
                    property $ \m -> isTrueModel m (Or (Not p) (Not (Not p))) `shouldBe` True
                it "isTrueModel satisfies P(t) -> ~~ P(t)" $ do
                    property $ \m -> isTrueModel m (Or (Not pt) (Not (Not pt))) `shouldBe` True
                it "isTrueModel errors for P(x) -> ~~ P(x)" $ do
                    property $ \m -> evaluate (isTrueModel m (Or (Not px) (Not (Not px)))) `shouldThrow` anyException
                it "isTrueModel satisfies t=t" $ do
                    property $ \m -> isTrueModel m (Equal n1 n1) `shouldBe` True
                it "isTrueModel errors for x=x" $ do
                    property $ \m -> evaluate (isTrueModel m (Equal (VarTerm x) (VarTerm x))) `shouldThrow` anyException
                it "isTrueModel satisfies ForAll x (P(x) -> P(x))" $ do 
                    property $ \m -> isTrueModel m (Not (Exists x (Not (Or (Not px) px)))) `shouldBe` True
                it "isTrueModel satisfies ForALL x (P(x) -> ~~ P(x))" $ do 
                    property $ \m -> isTrueModel m (Not (Exists x (Not (Or (Not px) (Not (Not px))))) ) `shouldBe` True
                it "isTrueModel satisfies ForAll x (P(x) -> Exists y P(y))" $ do 
                    property $ \m -> isTrueModel m (Not (Exists x (Not (Or (Not px) (Exists (Var "y") py)) ))) `shouldBe` True
                it "isTrueModel satisfies ((n1 = n2) -> K (n1 = n2)" $ do
                    property $ \m -> isTrueModel m (Or (Not (Equal n1 n2)) (K (Equal n1 n2))) `shouldBe` True
                it "isTrueModel satisfies ((n1 /= n2) -> K (n1 /= n2)" $ do
                    property $ \m -> isTrueModel m (Or (Not (Not (Equal n1 n2))) (K (Not (Equal n1 n2)))) `shouldBe` True            
                it "isTrueModel satisfies (K alpha -> K K alpha)" $ do
                    property $ \m -> isTrueModel m (Or (Not (K pt)) (K (K pt))) `shouldBe` True
                it "isTrueModel satisfies (~K alpha -> K ~K alpha)" $ do
                    property $ \m -> isTrueModel m (Or (Not (Not (K pt))) (K (Not (K pt)))) `shouldBe` True
            context "isTrueModel does not satisfy contradictions when atoms are ground" $ do
                it "isTrueModel does not satisfy ~(P v ~P)" $ do
                    property $ \m -> isTrueModel m (Not (Or p (Not p))) `shouldBe` False
                it "isTrueModel does not satisfy (Exists x (x /= x))" $ do
                    property $ \m -> isTrueModel m (Exists x (Not (Equal (VarTerm x) (VarTerm x)))) `shouldBe` False
        

        describe "freeVars - Unit Tests" $ do
            -- test fixtures
            let x = Var "x"
                y = Var "y"
                n1 = StdNameTerm $ StdName "n1"
                n2 = StdNameTerm $ StdName "n2"
                px = Atom (Pred "P" [VarTerm x])
                py = Atom (Pred "P" [VarTerm y])
                pf = Atom (Pred "P" [FuncAppTerm "f" [VarTerm x], FuncAppTerm "g" [VarTerm y]])
            it "freeVars returns nothing if no free var in formula" $ do
                let f = Exists x (Or (Or (Not px) (Exists y py)) (Equal n1 n2))
                freeVars f `shouldBe` Set.fromList []
            it "freeVars returns the free variables in a simple formula" $ do
                let f = Or (Or (Not px) py) (Equal n1 n2)
                freeVars f `shouldBe` Set.fromList [x, y]
            it "freeVars returns the free variables in a complex formula" $ do
                let f = Exists x (Or (Or (Not px) pf) (Equal n1 n2))
                freeVars f `shouldBe` Set.fromList [y]
        
        describe "groundFormula - Property Tests" $ do
            -- This is an expensive test, so we limit the size of the formula
            it "groundFormula returns a ground formula (dependant on isGroundFormula passing all tests)" $ do
               property $ forAll (resize 5 arbitrary) $ \f ->
                   forAll genStdNameSet $ \s ->
                       all isGroundFormula (groundFormula (f :: Formula) s)

        describe "checkModel - Property Tests" $ do
            -- test fixtures
            let x = Var "x"
                px = Atom (Pred "P" [VarTerm x])
            describe "checkModel satisfies validities when atoms are unground" $ do
                it "checkModel arbitrary model satisfies P(x) -> ~~ P(x)" $ do
                    property $ \m -> checkModel m (Or (Not px) (Not (Not px))) `shouldBe` True 
                it "checkModel  arbitrary model satisfies for x=x" $ do
                    property $ \m -> checkModel m (Equal (VarTerm x) (VarTerm x)) `shouldBe` True 

\end{code}