\section{Semantics Tests}

\begin{code}
{-# LANGUAGE InstanceSigs #-}

module Main where

import SemanticsKL
import SyntaxKL
import Generators

import qualified Data.Map as Map
import qualified Data.Set as Set

import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)
\end{code}

\begin{code}
main :: IO ()
main = hspec $ do
    describe "Eq is derived for the relevant KL Semantics" $ do
        it "WorldState Eq is derived" $ do
            property $ \w -> w == (w :: WorldState)
        -- TODO: add test to be sure that the world state only has primitive terms and atoms
    describe "evalTerm" $ do
        it "evalTerm errors with variables" $ do
            property $ \x -> evaluate (evalTerm (WorldState Map.empty Map.empty) (VarTerm x)) `shouldThrow` anyException
        it "evalTerm returns the StdName for StdNameTerm" $ do
            property $ \w n -> evalTerm w (StdNameTerm n) == n
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
    describe "isGround" $ do
        it "isGround returns False for VarTerm" $ do
            property $ \n -> not $ isGround (VarTerm n)
        it "isGround returns True for GroundFuncAppTerm or GroundStdNameTerm" $ do
           property $ forAll genGroundTerm $ \t -> isGround (t :: Term)
        it "isGround returns False for complex FuncAppTerm with a non-ground argument" $ do
            let term = FuncAppTerm "f" [FuncAppTerm "g" [VarTerm $ Var "x", StdNameTerm $ StdName "n1"]]
            isGround term `shouldBe` False
    describe "isGroundFormula" $ do 
        it "isGroundFormula returns True for groundFormula" $ do
            property $ forAll genGroundFormula $ \f -> isGroundFormula (f :: Formula)
        it "isGroundFormula returns False for Exists" $ do
            property $ \n f -> not $ isGroundFormula (Exists (Var n) (f :: Formula))
        it "isGroundFormula returns False for Atom with a non-ground term" $ do
            isGroundFormula (Atom (Pred "P" [VarTerm $ Var "x"])) `shouldBe` False
        it "isGroundFormula returns False for Equal with a non-ground term" $ do
            isGroundFormula (Equal (VarTerm $ Var"x") (StdNameTerm $ StdName "n1")) `shouldBe` False
    describe "substTerm" $ do
        it "substTerm replaces the variable with the StdName" $ do
            let term = FuncAppTerm "f" [VarTerm $ Var "x", StdNameTerm $ StdName "n1"]
            substTerm (Var "x") (StdName "n2") term `shouldBe` FuncAppTerm "f" [StdNameTerm $ StdName "n2", StdNameTerm $ StdName "n1"]
        it "substTerm does not replace the wrong variable" $ do
            let term = FuncAppTerm "f" [VarTerm $ Var "y", StdNameTerm $ StdName "n1"]
            substTerm (Var "x") (StdName "n2") term `shouldBe` term
    describe "subst" $ do 
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
    describe "satisfiesModel" $ do 
        let x = Var "x"
            n1 = StdNameTerm $ StdName "n1"
            n2 = StdNameTerm $ StdName "n2"
            p = Atom (Pred "P" [])
            px = Atom (Pred "P" [VarTerm x])
            py = Atom (Pred "P" [VarTerm $ Var "y"])
            pt = Atom (Pred "P" [n1])
        context "satisfiesModel satisfies validities when atoms are ground" $ do
            it "satisfiesModel satisfies P -> ~~ P" $ do
                property $ \m -> satisfiesModel m (Or (Not p) (Not (Not p))) `shouldBe` True
            it "satisfiesModel satisfies P(t) -> ~~ P(t)" $ do
                property $ \m -> satisfiesModel m (Or (Not pt) (Not (Not pt))) `shouldBe` True
            it "satisfiesModel errors for P(x) -> ~~ P(x)" $ do
                property $ \m -> evaluate (satisfiesModel m (Or (Not px) (Not (Not px)))) `shouldThrow` anyException
            it "satisfiesModel satisfies t=t" $ do
                property $ \m -> satisfiesModel m (Equal n1 n1) `shouldBe` True
            it "satisfiesModel errors for x=x" $ do
                property $ \m -> evaluate (satisfiesModel m (Equal (VarTerm x) (VarTerm x))) `shouldThrow` anyException
            it "satisfiesModel satisfies ForAll x (P(x) -> P(x))" $ do 
                property $ \m -> satisfiesModel m (Not (Exists x (Not (Or (Not px) px)))) `shouldBe` True
            it "satisfiesModel satisfies ForALL x (P(x) -> ~~ P(x))" $ do 
                property $ \m -> satisfiesModel m (Not (Exists x (Not (Or (Not px) (Not (Not px))))) ) `shouldBe` True
            it "satisfiesModel satisfies ForAll x (P(x) -> Exists y P(y))" $ do 
                property $ \m -> satisfiesModel m (Not (Exists x (Not (Or (Not px) (Exists (Var "y") py)) ))) `shouldBe` True
            it "satisfiesModel satisfies ((n1 = n2) -> K (n1 = n2)" $ do
                property $ \m -> satisfiesModel m (Or (Not (Equal n1 n2)) (K (Equal n1 n2))) `shouldBe` True
            it "satisfiesModel satisfies ((n1 /= n2) -> K (n1 /= n2)" $ do
                property $ \m -> satisfiesModel m (Or (Not (Not (Equal n1 n2))) (K (Not (Equal n1 n2)))) `shouldBe` True            
            it "satisfiesModel satisfies (K alpha -> K K alpha)" $ do
                property $ \m -> satisfiesModel m (Or (Not (K pt)) (K (K pt))) `shouldBe` True
            it "satisfiesModel satisfies (~K alpha -> K ~K alpha)" $ do
                property $ \m -> satisfiesModel m (Or (Not (Not (K pt))) (K (Not (K pt)))) `shouldBe` True
        context "satisfiesModel does not satisfy contradictions when atoms are ground" $ do
            it "satisfiesModel does not satisfy ~(P v ~P)" $ do
                property $ \m -> satisfiesModel m (Not (Or p (Not p))) `shouldBe` False
            it "satisfiesModel does not satisfy (Exists x (x /= x))" $ do
                property $ \m -> satisfiesModel m (Exists x (Not (Equal (VarTerm x) (VarTerm x)))) `shouldBe` False
    describe "freeVars" $ do
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
                let f = (Or (Or (Not px) py) (Equal n1 n2))
                freeVars f `shouldBe` Set.fromList [x, y]
            it "freeVars returns the free variables in a complex formula" $ do
                let f = (Exists x (Or (Or (Not px) pf) (Equal n1 n2)))
                freeVars f `shouldBe` Set.fromList [y]
    describe "groundFormula" $ do
        it "groundFormula returns a ground formula (dependant on isGroundFormula passing all tests)" $ do
            property $ forAll (resize 5 arbitrary) $ \f ->
                forAll genStdNameSet $ \s ->
                    all isGroundFormula (groundFormula (f :: Formula) s)
    describe "checkModel" $ do
        let x = Var "x"
            px = Atom (Pred "P" [VarTerm x])
        context "checkModel satisfies validities when atoms are unground" $ do
            it "checkModel errors for P(x) -> ~~ P(x)" $ do
                property $ \m -> checkModel m (Or (Not px) (Not (Not px))) `shouldBe` True 
            it "checkModel errors for x=x" $ do
                property $ \m -> checkModel m (Equal (VarTerm x) (VarTerm x)) `shouldBe` True 
            
\end{code}
 

