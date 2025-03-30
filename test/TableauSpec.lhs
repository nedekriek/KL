\hide{
\begin{code}
module TableauSpec where

import Test.Hspec
import Tableau
import SyntaxKL
import SemanticsKL
import Generators

import Data.List (nub)
import qualified Data.Set as Set

import Test.QuickCheck
--import Control.Exception (evaluate)

spec :: Spec
spec = do
    describe "Tableau Eq Instances" $ do
        it "Node Eq is derived" $
            property $ \f w -> Node (f :: Formula) (w :: TabWorld) == Node f w
        it "Branch Eq is derived" $
            property $ \ns ps ks -> Branch (ns :: [Node]) (ps :: Set.Set StdName) (ks :: [Node]) == Branch ns ps ks
        it "RuleResult Eq is derived" $
            property $ \r -> (r :: RuleResult) == r

    describe "newParams" $ do
        it "newParams generates fresh parameters not in the used set" $
            property $ \used -> do
                let freshParams = take 5 (newParams (used :: Set.Set StdName))
                all (`Set.notMember` used) freshParams `shouldBe` True
        it "newParams generates distinct parameters" $
            property $ \used -> do
                let freshParams = take 5 (newParams (used :: Set.Set StdName))
                length (nub freshParams) `shouldBe` 5

    describe "applyRule" $ do
        it "applyRule keeps atoms unchanged" $
            property $ forAll genGroundAtom $ \a -> do
                let branch = Branch [] Set.empty []
                    node = Node (Atom a) 0
                applyRule node branch `shouldBe` Open [Branch (nodes branch) (params branch) (retainedSubFormula branch ++ [node]) ]
        it "applyRule splits Or into two branches" $
            property $ forAll genGroundFormula $ \f1 -> forAll genGroundFormula $ \f2 -> do
                let branch = Branch [] Set.empty []
                    node = Node (Or f1 f2) 0
                    expected = Open [ Branch [Node f1 0] Set.empty []
                                    , Branch [Node f2 0] Set.empty []]
                applyRule node branch `shouldBe` expected
        it "applyRule handles Exists with a fresh parameter" $
            property $ \x f -> do
                let branch = Branch [] Set.empty []
                    node = Node (Exists (Var x) f) 0
                case applyRule node branch of
                    Open [newBranch] -> do
                        let newNodes = nodes newBranch
                            usedParams = params newBranch
                        length newNodes `shouldBe` 1
                        Set.size usedParams `shouldBe` 1
                        let newParam = Set.findMin usedParams
                            expectedFormula = subst (Var x) newParam f
                        head newNodes `shouldBe` Node expectedFormula 0
                    _ -> fail "Expected Open with one branch"
        it "applyRule expands K to a new world" $
            property $ forAll genGroundFormula $ \f -> do
                let branch = Branch [] Set.empty []
                    node = Node (K f) 0
                    expected = Open [Branch [Node f 1] Set.empty []]
                applyRule node branch `shouldBe` expected

    describe "isClosed" $ do
        it "isClosed detects atomic contradictions in the same world" $
            property $ forAll genGroundAtom $ \a -> do
                let branch = Branch [Node (Atom a) 0, Node (Not (Atom a)) 0] Set.empty []
                isClosed branch `shouldBe` True
        it "isClosed allows consistent atoms in the same world" $
            property $ forAll genGroundAtom $ \a -> forAll genGroundAtom $ \b -> a /= b ==> do
                let branch = Branch [Node (Atom a) 0, Node (Atom b) 0] Set.empty []
                isClosed branch `shouldBe` False
        it "isClosed allows contradictions across different worlds" $
            property $ forAll genGroundAtom $ \a -> do
                let branch = Branch [Node (Atom a) 0, Node (Not (Atom a)) 1] Set.empty []
                isClosed branch `shouldBe` False
        it "isClosed detects equality contradictions" $
            let t = StdNameTerm (StdName "n1")
                branch = Branch [Node (Equal t t) 0, Node (Not (Equal t t)) 0] Set.empty []
            in isClosed branch `shouldBe` True

    describe "expandTableau" $ do
        it "expandTableau closes contradictory branches" $
            property $ forAll genGroundAtom $ \a -> do
                let initBranch = Branch [Node (Atom a) 0, Node (Not (Atom a)) 0] Set.empty []
                expandTableau [initBranch] `shouldBe` Nothing
        it "expandTableau keeps satisfiable branches open" $
            property $ forAll genGroundAtom $ \a -> do
                let initBranch = Branch [Node (Or (Atom a) (Not (Atom a))) 0] Set.empty []
                case expandTableau [initBranch] of
                    Just branches -> length branches `shouldBe` 2
                    Nothing -> fail "Expected satisfiable formula to yield open branches"

    describe "isSatisfiable" $ do
        context "isSatisfiable on validities and tautologies" $ do
            it "isSatisfiable returns True for P v ~P" $
                property $ forAll genGroundAtom $ \a -> do
                    let f = Or (Atom a) (Not (Atom a))
                    isSatisfiable f `shouldBe` True
            it "isSatisfiable returns True for t = t" $
                property $ forAll genGroundTerm $ \t -> do
                    isSatisfiable (Equal t t) `shouldBe` True
            it "isSatisfiable returns True for K(P) v ~K(P)" $
                property $ forAll genGroundAtom $ \a -> do
                    let f = Or (K (Atom a)) (Not (K (Atom a)))
                    isSatisfiable f `shouldBe` True
        context "isSatisfiable on contradictions" $ do
            it "isSatisfiable returns False for P & ~P" $
                property $ forAll genGroundAtom $ \a -> do
                    let f = Not (Or (Not (Atom a)) (Not (Not (Atom a))))
                    isSatisfiable f `shouldBe` False
            it "isSatisfiable returns False for P & ~P 2" $
                property $ forAll genGroundAtom $ \a -> do
                    let f = Not (Or (Atom a) (Not (Atom a)))
                    isSatisfiable f `shouldBe` False
            it "isSatisfiable returns False for t /= t" $
                property $ forAll genGroundTerm $ \t -> do
                    isSatisfiable (Not (Equal t t)) `shouldBe` False

    describe "isValid" $ do
        context "isValid on valid formulas" $ do
            it "isValid returns True for P v ~P" $
                property $ forAll genGroundAtom $ \a -> do
                    let f = Or (Atom a) (Not (Atom a))
                    isValid f `shouldBe` True
            it "isValid returns True for t = t" $
                property $ forAll genGroundTerm $ \t -> do
                    isValid (Equal t t) `shouldBe` True
            it "isValid returns True for K(P) -> K(K(P))" $
                property $ forAll genGroundAtom $ \a -> do
                    let f = Or (Not (K (Atom a))) (K (K (Atom a)))
                    isValid f `shouldBe` True
            it "isValid returns False for K(~ K(P)) -> K(K(P))" $
                property $ forAll genGroundAtom $ \a -> do
                    let f = Not (Or (Not (K (Not (K (Atom a))))) (K (K (Atom a))))
                    isValid f `shouldBe` False
        context "isValid on non-valid formulas" $ do
            it "isValid returns False for P" $
                property $ forAll genGroundAtom $ \a -> do
                    isValid (Atom a) `shouldBe` False
            it "isValid returns False for K(P)" $
                property $ forAll genGroundAtom $ \a -> do
                    isValid (K (Atom a)) `shouldBe` False
\end{code}
}