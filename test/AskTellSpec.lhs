\begin{code}
module AskTellSpec where

import Test.Hspec


import AskTell
import SyntaxKL
import SemanticsKL
import Generators

import Test.QuickCheck
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


spec :: Spec
spec = describe "ask - Example Tests" $ do
        let atom = Pred "P" []
            f = Atom atom
            ask_ws1 = WorldState (Map.fromList [(atom, True)]) Map.empty
            ask_ws2 =  WorldState (Map.fromList [(atom, False)]) Map.empty
            d = Set.empty
        it "ask returns False when the epistemic state is empty" $ do
                let e = Set.empty
                ask d e f `shouldBe` False
        it "ask returns False when formula is not True in all world states." $ do
                let e = Set.fromList [ask_ws1,ask_ws2]
                ask d e f `shouldBe` False
        it "ask returns True when formula is True in all world states." $ do
                let e = Set.fromList [ask_ws1]
                ask d e f `shouldBe` True
        -- ask vs askModel
        it "askModel = ask = False when the epistemic state is empty" $ do
                let e = Set.empty
                    m = Model {actualWorld = (Set.findMin e), epistemicState = e, domain =d}
                ask d e f `shouldBe` askModel m f
        it "askModel = ask = False when formula is not True in all world states." $ do
                let e = Set.fromList [ask_ws1,ask_ws2]
                    m = Model {actualWorld = (Set.findMin e), epistemicState = e, domain =d}
                ask d e f `shouldBe` askModel m f
        it "askModel = ask = True when formula is True in all world states." $ do
                let e = Set.fromList [ask_ws1]
                    m = Model {actualWorld = (Set.findMin e), epistemicState = e, domain =d}
                ask d e f `shouldBe` askModel m f

        describe "ask - Property Tests" $ do
                it "ask is true for the tautology P(x) -> ~~ P(x)" $ do
                        let taut1 = (Or (Not f) (Not (Not f)))
                        property $ 
                                forAll genStdNameSet $ \d' ->  -- d' can be any set
                                forAll genNonEmptyEpistemicState $ \e ->  -- Ensure e is non-empty
                                        ask (d' :: Set StdName) (e :: Set WorldState) taut1 `shouldBe` True
                it "ask is true for the tautology P or ~P" $ do
                        let taut2 = Or (f) (Not f)
                        property $ 
                                forAll genStdNameSet $ \d' ->  -- d' can be any set
                                forAll genNonEmptyEpistemicState $ \e ->  -- Ensure e is non-empty
                                        ask (d' :: Set StdName) (e :: Set WorldState) taut2 `shouldBe` True
        -- TELL 
        describe "tell - Example Tests" $ do
                let atom1 = Pred "P1" []
                    atom2 = Pred "P2" []
                    tell_ws1 = WorldState (Map.fromList [(atom1, True), (atom2, True)]) Map.empty
                    tell_ws2 =  WorldState (Map.fromList [(atom1, True), (atom2, False)]) Map.empty
                    e' = Set.fromList [tell_ws1, tell_ws2]
                    d' = Set.empty
                    f' = Atom atom1
                    g = Atom atom2
                    m = Model {actualWorld = (Set.findMin e'), epistemicState = e', domain =d'}
                it "tell returns the same epistemic state when formula is known" $ do
                        tell d' e' f' `shouldBe` e'
                it "tell returns different epistemic state when formula is not known" $ do
                        (tell d e' g /= e') `shouldBe` True
               -- tell vs tellModel
                it "tell == tellModel  when formula is known" $ do
                        (tell d' e' f' == epistemicState (tellModel m f') ) `shouldBe` True
                it "tell == tellModel  when formula is not known" $ do
                        (tell d' e' g == epistemicState (tellModel m g)) `shouldBe` True
        describe "tell - Property Tests" $ do
                let f' = Atom (Pred "P1" [])
                it "tell shouldnt restrict the epistemic state for the tautology P(x) -> ~~ P(x)" $ do
                        let taut1 = (Or (Not f') (Not (Not f')))
                        property $ \e -> 
                            forAll genStdNameSet $ \d' -> 
                                tell  (d' :: Set StdName) (e :: Set WorldState) taut1 `shouldBe` e
                
        -- Initial 
        describe "initial - Example Tests" $ do
                let patoms_empt = []
                    pterms_empt = []
                    snames_empt = []
                    patoms = [PPred "P1" [StdName "S1", StdName "S2"],PPred "P2" [StdName "S2", StdName "S3"]]
                    pterms = [PStdNameTerm (StdName "S1"),PStdNameTerm (StdName "S2"),PStdNameTerm (StdName "S3")]
                    snames = [StdName "S1", StdName "S2", StdName "S3"]
                it "initial with empty inputs produces empty epistemic state" $ do
                        initial patoms_empt pterms_empt snames_empt == Set.empty `shouldBe` True
                it "initial with nonempty inputs should be nonempty" $ do
                        initial patoms pterms snames /= Set.empty `shouldBe` True

        -- Poteential tests to be added:
        -- initial - tell (contradiction) - is empty
        -- ask (tell e f) f - always returns true

             
\end{code}

