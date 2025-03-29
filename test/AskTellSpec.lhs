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
        describe "ask - Property Tests" $ do
                it "ask is true for all tautologies" $ do
                        let taut1 = (Or (Not f) (Not (Not f)))
                        -- property $ \e -> (e :: Set WorldState) == e
                        property $ \e -> 
                            forAll genStdNameSet $ \d' -> 
                                tell  (d' :: Set StdName) (e :: Set WorldState) taut1 `shouldBe` e
                        
                        

        --                         

        -- TELL 



        describe "tell - Example Tests" $ do
                let atom1 = Pred "P1" []
                    atom2 = Pred "P2" []
                    tell_ws1 = WorldState (Map.fromList [(atom1, True), (atom2, True)]) Map.empty
                    tell_ws2 =  WorldState (Map.fromList [(atom1, True), (atom2, False)]) Map.empty
                    e' = Set.fromList [tell_ws1, tell_ws2]
                    d' = Set.empty
                it "tell returns the same epistemic state when formula is known" $ do
                        let f' = Atom atom1
                        tell d' e' f' `shouldBe` e'
                -- it "tell returns different epistemic state when formula is not known" $ do
                --        let g = Atom atom2
                --         (tell d e g) <> e `shouldBe` True
        
        -- TELL ASK - always returns true

             
\end{code}

 % Arbitrary WorldState 
 % to get arbitary epistemic state, 


%         it "ask returns False when formula is not known at the epistemic state" $ do
%                 let e = Set.fromList [ws2]
%                 ask e es f `shouldBe` True
        