\begin{code}
module AskTellSpec where

import Test.Hspec


import AskTell
import SyntaxKL
import SemanticsKL

import qualified Data.Map as Map
import qualified Data.Set as Set


spec :: Spec
spec = describe "ask - Example Tests" $ do
        let atom = Pred "P" []
            f = Atom atom
            ws1 = WorldState (Map.fromList [(atom, True)]) Map.empty
            ws2 =  WorldState (Map.fromList [(atom, False)]) Map.empty
            d = Set.empty

        it "ask returns False when the epistemic state is empty" $ do
                let e = Set.empty
                ask d e f `shouldBe` False
        it "ask returns False when formula is not True in all world states." $ do
                let e = Set.fromList [ws1,ws2]
                ask d e f `shouldBe` False
        it "ask returns True when formula is True in all world states." $ do
                let e = Set.fromList [ws1]
                ask d e f `shouldBe` True
       
       
                     
\end{code}


%         it "ask returns False when formula is not known at the epistemic state" $ do
%                 let e = Set.fromList [ws2]
%                 ask e es f `shouldBe` True
        