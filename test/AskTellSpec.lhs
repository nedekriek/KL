\begin{code}
module AskTellSpec where

import Test.Hspec


import AskTell
import SyntaxKL
import SemanticsKL

import qualified Data.Map as Map
import qualified Data.Set as Set


spec :: Spec
spec = describe "ask - Unit Tests" $ do
        let atom = Pred "P" []
            f = Atom atom
            ws1 = WorldState (Map.fromList [(atom, True)]) Map.empty
            ws2 =  WorldState (Map.fromList [(atom, False)]) Map.empty
            es = Set.fromList [ws1,ws2]
        it "ask returns false when epistemic state is empty" $ do
                let e = Set.empty
                ask e es f `shouldBe` False
        it "ask returns true when formula is known at the epistemic state" $ do
                let e = Set.fromList [ws1]
                ask (e es f) `shouldBe` True
       
                     
\end{code}


%         it "ask returns false when formula is not known at the epistemic state" $ do
%                 let e = Set.fromList [ws2]
%                 ask e es f `shouldBe` True
        