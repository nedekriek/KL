\begin{code}
module AskTellSpec where

import Test.Hspec
import AskTell

spec :: Spec
spec = describe "func_name1 - Specify collection of Unit/Property/Integration Tests" $ do
        it "test description" $
                True `shouldBe` True
\end{code}