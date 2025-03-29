\vspace{10pt}
\begin{code}
module SyntaxKLSpec where

import Test.Hspec
import SyntaxKL

spec :: Spec
spec = describe "func_name1 - Specify collection of Unit/Property/Integration Tests" $ do
            it "test description" $
                True `shouldBe` True
\end{code}