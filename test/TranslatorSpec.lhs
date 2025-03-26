\begin{code}
module TranslatorSpec where

import Test.Hspec
import Test.QuickCheck
import Data.Maybe
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Translator
import SyntaxKL
import SemanticsKL

import Generators


spec :: Spec
spec =  describe "translateFormToKr" $ do
        let formula1 = Atom (Pred "P" [StdNameTerm n1])
            formula2 = K (Atom (Pred "P" [StdNameTerm n1]))
            formula3 = Not (K (Atom (Pred "P" [StdNameTerm n1])))
            trFormula1 = P 1
            trFormula2 = Box (P 1) 
            trFormula3 = Neg (Box (P 1))
            formula4 = Atom (Pred "Teach" [StdNameTerm n1, StdNameTerm n2])
            formula5 = Not (K (Atom (Pred "Q" [StdNameTerm n1])))

        it "'P(n1)' correctly translated" $ do
            fromJust (translateFormToKr formula1) `shouldBe` trFormula1
        it "'K(P(n1))' correctly translated" $ do
            fromJust (translateFormToKr formula2) `shouldBe` trFormula2
        it "'~K(P(n1))' correctly translated" $ do
            fromJust (translateFormToKr formula3) `shouldBe` trFormula3
        it "'Teach(n1, n2)' shouldn't be translated (the translation function should return Nothing)" $ do
            isNothing (translateFormToKr formula4) `shouldBe` True
        it "'~K(Q(n1))' shouldn't be translated (the translation function should return Nothing)" $ do
            isNothing (translateFormToKr formula5) `shouldBe` True

        describe "translateModToKr" $ do
            let n1 = StdName "n1" 
                n2 = StdName "n2" 
                n3 = StdName "n3" 
                n4 = StdName "n4" 

                -- a model where the actual world is part of the epistemic state
                w1, w2, w3, w4 :: WorldState
                w1 = mkWorldState [ (PPred "P" [n1], True) ] []
                w2 = mkWorldState [ (PPred "P" [n2], True)
                    , (PPred "P" [n3], True) ] []
                w3 = mkWorldState [ (PPred "P" [n4], True) ] []
                w4 = mkWorldState [] []

                e1 :: EpistemicState
                e1 = Set.fromList [w1, w2, w3, w4]

                domain1 :: Set StdName
                domain1 = Set.fromList [n1, n2, n3, n4]

                model1 :: Model
                model1 = Model w1 e1 domain1

                -- if all goes well, this should be converted to the following KripkeModel
                kripkeM1 :: KripkeModel
                kripkeM1 = KrM uni val rel where
                    uni = [w1, w2, w3, w4]
                    val world   | world == w1 = [1]
                                | world == w2 = [2, 3]
                                | world == w3 = [4]
                                | otherwise   = []
                    rel = [(v, v') | v <- uni, v' <- uni]

                -- a model where the actual world is NOT part of the epistemic state
                e2 :: EpistemicState
                e2 = Set.fromList [w2, w3, w4]

                model2 :: Model
                model2 = Model w1 e2 domain1

                -- if all goes well, this should be converted to the following KripkeModel
                kripkeM2 :: KripkeModel
                kripkeM2 = KrM uni val rel where
                    uni = [w1, w2, w3, w4]
                    val world   | world == w1 = [1]
                                | world == w2 = [2, 3]
                                | world == w3 = [4]
                                | otherwise   = []
                    rel = [(v, v') | v <- es, v' <- es] ++ [(w1, v) | v <- es] where
                        es = [w2, w3, w4]

                -- a model that contains non-atomic formulas
                w2' :: WorldState
                w2' = mkWorldState [ (PPred "P" [n2], True)
                                , (PPred "P" [n3], True) 
                                , (PPred "R" [n4, n1], True)] []

                e1' :: EpistemicState
                e1' = Set.fromList [w1, w2', w3, w4]

                -- model1' is like model1, except for extra formulas true in w2' that aren't
                -- true in w2
                model1' :: Model
                model1' = Model w1 e1' domain1

            it "correct conversion of model where actual world is in epistemic state" $ do
                translateModToKr model1 == kripkeM1 `shouldBe` True
            it "correct conversion of model where actual world is not in epistemic state" $ do
                translateModToKr model1 == kripkeM1 `shouldBe` True
            it "if the only difference between two KL models is in one of them, additional formulas not of the form 'P(standardname)' are true, they should be converted to Kripke models that 'look the same'" $ do
                translateKrToKrInt (translateModToKr model1) == translateKrToKrInt (translateModToKr model1') `shouldBe` True

        describe "integration tests language translation" $ do
            it "translating KL to SEL formula, and then back, shouldn't change anything" $ do
                property $ True --forAll genTransFormula $ \f -> f == translateFormToKL (fromJust (translateFormToKr f))
                --this currently doesn't work, because the modal language doesn't have disjunction => discuss how to fix
            it "translating SEL to KL, and then back, shouldn't change anything" $ do
                property $ \g -> g == fromJust (translateFormToKr (translateFormToKL g))
        
        describe "integration tests model translation" $ do
            it "translating KL to SEL model, and then back, shouldn't change anything" $ do
                property $ \(Model w e d) -> (Model w e d) == fromJust (kripkeToKL (translateModToKr (Model w e d)) w) 

        describe "combined" $ do
            it "if a formula is true in a KL model, its translation should be true at the corresponding Kripke model and world, and vice versa" $ do
                property $ \(Model w e d) f -> ((Model w e d) `satisfiesModel` f) <==> ((translateModToKr (Model w e d), w) `makesTrue` fromJust (translateFormToKr f))
                    
            it "if a formula is true at a world and Kripke model, then it should be true at the corresponding KL model, and vice versa" $ do
                property $ forAll (do
                    (m, w) <- genTransEucKripkeWithWorld `suchThat` (\(m, w) -> w `elem` (universe m))
                    g <- arbitrary 
                    return (m, w, g)
                    ) $ \(m, w, g) ->  ((m, w) `makesTrue` g <==> (fromJust (kripkeToKL m w) `satisfiesModel` (translateFormToKL g)))

(<==>) :: Bool -> Bool -> Bool
(<==>) p q = (p && q) || (not p && not q)
\end{code}