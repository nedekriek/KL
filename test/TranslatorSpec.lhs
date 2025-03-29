\vspace{10pt}
\begin{code}
module TranslatorSpec where

import Test.Hspec
import Test.QuickCheck
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set


import Translator hiding (dia)
import SyntaxKL
import SemanticsKL

import Generators

-- We will use the following repeatedly, and therefore define them globally.
n1, n2, n3, n4 :: StdName
n1 = StdName "n1" 
n2 = StdName "n2" 
n3 = StdName "n3" 
n4 = StdName "n4" 

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
            let -- a model where the actual world is part of the epistemic state
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
                kripkeM1 :: KripkeModel WorldState
                kripkeM1 = KrM uni val rel where
                    uni = [w1, w2, w3, w4]
                    val world   | world == w1 = [1]
                                | world == w2 = [2, 3]
                                | world == w3 = [4]
                                | otherwise   = []
                    rel = [(v, v') | v <- uni, v' <- uni]

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
                property $ forAll genTransFormula $ \f -> f == translateFormToKL (fromJust (translateFormToKr f))
            it "translating SEL to KL, and then back, shouldn't change anything" $ do
                property $ \g -> g == fromJust (translateFormToKr (translateFormToKL g))

        describe "integration tests language and model translation" $ do
            it "if a translatable formula is true in a KL model, its translation should be true at the corresponding Kripke model and world, and vice versa" $ do
                property $ forAll (do
                    m <- resize 6 arbitrary
                    f <- resize 6 genTransFormula
                    return (m, f)
                    ) $ \(Model w e d, f) -> (Model w e d `satisfiesModel` f) <==> ((translateModToKr (Model w e d), w) `makesTrue` fromJust (translateFormToKr f))
                    
            it "if a formula is true at a world and Kripke model, then it should be true at the corresponding KL model, and vice versa" $ do
                property $ forAll (do
                    (m, w) <- genTransEucKripkeWithWorld `suchThat` (\(m, w) -> w `elem` universe m)
                    g <- arbitrary 
                    return (m, w, g)
                    ) $ \(m, w, g) ->  (m, w) `makesTrue` g <==> (fromJust (kripkeToKL m w) `satisfiesModel` translateFormToKL g)

        describe "trueEverywhere" $ do
            let ww1 = mkWorldState [(PPred "P" [StdName "n1"], True)] []
                ww2 = mkWorldState [(PPred "P" [StdName "n1"], True), (PPred "P" [StdName "n2"], True)] []
                modelAllP1 = KrM [ww1, ww2] trueAtomicPropsAt [(ww1, ww1), (ww1, ww2), (ww2, ww1), (ww2, ww2)]
                modelSomeP1 = KrM [ww1, mkWorldState [] []] trueAtomicPropsAt [(ww1, ww1)]

                w1, w2 :: WorldState
                w1 = mkWorldState [ (PPred "P" [n1], True) ] []
                w2 = mkWorldState [ (PPred "P" [n2], True)
                    , (PPred "P" [n3], True) ] []

            it "returns true when P 1 is true in every world" $ do
                trueEverywhere modelAllP1 (P 1) `shouldBe` True

            it "returns false when P 1 is not true in every world" $ do
                trueEverywhere modelSomeP1 (P 1) `shouldBe` False

            it "returns true for Box (P 1) when P 1 is true in all accessible worlds from every world" $ do
                trueEverywhere modelAllP1 (Box (P 1)) `shouldBe` True

            it "returns false for Box (P 1) when P 1 is not true in all accessible worlds" $ do
                let modelPartial = KrM [w1, w2] trueAtomicPropsAt [(w1, w2)]
                trueEverywhere modelPartial (Box (P 1)) `shouldBe` False

            it "holds everywhere if and only if makesTrue holds for all worlds (property)" $
                property $ do
                    model <- genRandomKripkeModel
                    formula <- genModForm
                    let holdsEverywhere = trueEverywhere model formula
                        univ = universe model
                    return $ holdsEverywhere <==> all (\w -> makesTrue (model, w) formula) univ

            it "Box f holds everywhere iff f holds in all accessible worlds from every world (property)" $
                property $ do
                    model <- genRandomKripkeModel
                    f <- genModForm
                    let univ = universe model
                        rel = relation model
                        holdsEverywhere = trueEverywhere model (Box f)
                        allAccessibleSatisfy = all (\w -> all (\w' -> makesTrue (model, w') f) (rel ! w)) univ
                    return $ holdsEverywhere <==> allAccessibleSatisfy



        describe "kripkeToKL" $ do
        -- Specific test cases
            let ww1 = mkWorldState [(PPred "P" [StdName "n1"], True)] []
                ww2 = mkWorldState [(PPred "P" [StdName "n2"], True)] []
                ww3 = mkWorldState [(PPred "P" [StdName "n3"], True)] []
                -- Non-Euclidean model: ww1 -> ww2, ww1 -> ww3, but ww2 -/-> ww3
                nonEuclideanKr = KrM [ww1, ww2, ww3] trueAtomicPropsAt [(ww1, ww2), (ww1, ww3)]
                -- Non-transitive model: ww1 -> ww2 -> ww3, but ww1 -/-> ww3
                nonTransitiveKr = KrM [ww1, ww2, ww3] trueAtomicPropsAt [(ww1, ww2), (ww2, ww3)]
                -- Valid model but w not in universe
                validKr = KrM [ww1, ww2] trueAtomicPropsAt [(ww1, ww1), (ww1, ww2), (ww2, ww1), (ww2, ww2)]
                wOut = mkWorldState [(PPred "P" [StdName "n4"], True)] []

            it "returns Nothing for a non-Euclidean model" $ do
                isNothing (kripkeToKL nonEuclideanKr ww1) `shouldBe` True

            it "returns Nothing for a non-transitive model" $ do
                isNothing (kripkeToKL nonTransitiveKr ww1) `shouldBe` True

            it "returns Nothing when the world is not in the universe" $ do
                isNothing (kripkeToKL validKr wOut) `shouldBe` True

            it "returns Nothing iff not (isEuclidean && isTransitive) || not (isInUniv w univ) (property)" $
                property $ do
                    kr@(KrM univ _ _) <- genSmallRandomucKripke
                    w <- oneof ([elements univ | not (null univ)] ++ [genTransWorldState])
                    let result = kripkeToKL kr w
                        condition = not (isEuclidean kr && isTransitive kr) || not (isInUniv w univ)
                    return $ isNothing result <==> condition

        describe "convertToWorldStateModel" $ do
            let intModel = KrM [0, 1] (\w -> if w == 0 then [1] else [2]) [(0, 1)]
                expectedKr = KrM [makeWorldState 0, makeWorldState 1] 
                    (\w -> if w == makeWorldState 0 then [1] else [2]) 
                    [(makeWorldState 0, makeWorldState 1)]

            it "correctly converts an IntKripkeModel to a KripkeModel" $ do
                let converted = convertToWorldStateModel intModel
                universe converted `shouldBe` universe expectedKr
                all (\w -> valuation converted w == valuation expectedKr w) (universe converted) `shouldBe` True
                relation converted `shouldBe` relation expectedKr

            it "preserves structure in conversion (property)" $ 
                property $ do
                intKr <- genIntKripkeModel
                let kr = convertToWorldStateModel intKr
                    KrM intUniv intVal intRel = intKr
                    worldStates = map makeWorldState intUniv
                return $ length (universe kr) == length intUniv &&
                    relation kr == [(makeWorldState i, makeWorldState j) | (i, j) <- intRel] &&
                    all (\(i, w) -> valuation kr w == intVal i) (zip intUniv worldStates)

            it "produces distinct WorldStates for distinct integers (property)" $
                property $ do
                    n <- choose (0, 100)
                    m <- choose (0, 100) `suchThat` (/= n)
                    let ws1 = makeWorldState n
                        ws2 = makeWorldState m
                    return $ ws1 /= ws2

        describe "Show KripkeModel Integer" $ do
            let intModel = KrM [0::Integer, 1] (\w -> if w == 0 then [1] else [2]) [(0, 1)]
            it "shows KripkeModel Integer in expected format" $ do
                show intModel `shouldBe` "KrM\n[0,1]\n[(0,[1]),(1,[2])]\n[(0,1)]"

            it "consistently formats universe, valuation, and relation (property)" $
                property $ do
                    intKr@(KrM univ val rel) <- genIntKripkeModel
                    let expected = "KrM\n" ++ show univ ++ "\n" ++ show [(x, val x) | x <- univ] ++ "\n" ++ show rel
                    return $ show intKr == expected

        describe "Show KripkeModel WorldState" $ do
            let krModel = KrM [makeWorldState 0, makeWorldState 1] 
                            (\w -> if w == makeWorldState 0 then [1] else [2]) 
                            [(makeWorldState 0, makeWorldState 1)]
            it "shows KripkeModel WorldState via KripkeModel Integer conversion" $ do
                show (translateKrToKrInt krModel) `shouldBe` "KrM\n[0,1]\n[(0,[1]),(1,[2])]\n[(0,1)]"

            it "translating KripkeModel Integer to KripkeModel WorldState and back show the same model" $
                property $ do
                show (convertToWorldStateModel (translateKrToKrInt krModel)) `shouldBe` "KrM\n[WorldState {atomValues = fromList [(Pred \"WorldID\" [StdNameTerm (StdName \"0\")],True)], termValues = fromList []},WorldState {atomValues = fromList [(Pred \"WorldID\" [StdNameTerm (StdName \"1\")],True)], termValues = fromList []}]\n[(WorldState {atomValues = fromList [(Pred \"WorldID\" [StdNameTerm (StdName \"0\")],True)], termValues = fromList []},[1]),(WorldState {atomValues = fromList [(Pred \"WorldID\" [StdNameTerm (StdName \"1\")],True)], termValues = fromList []},[2])]\n[(WorldState {atomValues = fromList [(Pred \"WorldID\" [StdNameTerm (StdName \"0\")],True)], termValues = fromList []},WorldState {atomValues = fromList [(Pred \"WorldID\" [StdNameTerm (StdName \"1\")],True)], termValues = fromList []})]"

        describe "con" $ do
            it "computes conjunction as Neg (Dis (Neg f) (Neg g))" $ do
                con (P 1) (P 2) `shouldBe` Neg (Dis (Neg (P 1)) (Neg (P 2)))

            it "behaves like logical AND (property)" $
                property $ do
                kr <- genRandomKripkeModel
                f <- genModForm
                g <- genModForm
                let univ = universe kr
                return $ all (\w -> makesTrue (kr, w) (con f g) == (makesTrue (kr, w) f && makesTrue (kr, w) g)) univ

        describe "impl" $ do
            it "computes implication as Dis (Neg f) g" $ do
                impl (P 1) (P 2) `shouldBe` Dis (Neg (P 1)) (P 2)

            it "behaves like logical implication (property)" $
                property $ do
                kr <- genRandomKripkeModel
                f <- genModForm
                g <- genModForm
                let univ = universe kr
                return $ all (\w -> makesTrue (kr, w) (impl f g) == (not (makesTrue (kr, w) f) || makesTrue (kr, w) g)) univ


        describe "Translation (Propositional Modal Logic to KL)" $ do
            -- Helper functions
            let   
                -- Example models (completed)
                intW0, intW1, intW2 :: World Integer
                intW0 = 0; intW1 = 1; intW2 = 2
                intUniverse1 = [intW0, intW1, intW2]
                intValuation1 w | w == 0 || w == 1 = [1] | w == 2 = [] | otherwise = []
                intRelation1 = [(0, 0), (0, 1), (1, 0), (1, 1), (2, 2)]
                intModel1 = KrM intUniverse1 intValuation1 intRelation1
                exampleModel1 = convertToWorldStateModel intModel1

                intW20, intW21, intW22 :: World Integer
                intW20 = 20; intW21 = 21; intW22 = 22
                intUniverse2 = [intW20, intW21, intW22]
                intValuation2 w | w == 20 = [1] | w == 21 = [] | w == 22 = [1] | otherwise = []
                intRelation2 = [(20, 21), (21, 22)]
                intModel2 = KrM intUniverse2 intValuation2 intRelation2
                exampleModel2 = convertToWorldStateModel intModel2

                intW30, intW31, intW32 :: World Integer
                intW30 = 30; intW31 = 31; intW32 = 32
                intUniverse3 = [intW30, intW31, intW32]
                intValuation3 w | w == 30 = [1] | otherwise = []
                intRelation3 = [(w1, w2) | w1 <- intUniverse3, w2 <- intUniverse3]
                intModel3 = KrM intUniverse3 intValuation3 intRelation3
                exampleModel3 = convertToWorldStateModel intModel3

                intW40, intW41, intW42 :: World Integer
                intW40 = 40; intW41 = 41; intW42 = 42
                intUniverse4 = [intW40, intW41, intW42]
                intValuation4 w | w == 40 = [1] | w == 41 = [] | w == 42 = [2] | otherwise = []
                intRelation4 = []
                intModel4 = KrM intUniverse4 intValuation4 intRelation4
                exampleModel4 = convertToWorldStateModel intModel4

                intW50, intW51, intW52 :: World Integer
                intW50 = 50; intW51 = 51; intW52 = 52
                intUniverse5 = [intW50, intW51, intW52]
                intValuation5 w | w == 50 = [1, 2] | w == 51 = [1] | w == 52 = [] | otherwise = []
                intRelation5 = [(50, 51), (51, 52), (52, 50)]
                intModel5 = KrM intUniverse5 intValuation5 intRelation5
                exampleModel5 = convertToWorldStateModel intModel5

                intW60, intW61, intW62, intW63, intW64 :: World Integer
                intW60 = 60; intW61 = 61; intW62 = 62; intW63 = 63; intW64 = 64
                intUniverse6 = [intW60, intW61, intW62, intW63, intW64]
                intValuation6 w | w == 60 = [1] | w == 61 = [1, 2] | w == 62 = [] | w == 63 = [2] | w == 64 = [1, 2] | otherwise = []
                intRelation6 = let cluster1 = [60, 61, 62]; cluster2 = [63, 64]
                            in [(w1, w2) | w1 <- cluster1, w2 <- cluster1] ++ [(w1, w2) | w1 <- cluster2, w2 <- cluster2]
                intModel6 = KrM intUniverse6 intValuation6 intRelation6
                exampleModel6 = convertToWorldStateModel intModel6

                intW70, intW71, intW72, intW73, intW74, intW75 :: World Integer
                intW70 = 70; intW71 = 71; intW72 = 72; intW73 = 73; intW74 = 74; intW75 = 75
                intUniverse7 = [intW70, intW71, intW72, intW73, intW74, intW75]
                intValuation7 w | w == 70 = [1] | w == 71 = [1, 2] | w == 72 = [2] | w == 73 = [] | w == 74 = [1] | w == 75 = [1, 2] | otherwise = []
                intRelation7 = let cluster = [71, 72, 73, 74, 75]
                            in [(70, w) | w <- cluster] ++ [(w1, w2) | w1 <- cluster, w2 <- cluster]
                intModel7 = KrM intUniverse7 intValuation7 intRelation7
                exampleModel7 = convertToWorldStateModel intModel7

                modelKL7 = fromJust (kripkeToKL exampleModel7 (makeWorldState 70))
                modelKL7b = fromJust (kripkeToKL exampleModel7 (makeWorldState 71))
                ref = translateFormToKL (impl (Box (P 99)) (P 99))

                smallModels :: [KripkeModel WorldState]
                smallModels = [exampleModel1, exampleModel2, exampleModel3, exampleModel4, exampleModel5, exampleModel6, exampleModel7]


            it "translates atomic proposition P 1 correctly" $ do
                translateFormToKL (P 1) `shouldBe` Atom (Pred "P" [StdNameTerm (StdName "n1")])

            it "translates negation Neg (P 1) correctly" $ do
                translateFormToKL (Neg (P 1)) `shouldBe` Not (Atom (Pred "P" [StdNameTerm (StdName "n1")]))

            it "translates conjunction con (P 1) (P 2) correctly" $ do
                translateFormToKL (con (P 1) (P 2)) `shouldBe` 
                    Not (Or (Not (Atom (Pred "P" [StdNameTerm (StdName "n1")]))) 
                            (Not (Atom (Pred "P" [StdNameTerm (StdName "n2")]))))

            it "translates box operator Box (P 1) correctly" $ do
                translateFormToKL (Box (P 1)) `shouldBe` K (Atom (Pred "P" [StdNameTerm (StdName "n1")]))

            it "translates diamond operator dia (P 1) correctly" $ do
                translateFormToKL (dia (P 1)) `shouldBe` 
                    Not (K (Not (Atom (Pred "P" [StdNameTerm (StdName "n1")]))))

            it "ensures invertibility of simple formula Box (P 1) using equivalence" $ do
                let g = Box (P 1)
                    klForm = translateFormToKL g
                    selForm = fromJust (translateFormToKr klForm)
                areEquivalent smallModels g selForm `shouldBe` True

            it "ensures invertibility of complex formula Box (con (P 1) (Neg (P 2))) using equivalence" $ do
                let g = Box (con (P 1) (Neg (P 2)))
                    klForm = translateFormToKL g
                    selForm = fromJust (translateFormToKr klForm)
                areEquivalent smallModels g selForm `shouldBe` True

        
            it "translation succeeds for S5 model (exampleModel3)" $ do
                isJust (kripkeToKL exampleModel3 (makeWorldState 30)) `shouldBe` True

            it "translation succeeds for clustered model (exampleModel6)" $ do
                isJust (kripkeToKL exampleModel6 (makeWorldState 60)) `shouldBe` True

            it "translation fails for linear non-transitive model (exampleModel2)" $ do
                isNothing (kripkeToKL exampleModel2 (makeWorldState 20)) `shouldBe` True

            it "translation fails for cyclic non-transitive model (exampleModel5)" $ do
                isNothing (kripkeToKL exampleModel5 (makeWorldState 50)) `shouldBe` True

            it "preserves truth for atomic proposition P 1 in S5 model (exampleModel3)" $ do
                testTruthPres exampleModel3 (makeWorldState 30) (P 1) `shouldBe` Just True

            it "preserves truth for box operator Box (P 1) in S5 model (exampleModel3)" $ do
                testTruthPres exampleModel3 (makeWorldState 30) (Box (P 1)) `shouldBe` Just True

            it "preserves truth for diamond operator dia (P 1) in S5 model (exampleModel3)" $ do
                testTruthPres exampleModel3 (makeWorldState 30) (dia (P 1)) `shouldBe` Just True

            it "preserves truth for conjunction con (P 1) (P 2) in clustered model (exampleModel6)" $ do
                testTruthPres exampleModel6 (makeWorldState 60) (con (P 1) (P 2)) `shouldBe` Just True

            it "verifies contradiction is false in modelKL7" $ do
                not (checkModel modelKL7 (translateFormToKL (con (P 2) (Neg (P 2))))) `shouldBe` True

            it "verifies reflexivity axiom true in modelKL7b (w71 in cluster)" $ do
                checkModel modelKL7b ref `shouldBe` True
            
            it "always creates an empty domain" $ do
                 domain (fromJust (kripkeToKL exampleModel3 (makeWorldState 30))) `shouldBe` Set.empty

areEquivalent :: (Eq a, Ord a) => [KripkeModel a] -> ModForm -> ModForm -> Bool
areEquivalent models f1 f2 = 
    all (\m -> all (\w -> makesTrue (m, w) f1 == makesTrue (m, w) f2) (universe m)) models

testTruthPres :: KripkeModel WorldState -> WorldState -> ModForm -> Maybe Bool
testTruthPres km w g = 
    case kripkeToKL km w of
    Nothing -> Nothing
    Just klModel -> Just $ makesTrue (km, w) g == satisfiesModel klModel (translateFormToKL g)

dia :: ModForm -> ModForm
dia f = Neg (Box (Neg f))


(<==>) :: Bool -> Bool -> Bool
(<==>) p q = (p && q) || (not p && not q)
\end{code}