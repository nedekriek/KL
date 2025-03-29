\vspace{10pt}
\begin{code}
{-# LANGUAGE InstanceSigs #-}

module Generators where

import SyntaxKL (Term(..), Atom(..), Formula(..), StdName)
import SemanticsKL
import Translator

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List
import qualified Data.Map as Map
import Test.QuickCheck
\end{code}

This file contains helper generators, used only in testing. 
s
\vspace{10pt}
\begin{code}
-- Generator for arbitrary upper case letter
genUpper :: Gen String
genUpper = (:[]) <$> elements ['A'..'Z']

-- Generator for arbitrary lower case letter
genLower :: Gen String
genLower = (:[]) <$> elements ['a'..'z']

-- Generator for ground terms
genGroundTerm :: Gen Term
genGroundTerm = sized genTerm
    where
        genTerm 0 = StdNameTerm <$> arbitrary
        genTerm n = oneof [StdNameTerm <$> arbitrary, 
                           FuncAppTerm <$> genLower <*> resize (n `div` 2) (listOf genGroundTerm)]

-- Generator for ground Atoms
genGroundAtom :: Gen Atom
genGroundAtom = Pred <$> genUpper<*> listOf genGroundTerm

-- Generator for ground formulas
genGroundFormula :: Gen Formula
genGroundFormula = sized genFormula
    where
        genFormula 0 = Atom <$> genGroundAtom
        genFormula n = oneof [ Atom <$> genGroundAtom
                             , Equal <$> genGroundTerm <*> genGroundTerm
                             , Not <$> genFormula (n `div` 2)
                             , Or <$> genFormula (n `div` 2) <*> genFormula (n `div` 2)
                             , K <$> genFormula (n `div` 2)
                             ]

-- Generator for a set of StdName values
genStdNameSet :: Gen (Set StdName)
genStdNameSet = sized $ \n -> do
  let m = min n 5
  size <- choose (0, m)
  Set.fromList <$> vectorOf size arbitrary

-- Helper Generator for atoms of the form 'P(standardname)'
genPAtom :: Gen Atom
genPAtom =  do
  n <- arbitrary
  return (Pred "P" [StdNameTerm n])

-- Generator for KL-formulas that can be translated
genTransFormula :: Gen Formula
genTransFormula = sized genTrForm
    where
        genTrForm 0 = Atom <$> genPAtom
        genTrForm n = oneof [ Atom <$> genPAtom
                             , Not <$> genTrForm (n `div` 2)
                             , Or <$> genTrForm (n `div` 2) <*> genTrForm (n `div` 2)
                             , K <$> genTrForm (n `div` 2)
                             ]


-- Generator for SEL-Formulae
genModForm :: Gen ModForm
genModForm = sized genFormula
  where
    genFormula :: Int -> Gen ModForm
    genFormula 0 = P <$> choose (1, 5)  -- Base case: atomic proposition
    genFormula n = frequency
      [ (2, P <$> choose (1, 5))                  -- Atomic proposition 
      , (1, Neg <$> genFormula (n `div` 2))       -- Negation
      , (1, Dis <$> genFormula (n `div` 2)        -- Disjunction
                <*> genFormula (n `div` 2))
      , (1, Box <$> genFormula (n `div` 2))       -- Box operator
      ]

-- Generator for WorldStates at which only propositions of the form 'P(standardname)' are true
genTransWorldState ::Gen WorldState
genTransWorldState = do
    let m = 5 
    atoms <- vectorOf m genPAtom `suchThat` (\xs -> nub xs == xs)
    tvs <- vectorOf m arbitrary
    let atValues' = zip atoms tvs
    let atValues = Map.fromList $ checkDups atValues'
    WorldState atValues <$> arbitrary

-- Generator for smaller transitive and Euclidean Kripke models
genSmallTransEucKripke :: Gen (KripkeModel WorldState)
genSmallTransEucKripke = resize 6 genTransEucKripke

-- Generator for transitive and Euclidean Kripke models
genTransEucKripke :: Gen (KripkeModel WorldState)
genTransEucKripke = sized randomModel where
    randomModel :: Int -> Gen (KripkeModel WorldState)
    randomModel n = do
      msize <- choose (1, 1+n)
      u <- nub . sort <$> vectorOf msize genTransWorldState
      let v = trueAtomicPropsAt
      r' <- if null u 
        then return []
        else listOf $ do 
          x <- elements u
          y <- elements u
          return (x,y)
      let r = transEucClosure r'
      return (KrM u v r)

-- Generator for arbitrary world state Kripke models
genRandomKripkeModel :: Gen (KripkeModel WorldState)
genRandomKripkeModel = sized randomModel where
    randomModel :: Int -> Gen (KripkeModel WorldState)
    randomModel n = do
      msize <- choose (1, 1+n)
      u <- nub . sort <$> vectorOf msize genTransWorldState
      let v = trueAtomicPropsAt
      r' <- if null u 
        then return []
        else listOf $ do 
          x <- elements u
          y <- elements u
          return (x,y)
      return (KrM u v r')

genSmallRandomucKripke :: Gen (KripkeModel WorldState)
genSmallRandomucKripke = resize 6 genRandomKripkeModel


genIntKripkeModel :: Gen (KripkeModel Integer)
genIntKripkeModel = do
  n <- choose (1, 6::Integer)  -- Small universe for simplicity
  let univ = [0 .. n-1]
  val <- vectorOf (fromInteger n) (sublistOf [1..4]) >>= \props -> return $ \w -> props !! fromInteger w
  rel <- sublistOf [(w, w') | w <- univ, w' <- univ]
  return $ KrM univ val rel

transEucClosure :: Eq a => [(a,a)] -> [(a,a)]
transEucClosure rela
    | rela == closure   = rela
    | otherwise             = transEucClosure closure where
    closure = nub $ rela ++ [(a,c) | (a,b) <- rela, (b',c) <- rela, b == b'] ++ [(b,c) | (a,b) <- rela, (a',c) <- rela, a == a']

-- Generator, which, given a KripkeModel, picks a world
genWorldFrom :: (KripkeModel a) -> Gen (World a)
genWorldFrom m = elements (universe m)

-- Generator for a pair consisting of a transitive, Euclidean model, and a world in that model
genTransEucKripkeWithWorld :: Gen (KripkeModel WorldState, World WorldState)
genTransEucKripkeWithWorld = do
  m <- genSmallTransEucKripke
  w <- genWorldFrom m
  return (m, w)

\end{code}