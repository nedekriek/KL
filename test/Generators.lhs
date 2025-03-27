\begin{code}
{-# LANGUAGE InstanceSigs #-}

module Generators where

import SyntaxKL
import SemanticsKL
import Translator

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Test.QuickCheck
\end{code}

This file contains helper generators, used only in testing. 
s
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
genSmallTransEucKripke :: Gen KripkeModel
genSmallTransEucKripke = resize 6 genTransEucKripke

-- Generator for transitive and Euclidean Kripke models
genTransEucKripke :: Gen KripkeModel
genTransEucKripke = sized randomModel where
    randomModel :: Int -> Gen KripkeModel
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

transEucClosure :: Eq a => [(a,a)] -> [(a,a)]
transEucClosure relation
    | relation == closure   = relation
    | otherwise             = transEucClosure closure where
    closure = nub $ relation ++ [(a,c) | (a,b) <- relation, (b',c) <- relation, b == b'] ++ [(b,c) | (a,b) <- relation, (a',c) <- relation, a == a']

-- Generator, which, given a KripkeModel, picks a world
genWorldFrom :: KripkeModel -> Gen World
genWorldFrom m = elements (universe m)

-- Generator for a pair consisting of a transitive, Euclidean model, and a world in that model
genTransEucKripkeWithWorld :: Gen (KripkeModel, World)
genTransEucKripkeWithWorld = do
  m <- genSmallTransEucKripke
  w <- genWorldFrom m
  return (m, w)

\end{code}