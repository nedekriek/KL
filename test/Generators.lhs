\begin{code}
{-# LANGUAGE InstanceSigs #-}

module Generators where

import SyntaxKL
import Tableau
import Data.Set (Set)
import qualified Data.Set as Set
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

generateListOfNodes :: IO [Node]
generateListOfNodes = generate $ listOf arbitrary

{-}
instance Arbitrary Node where
    arbitrary = do
        f <- genGroundFormula
        w <- choose (0, 5) :: Gen Int
        return $ Node f w

instance Arbitrary Branch where
    arbitrary = do
        ns <- resize 5 (listOf arbitrary) :: Gen [Node] -- Limit to 0-5 nodes
        ps <- genStdNameSet
        ks <- resize 5 (listOf arbitrary) :: Gen [Node] -- Generate a list of Nodes for keeps
        return $ Branch ns ps ks
-}
\end{code}