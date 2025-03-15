\section{KL Generators}

\begin{code}
{-# LANGUAGE InstanceSigs #-}

module Main where

import SyntaxKL
import SemanticsKL

import Test.Hspec
import Test.QuickCheck
\end{code}

-- TODO: move to be defined where the type is defined. 
-- TODO: work out acceptable sizes for generated artifacts 

--Syntax
\begin{code}
instance Arbitrary StdName where
  arbitrary:: Gen StdName
  arbitrary = StdName . ("n" ++) . show <$> elements [1 .. 20]

instance Arbitrary Variable where
  arbitrary:: Gen Variable
  arbitrary = Var . show <$> elements [1 .. 20]

arbitraryUpperLetter :: Gen String
arbitraryUpperLetter = (:[]) <$> elements ['A'..'Z']

arbitraryLowerLetter :: Gen String
arbitraryLowerLetter = (:[]) <$> elements ['a'..'z']

instance Arbitrary Term where
  arbitrary :: Gen Term
  arbitrary = sized $ \n -> genTerm (min n 5) where 
    genTerm 0 = oneof [VarTerm <$> arbitrary, 
                       StdNameTerm <$> arbitrary]
    genTerm n = oneof [VarTerm <$> arbitrary, 
                       StdNameTerm <$> arbitrary, 
                       FuncAppTerm <$> arbitraryLowerLetter 
                                   <*> resize (n `div` 2) (listOf (genTerm (n `div` 2)))]

instance Arbitrary Atom where
  arbitrary :: Gen Atom
  arbitrary = sized $ \n -> genAtom (min n 5) where 
      genAtom :: Int -> Gen Atom
      genAtom n = Pred <$> arbitraryLowerLetter <*> vectorOf n  arbitrary

instance Arbitrary Formula where
  arbitrary :: Gen Formula 
  arbitrary = sized $ \n -> genFormula (min n 5)   where
    genFormula 0 = oneof [Atom <$> arbitrary, 
                          Equal <$> arbitrary <*> arbitrary]
    genFormula n = oneof [Not <$> genFormula (n `div` 2),
                          Or <$> genFormula (n `div` 2) <*> genFormula (n `div` 2),
                          Exists <$> arbitrary <*> genFormula (n `div` 2),
                          K <$> genFormula (n `div` 2)]
\end{code}

-- Semantics
\begin{code}
instance Arbitrary WorldState where
  arbitrary :: Gen WorldState
  arbitrary = WorldState <$> arbitrary <*> arbitrary

instance Arbitrary Model where 
  arbitrary:: Gen Model 
  arbitrary = Model <$> arbitrary <*> arbitrary <*> arbitrary
\end{code}


\begin{code}
main :: IO ()
main = do
  stdName <- generate (arbitrary :: Gen StdName)
  var <- generate (arbitrary :: Gen Variable)
  term <- generate (arbitrary :: Gen Term)
  at <- generate (arbitrary :: Gen Atom)
  ws <- generate (arbitrary :: Gen WorldState)
  m <- generate (arbitrary :: Gen Model)
  form <- generate (arbitrary :: Gen Formula)
  putStrLn (show stdName)
  putStrLn  (show var)
  putStrLn (show term)
  putStrLn (show at)
  putStrLn (show ws)
  putStrLn (show m)
  putStrLn (show form)
  
  return ()
\end{code}