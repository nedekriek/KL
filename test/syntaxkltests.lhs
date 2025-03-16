\section{Syntax Tests}

\begin{code}
{-# LANGUAGE InstanceSigs #-}

module Main where

import SyntaxKL

import Test.Hspec
import Test.QuickCheck
\end{code}

\begin{code}
main :: IO ()
main = hspec $ do
  describe "Eq is derived for the relevant KL Syntax" $ do
    it "StdName Eq is derived" $ do
      property $ \n -> StdName n == StdName n
    it "Variable Eq is derived" $ do
      property $ \n -> Var n == Var n
    it "Term Eq is derived" $ do
      property $ \t -> FuncAppTerm "f" t == FuncAppTerm "f" t
    it "FuncAppTerm is not equal to VarTerm" $ do
      property $ \v t -> FuncAppTerm "f" (t :: [Term]) /= VarTerm (v :: Variable)
    it "FuncAppTerm is not equal to StdNameTerm" $ do
      property $ \s t -> FuncAppTerm "f" (t :: [Term]) /= StdNameTerm (s :: StdName)
    it "VarTerm is not equal to StdNameTerm" $ do
      property $ \v s -> VarTerm (v :: Variable) /= StdNameTerm (s :: StdName)
    it "Atom Eq is derived" $ do
      property $ \a -> a == (a :: Atom)
\end{code}
 
 