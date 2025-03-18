

\section{Syntax of $\mathcal{KL}$}\label{subsec:KLsyntax}
The syntax of the language $\mathcal{KL}$ is described in \textcite{Lokb} and inspired by Levesque's work (\cite{levesque1981}).
The SyntaxKL module establishes the foundation for $\mathcal{KL}$'s syntax, defining the alphabet and grammar used in subsequent semantic evaluation.
\begin{code}
{-# LANGUAGE InstanceSigs #-}


module SyntaxKL where

import Test.QuickCheck

\end{code}

\textbf{Symbols of $\mathcal{KL}$}\\
The expressions of $\mathcal{KL}$ are constituted by sequences of symbols drawn from the following two sets (cf. \cite{levesque1981}): 
Firstly, the \textit{logical symbols}, which consist of the logical connectives and quantifiers $\exists, \vee, \neg$, as well as punctuation and parentheses.
Furthermore, it compromises a countably infinite supply of first-order variables  denoted by the set $\{x, y, z, \ldots\}$, a countably infinite supply of standard names, represented by the set $\{\#1, \#2,\ldots\}$, and the equality symbol =. 
The \textit{non-logical symbols} comprise predicate symbols of any arity $\{P, Q, R, \ldots\}$, which are intended to represent domain-specific properties and relations, and function symbols of any arity, which are used to denote mappings from individuals to individuals (\cite{Lokb}, p.22). \\
n this implementation, standard names are represented as strings (e.g., "n1", "n2") via the StdName type, and variables are similarly encoded as strings (e.g., $"x"$, $"y"$) with the Variable type, ensuring that we have a distinct yet infinite supplies of each.

\begin{code}
-- Represents a standard name (e.g., "n1") from the infinite domain N
newtype StdName = StdName String deriving (Eq, Ord, Show)

-- Represents a first-order variable (e.g., "x")
newtype Variable = Var String deriving (Eq, Ord, Show)
\end{code}

\textbf{Terms and Atoms}\\
Terms in $\mathcal{KL}$ are the building blocks of expressions, consisting of variables, standard names, or function applications. 
Atomic propositions (atoms) are formed by applying predicate symbols to lists of terms. 
To distinguish primitive terms (those that contain no variable and only a single function symbol) and primitive atoms (those atoms that contain no variables and only standard names as terms) for semantic evaluation, we also define PrimitiveTerm and PrimitiveAtom.

\begin{code}
-- Defines terms: variables, standard names, or function applications
data Term = VarTerm Variable   -- A variable (e.g., "x")
          | StdNameTerm StdName   -- A standard name (e.g., "n1")
          | FuncAppTerm String [Term]   -- Function application (e.g., "Teacher" ("x"))
          deriving (Eq, Ord, Show)

-- Terms with no variables and only a single function symbol
data PrimitiveTerm = PStdNameTerm StdName   -- e.g., "n1"
                    | PFuncAppTerm String [StdName]     
  deriving (Eq, Ord, Show)

-- Define Atoms as predicates applied to terms
data Atom = Pred String [Term]  --e.g. "Teach" ("n1", "n2")
  deriving (Eq, Ord, Show)

-- Atoms with only standard names as terms
data PrimitiveAtom = PPred String [StdName]
  deriving (Eq, Ord, Show)

\end{code}

\textbf{Formulas}\\
$\mathcal{KL}$-formulas are constructed recursively from atoms, equality, and logical operators. 
The Formula type includes atomic formulas, equality between terms, negation, disjunction, existential quantification, and the knowledge operator $K$. 
Additional connectives like universal quantification ($\forall$), implication ($\rightarrow$), and biconditional ($\leftrightarrow$) are defined as derived forms for convenience.

\begin{code}
--Defines KL-formulas with logical and epistemic constructs
data Formula = Atom Atom                -- Predicate (e.g. Teach(x, "n1"))
              | Equal Term Term         -- Equality (e.g., x = "n1")
              | Not Formula             -- Negation 
              | Or Formula Formula      -- Disjunction
              | Exists Variable Formula -- Existential (e.g., exists x (Teach x "sue")) 
              | K Formula               -- Knowledge Operator (e.g., K (Teach "ted" "sue"))
              deriving (Show)

-- Universal quantifier as derived form
for_all :: Variable -> Formula -> Formula
for_all x f = Not (Exists x (Not f))

-- Implication as derived form
implies :: Formula -> Formula -> Formula
implies f1 f2 = Or (Not f1) f2

-- Biconditional as derived form
iff :: Formula -> Formula -> Formula
iff f1 f2 = Or (Not (Or f1 f2)) (Or (Not f1) f2)
\end{code}

We can now use this implementation of $\mathcal{KL}$'s syntax to implement the semantics.

\begin{code}
instance Arbitrary StdName where
  arbitrary:: Gen StdName
  arbitrary = StdName . ("n" ++) . show <$> elements [1 .. 20::Int]

instance Arbitrary Variable where
  arbitrary:: Gen Variable
  arbitrary = Var . show <$> elements [1 .. 20::Int]

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
                                   <*> resize (n `div` 2) (listOf1 (genTerm (n `div` 2)))]

instance Arbitrary Atom where
  arbitrary :: Gen Atom
  arbitrary = sized $ \n -> genAtom (min n 5) where 
      genAtom :: Int -> Gen Atom
      genAtom 0 = Pred <$> arbitraryLowerLetter <*> pure []
      genAtom n = Pred <$> arbitraryLowerLetter <*> vectorOf n arbitrary

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