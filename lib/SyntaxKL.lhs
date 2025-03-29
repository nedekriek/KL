

\subsection{Syntax of \texorpdfstring{$\mathcal{KL}$}{KL}}\label{subsec:KLsyntax}

The syntax of the language $\mathcal{KL}$ is described in \textcite{Lokb} and was first developed by Levesque (\cite{levesque1981}).
The \verb?SyntaxKL? module establishes the foundation for $\mathcal{KL}$'s syntax, defining the alphabet and grammar used in subsequent semantic evaluation.
\begin{code}
{-# LANGUAGE InstanceSigs #-}
module SyntaxKL where
import Test.QuickCheck
\end{code}

\textbf{Symbols of $\mathcal{KL}$}\\
The language \(\mathcal{KL}\) is built on the following alphabet:
\begin{itemize}
    \item \textbf{Variables}: \(x, y, z, \ldots\) (an infinite set).
    \item \textbf{Constants}: \(c, d, n1, n2, \ldots\) (including standard names).
    \item \textbf{Function symbols}: \(f, g, h, \ldots\) (with associated arities).
    \item \textbf{Predicate symbols}: \(P, Q, R, \ldots\) (with associated arities).
    \item \textbf{Logical symbols}: \(\neg, \vee, \exists, =, $\mathbf{K}$, (, )\).
\end{itemize}
In this our implementation, standard names are represented as strings (e.g., "n1", "n2") via the \verb?StdName? type, and variables are similarly encoded as strings (e.g., "x", "y") with the \verb?Variable? type, ensuring that we have a distinct yet infinite supplies of each.

\begin{code}
--TODO hide
arbitraryUpperLetter :: Gen String
arbitraryUpperLetter = (:[]) <$> elements ['A'..'Z']
--TODO hide
arbitraryLowerLetter :: Gen String
arbitraryLowerLetter = (:[]) <$> elements ['a'..'z']

-- Represents a standard name (e.g., "n1") from the infinite domain N
newtype StdName = StdName String deriving (Eq, Ord, Show)

--TODO hide
instance Arbitrary StdName where
  arbitrary:: Gen StdName
  arbitrary = StdName . ("n" ++) . show <$> elements [1 .. 20::Int]

-- Represents a first-order variable (e.g., "x")
newtype Variable = Var String deriving (Eq, Ord, Show)

--TODO hide
instance Arbitrary Variable where
  arbitrary:: Gen Variable
  arbitrary = Var . show <$> elements [1 .. 20::Int]

\end{code}

\textbf{Terms, Atoms, and Formulas}\\
The syntax of \(\mathcal{KL}\) is defined recursively in Backus-Naur Form as follows:\\
Terms represent objects in the domain:
\begin{verbatim}
<term> ::= <variable> | <constant> | <function-term>
<variable> ::= "x" | "y" | "z" | ...
<constant> ::= "c" | "d" | "n1" | "n2" | ...
<function-term> ::= <function-symbol> "(" <term-list> ")"
<function-symbol> ::= "f" | "g" | "h" | ...
<term-list> ::= <term> | <term> "," <term-list>
\end{verbatim}

Well-formed formulas (wffs) define the logical expressions:
\begin{verbatim}
<wff> ::= <atomic-wff> | <negated-wff> | <disjunction-wff> | 
          <existential-wff> | <knowledge-wff>
<atomic-wff> ::= <predicate> | <equality>
<predicate> ::= <predicate-symbol> "(" <term-list> ")"
<predicate-symbol> ::= "P" | "Q" | "R" | ...
<equality> ::= <term> "=" <term>
<negated-wff> ::= "\not" <wff>
<disjunction-wff> ::= "(" <wff> "\lor" <wff> ")"
<existential-wff> ::= "\exists" <variable> "." <wff>
<knowledge-wff> ::= "K" <wff>
\end{verbatim}

Predicate and function symbols have implicit arities, abstracted here for generality.
Furthermore, the epistemic operator \(\mathbf{K}\) allows nested expressions, e.g., \(\mathbf{K} \neg \mathbf{K} P(x)\).\\
Sentences of $\mathcal{KL}$ can look like this:
\begin{itemize}
    \item \(Teach(ted, sue)\):\\
    \verb?<wff> -> <atomic-wff> -> <predicate> -> "Teach" "(" "ted" "," "sue" ")"?
    \item \(\boldsymbol{K} \exists x . Teach(x, sam)\):
    \begin{verbatim}
    <wff> -> <knowledge-wff> -> "K" <wff>
          -> "K" <existential-wff> → "K" "\exists" "x" "." <wff>
          -> "K" "\exists" "x" "." "Teach" "(" "x" "," "sam" ")"
    \end{verbatim}
    \item \(\neg \boldsymbol{K} Teach(tina, sue)\):
    \begin{verbatim}
    <wff> -> <negated-wff> -> "\neg" <wff>
          -> "\neg" <knowledge-wff> -> "\neg" "K" <wff>
          -> "\neg" "K" "Teach" "(" "tina" "," "sue" ")"
    \end{verbatim}
\end{itemize}
To distinguish primitive terms (those that contain no variable and only a single function symbol) and primitive atoms (those atoms that contain no variables and only standard names as terms) for semantic evaluation, we also define \verb?PrimitiveTerm? and \verb?PrimitiveAtom?.

\begin{code}
-- Defines terms: variables, standard names, or function applications
data Term = VarTerm Variable   -- A variable (e.g., "x")
          | StdNameTerm StdName   -- A standard name (e.g., "n1")
          | FuncAppTerm String [Term]   -- Function application (e.g., "Teacher" ("x"))
          deriving (Eq, Ord, Show)

--TODO hide
instance Arbitrary Term where
  arbitrary :: Gen Term
  arbitrary = sized $ \n -> genTerm (min n 5) where 
    genTerm 0 = oneof [VarTerm <$> arbitrary, 
                       StdNameTerm <$> arbitrary]
    genTerm n = oneof [VarTerm <$> arbitrary, 
                       StdNameTerm <$> arbitrary, 
                       FuncAppTerm <$> arbitraryLowerLetter 
                                   <*> resize (n `div` 2) (listOf1 (genTerm (n `div` 2)))]

-- Terms with no variables and only a single function symbol
data PrimitiveTerm = PStdNameTerm StdName   -- e.g., "n1"
                    | PFuncAppTerm String [StdName]     
  deriving (Eq, Ord, Show)

-- Define Atoms as predicates applied to terms
data Atom = Pred String [Term]  --e.g. "Teach" ("n1", "n2")
  deriving (Eq, Ord, Show)

--TODO hide
instance Arbitrary Atom where
  arbitrary :: Gen Atom
  arbitrary = sized $ \n -> genAtom (min n 5) where 
      genAtom :: Int -> Gen Atom
      genAtom 0 = Pred <$> arbitraryLowerLetter <*> pure []
      genAtom n = Pred <$> arbitraryLowerLetter <*> vectorOf n arbitrary

-- Atoms with only standard names as terms
data PrimitiveAtom = PPred String [StdName]
  deriving (Eq, Ord, Show)

--Defines KL-formulas with logical and epistemic constructs
data Formula = Atom Atom                -- Predicate (e.g. Teach(x, n1))
              | Equal Term Term         -- Equality (e.g., x = n1)
              | Not Formula             -- Negation 
              | Or Formula Formula      -- Disjunction
              | Exists Variable Formula -- Existential (e.g., exists x (Teach x sue)) 
              | K Formula               -- Knowledge Operator (e.g., K (Teach ted sue))
              deriving (Eq, Ord, Show)

--TODO hide
instance Arbitrary Formula where
  arbitrary :: Gen Formula 
  arbitrary = sized $ \n -> genFormula (min n 5)   where
    genFormula 0 = oneof [Atom <$> arbitrary, 
                          Equal <$> arbitrary <*> arbitrary]
    genFormula n = oneof [Not <$> genFormula (n `div` 2),
                          Or <$> genFormula (n `div` 2) <*> genFormula (n `div` 2),
                          Exists <$> arbitrary <*> genFormula (n `div` 2),
                          K <$> genFormula (n `div` 2)]
                          
-- Universal quantifier as derived form
klforall :: Variable -> Formula -> Formula
klforall x f = Not (Exists x (Not f))

-- Implication as derived form
implies :: Formula -> Formula -> Formula
implies f1 = Or (Not f1)

-- Biconditional as derived form
iff :: Formula -> Formula -> Formula
iff f1 f2 = Or (Not (Or f1 f2)) (Or (Not f1) f2)
\end{code}

We can now use this implementation of $\mathcal{KL}$'s syntax to implement the semantics.
