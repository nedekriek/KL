\subsection{Syntax}
\begin{code}
module SyntaxKL where
\end{code}

We represent standard names as strings (e.g., "n1", "n2", ...) and have (in theory) an infinite amount of them. 
We also define a newtype Variable, which we also represent as strings.

\begin{code}
newtype StdName = StdName String deriving (Eq, Ord, Show)

newtype Variable = Var String deriving (Eq, Ord, Show)
\end{code}

Terms are variables, standard names, or function applications,
Atomic propositions are predicates applied to terms.

\begin{code}
data Term = VarTerm Variable
          | StdNameTerm StdName
          | FuncApp String [Term]
          deriving (Eq, Ord, Show)

data Atom = Pred String [Term] deriving (Eq, Ord, Show)
\end{code}

Based on this, we can now define $\mathcal{KL}$-formulas:
\begin{code}
data Formula = Atom Atom                -- Predicate (e.g. Teach(x, "n1"))
              | Equal Term Term         --Equality (e.g., x = "n1")
              | Not Formula             -- Negation 
              | Or Formula Formula      -- Disjunction
              | Exists Variable Formula -- Existential (e.g., exists x (Teach x "sue")) TODO
              | K Formula               -- Knowledge Operator (e.g., K (Teach "ted" "sue"))
              deriving (Show)

-- TODO: model forall, rightarrow, leftrightarrow
\end{code}