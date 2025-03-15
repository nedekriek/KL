{-# LANGUAGE InstanceSigs #-}
\subsection{Syntax}
\begin{code}
module SyntaxKL where
\end{code}

The expressions of $\mathcal{KL}$ are constituted by sequences of symbols drawn from the following two sets (cf. \cite{levesque}): 
Firstly, the logical symbols, which consist of the logical connectives and quantifiers $\exists, \vee, \neg$, as well as punctuation and parentheses.
Furthermore, it compromises a countably infinite supply of first-order variables, denoted by the set $\{x, y, z,…\}$, a countably infinite supply of standard names, represented by the set $\{\#1, \#2, …\}$, and the equality symbol =. 
The second set is that of the non-logical symbols. It includes predicate symbols of any arity $\{P, Q, R ...\}$, which are intended to represent domain-specific properties and relations. 
Additionally, it contains function symbols of any arity, which are used to denote mappings from individuals to individuals. 


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
          deriving (Show)

instance Eq Term where
  VarTerm v1 == VarTerm v2 = v1 == v2
  StdNameTerm n1 == StdNameTerm n2 = n1 == n2
  FuncApp f1 ts1 == FuncApp f2 ts2 = f1 == f2 && ts1 == ts2
  _ == _ = False

instance Ord Term where
  compare (VarTerm v1) (VarTerm v2) = compare v1 v2
  compare (VarTerm _) _ = LT
  compare _ (VarTerm _) = GT
  compare (StdNameTerm n1) (StdNameTerm n2) = compare n1 n2
  compare (StdNameTerm _) (FuncApp _ _) = LT
  compare (FuncApp _ _) (StdNameTerm _) = GT
  compare (FuncApp f1 ts1) (FuncApp f2 ts2) =
    case compare f1 f2 of
      EQ -> compare ts1 ts2
      ord -> ord

data Atom = Pred String [Term] 

--two Preds are equal if their predicate names and term lists are identical.
instance Eq Atom where
    Pred p1 ts1 == Pred p2 ts2 = p1 == p2 && ts1 == ts2

--Defines an ordering for Atoms, useful for sets or sorting. We'll order by predicate name first, then by terms.
instance Ord Atom where
  compare (Pred p1 ts1) (Pred p2 ts2) =
    case compare p1 p2 of
      EQ -> compare ts1 ts2
      ord -> ord

instance Show Atom where
  show (Pred p ts) = p ++ "(" ++ unwords (map show ts) ++ ")"

\end{code}

Based on this, we can now define $\mathcal{KL}$-formulas:
\begin{code}
data Formula = Atom Atom                -- Predicate (e.g. Teach(x, "n1"))
              | Equal Term Term         --Equality (e.g., x = "n1")
              | Not Formula             -- Negation 
              | Or Formula Formula      -- Disjunction
              | Exists Variable Formula -- Existential (e.g., exists x (Teach x "sue")) 
              | K Formula               -- Knowledge Operator (e.g., K (Teach "ted" "sue"))
              deriving (Eq, Show)


forall :: Variable -> Formula -> Formula
forall x f = Not (Exists x (Not f))

implies :: Formula -> Formula -> Formula
implies f1 f2 = Or (Not f1) f2

iff :: Formula -> Formula -> Formula
iff f1 f2 = Or (Not (Or f1 f2)) (Or (Not f1) f2)
\end{code}