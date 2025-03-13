\section{$\mathcal{KL}$: Syntax and Semantics}\label{sec:KLmodel}
\insert{Syntax}

\subsection{Semantics}

\begin{code}
module SemanticsKL where

import SyntaxKL
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

\end{code}



We want a world state to assign values to primitive terms and atoms, so we create a new type WorldState. 
An epistemic state is a set of possible world states.
\begin{code}
data WorldState = WorldState
  { atomValues :: Map Atom Bool        -- Truth values of ground atoms
  , termValues :: Map Term StdName     -- Values of ground terms
  } deriving (Eq, Ord, Show)

type EpistemicState = Set WorldState
\end{code}

To evaluate a ground term in a world state, we define a function evalTerm that takes a WorldState and a Term and returns a StdName. 
The idea is to map syntactic terms to their semantic values (standard names) in a given world state. 
The function uses pattern matching to handle the three possible forms of Term:
\begin{itemize}
\item[1.] VarTerm $\mathunderscore$ \\
If the term is a variable (e.g., x), it throws an error.
This enforces a precondition that evalTerm only works on ground terms (terms with no free variables). 
In $\mathcal{KL}$, variables must be substituted with standard names before evaluation, aligning with the semantics where only ground terms have denotations %TODO \cite{LokB}, p. 24). 
This is a runtime check to catch ungrounded inputs. 
\item[2.] StdNameTerm n\\
If the term is a standard name wrapped in StdNameTerm (e.g., StdNameTerm (StdName "n1")), it simply returns the underlying StdName (e.g., StdName "n1").
Standard names in $\mathcal{KL}$ are constants that denote themselves (ibid., p.22). 
For example, if n=StdName "n1", it represents the individual n1, and its value in any world is n1. 
In this case, no lookup or computation is needed.
\item[3.] FuncApp f args\\
If the term is a function application (e.g., f(n1,n2)), evalTerm evaluates the argument, by recursively computing the StdName values of each argument in args using evalTerm w. 
Next, the ground term is constructed: It Builds a new FuncApp term where all arguments are standard names (wrapped in StdNameTerm), ensuring it's fully ground.
We then look up the value by querying the termValues map in the world state w for the denotation of this ground term, defaulting to StdName "n1" if not found.
\end{itemize}

\begin{code}
evalTerm :: WorldState -> Term -> StdName
evalTerm w t = case t of
  VarTerm _ -> error "evalTerm: Variables must be substituted"
  StdNameTerm n -> n
  FuncApp f args ->
    let argValues = map (evalTerm w) args
        groundTerm = FuncApp f (map StdNameTerm argValues)
    in Map.findWithDefault (StdName "n1") groundTerm (termValues w) -- Default for undefined, use "n1"
\end{code}

Next, we want to define a satisfies function. For this, we need a helper-function that checks whether a term or formula is ground. 
We also need a helper-function that substitutes a variable with a standard name in a term  for the exists-case.

\begin{code}
-- Check if a term is ground (contains no variables).
isGround :: Term -> Bool
isGround t = case t of
  VarTerm _ -> False
  StdNameTerm _ -> True
  FuncApp _ args -> all isGround args

-- Check if a formula is ground.
isGroundFormula :: Formula -> Bool
isGroundFormula f = case f of
  Atom (Pred _ terms) -> all isGround terms
  Equal t1 t2 -> isGround t1 && isGround t2
  Not f' -> isGroundFormula f'
  Or f1 f2 -> isGroundFormula f1 && isGroundFormula f2
  Exists _ _ -> False   -- always contains a variable
  K f' -> isGroundFormula f'

-- Substitute a variable with a standard name in a term.
substTerm :: Variable -> StdName -> Term -> Term
substTerm x n t = case t of
  VarTerm v | v == x -> StdNameTerm n
  VarTerm _ -> t
  StdNameTerm _ -> t
  FuncApp f args -> FuncApp f (map (substTerm x n) args)

-- Substitute a variable with a standard name in a formula.
subst :: Variable -> StdName -> Formula -> Formula
subst x n formula = case formula of
  Atom (Pred p terms) -> Atom (Pred p (map (substTerm x n) terms))
  Equal t1 t2 -> Equal (substTerm x n t1) (substTerm x n t2)
  Not f -> Not (subst x n f)
  Or f1 f2 -> Or (subst x n f1) (subst x n f2)
  Exists y f | y == x -> formula -- Avoid capture
             | otherwise -> Exists y (subst x n f)
  K f -> K (subst x n f)


\end{code}

Since we want to check for satisfiability in a model, we want to make the model explicit:
\begin{code}
data Model = Model
  { actualWorld :: WorldState      -- The actual world state
  , epistemicState :: EpistemicState -- Set of possible world states
  , domain :: Set StdName          -- Domain of standard names
  } deriving (Show)
\end{code}

With the helper-functions and the new type Model, we can now implement the satisfiesModel function as follows:
\begin{code}
satisfiesModel :: Model -> Formula -> Bool
satisfiesModel m = satisfies (epistemicState m) (actualWorld m)
  where
    satisfies e w formula = case formula of
      Atom (Pred p terms) ->
        if all isGround terms
          then Map.findWithDefault False (Pred p terms) (atomValues w)
          else error "Non-ground atom in satisfies!"
      Equal t1 t2 ->
        if isGround t1 && isGround t2
          then evalTerm w t1 == evalTerm w t2
          else error "Non-ground equality in satisfies!"
      Not f ->
        not (satisfies e w f)
      Or f1 f2 ->
        satisfies e w f1 || satisfies e w f2
      Exists x f -> 
      -- \(e, w \models \exists x. \alpha\) iff for some name \(n\), \(e, w \models \alpha_n^x\)
        any (\n -> satisfies e w (subst x n f)) (Set.toList $ domain m)
      -- \(e, w \models K \alpha\) iff for every \(w' \in e\), \(e, w' \models \alpha\)
      K f ->
        all (\w' -> satisfies e w' f) e

\end{code}

Building on this we can implement a function checkModel that checks whether a formula holds in a given model:
\begin{code}
checkModel :: Model -> Formula -> Bool
checkModel m phi = all (satisfiesModel m) (groundFormula phi (domain m))
\end{code}

Note that we use the function groundFormula here. 
Since we have implemented satisfiesModel such that it assumes ground formulas or errors out, we decided to handle free variables by grounding formulas by substituting free variables. 
We implement groundFormula as follows:

\begin{code}
groundFormula :: Formula -> Set StdName -> [Formula]
groundFormula f domain = do
  -- converts the set of free variables in f to a list
  let fvs = Set.toList (freeVars f)
  -- creates a list of all possible assignments of domain elements to each free variable
  -- For each variable in fvs, toList domain provides the list of standard names, mapM applies this (monadically), producing all the combinations
  subs <- mapM (\_ -> Set.toList domain) fvs
  --iteratively substitute each variable v with a standard name n in the formula
  return $ foldl (\acc (v, n) -> subst v n acc) f (zip fvs subs)
\end{code}
This function takes a formula and a domain of standard names and returns a list of all possible ground instances of the formula by substituting its free variables with elements from the domain.
We use a function freeVars that identifies all the variables in a formula that need grounding or substitution. 
It takes a formula and returns a Set Variable containing all the free variables in that formula:

\begin{code}
freeVars :: Formula -> Set Variable
freeVars f = case f of
  --Collects free variables from all terms in the predicate
  Atom (Pred _ terms) -> Set.unions (map freeVarsTerm terms)
  -- Unions the free variables from both terms t1 and t2.
  Equal t1 t2 -> freeVarsTerm t1 `Set.union` freeVarsTerm t2
  -- Recursively computes free variables in the negated subformula f'.
  Not f' -> freeVars f'
  -- Unions the free variables from both disjuncts f1 and f2.
  Or f1 f2 -> freeVars f1 `Set.union` freeVars f2
  -- Computes free variables in f', then removes x (the bound variable) using delete, since x is not free within \exists x f'
  Exists x f' -> Set.delete x (freeVars f')
  -- Recursively computes free variables in f', as the K operator doesn't bind variables.
  K f' -> freeVars f'
  where
    freeVarsTerm t = case t of
      --A variable (e.g., x) leads to a singleton set containing v.
      VarTerm v -> Set.singleton v
      -- A standard name (e.g., n1) has no free variables, so returns an empty set.
      StdNameTerm _ -> Set.empty
      -- A function application (e.g., f(x,n1)) recursively computes free variables in its arguments.
      FuncApp _ args -> Set.unions (map freeVarsTerm args)
\end{code}