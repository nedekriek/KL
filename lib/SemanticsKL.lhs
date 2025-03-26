% \section{$\mathcal{KL}$: Syntax and Semantics}\label{sec:KLmodel}

\subsection{Semantics of \texorpdfstring{ $\mathcal{KL}$}{KL}}\label{subsec:KLsemantics}
$\mathcal{KL}$ is an epistemic extension of first-order logic designed to model knowledge and uncertainty, as detailed in \textcite{Lokb}.
It introduces a knowledge operator $\mathbf{K}$ and uses an infinite domain $\mathcal{N}$ of standard names to denote individuals. 
Formulas are evaluated in world states: consistent valuations of atoms and terms, while epistemic states capture multiple possible worlds, reflecting epistemic possibilities.\\
The semantics are implemented in the \verb?SemanticsKL? module, which imports syntactic definitions from \verb?SyntaxKL? and uses Haskell's \verb?Data.Map? and \verb?Data.Set? for efficient and consistent mappings.

\begin{code}
{-# LANGUAGE InstanceSigs #-}

module SemanticsKL where

import SyntaxKL 
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Test.QuickCheck

\end{code}

\textbf{Worlds and Epistemic States}\\
A \verb?WorldState? represents a single possible world in $\mathcal{KL}$, mapping truth values to primitive atoms and standard names to primitive terms.
An \verb?EpistemicState?, defined as a set of \verb?WorldState?s, models the set of worlds an agent considers possible, enabling the evaluation of the $\mathbf{K}$ operator.

\begin{code}
-- A single world state with valuations for atoms and terms
data WorldState = WorldState
 { atomValues :: Map Atom Bool,    -- Maps (primitive) atoms to truth values
   termValues :: Map Term StdName   --Maps (primitive) terms to standard names
  }  deriving (Eq, Ord, Show)

instance Arbitrary WorldState where
  arbitrary :: Gen WorldState
  arbitrary = WorldState <$> arbitrary <*> arbitrary

-- A set of possible world states, modeling epistemic possibilities
type EpistemicState = Set WorldState

\end{code}
\textbf{Constructing World States}\\
We can construct world states by using \verb?mkWorldState?, which builds a \verb?WorldState? from lists of primitive atoms and terms. 
While a \verb?WorldState? is defined in terms of \verb?Atom? and \verb?Term?, we use \verb?mkWorldState? to make sure that we can only have primitive atoms and primitive terms in the mapping.
To be able to use primitive terms and atoms in other functions just as we would use \verb?Atom? and \verb?Term? (since primitive atoms and primitive terms are atoms and terms as well),
we convert the constructors to those of regular terms and atoms.
We then use the function \verb?checkDups? to ensure that there are no contradictions in the world state (e.g., P(n1) mapped to both True and False), thus reinforcing the single-valuation principle (\cite{Lokb}, p. 24).
\verb?mkWorldState? then constructs maps for efficient lookup.

\begin{code}
-- Constructs a WorldState from primitive atoms and primitive terms
mkWorldState :: [(PrimitiveAtom, Bool)] -> [(PrimitiveTerm, StdName)] -> WorldState
mkWorldState atoms terms =
  let convertAtom (PPred p ns, b) = (Pred p (map StdNameTerm ns), b)  -- Convert primitive atom to Atom
      convertTerm (PStdNameTerm n, v) = (StdNameTerm n, v)  -- Convert primitive term to Term
      convertTerm (PFuncAppTerm f ns, v) = (FuncAppTerm f (map StdNameTerm ns), v)
      atomList = map convertAtom atoms
      termList = map convertTerm terms
  in WorldState (Map.fromList (checkDups atomList)) (Map.fromList (checkDups termList))

-- Checks for contradictory mappings in a key-value list
checkDups :: (Eq k, Show k, Eq v, Show v) => [(k, v)] -> [(k, v)]
checkDups [] = []  -- Empty list is consistent
checkDups ((k, v) : rest) =  -- Recursively checks each key k against the rest of the list.
  case lookup k rest of  
    Just v' | v /= v' -> error $ "Contradictory mapping for " ++ show k ++ ": " ++ show v ++ " vs " ++ show v' -- If k appears with a different value v', throws an error.
    _ -> (k, v) : checkDups rest  -- Keep pair if no contradiction

\end{code}

Since we have decided to change the constructors of data of type \verb?PrimitiveAtom? or \verb?PrimitiveTerm? to those of \verb?Atom? and \verb?Term?, we have implemented two helper-functions to check if a \verb?Term? or an \verb?Atom? is primitive.
This way, we can, if needed, check whether a given \verb?Term? or \verb?Atom? is primitive and then change the constructors appropriately.


\begin{code}
-- Checks if a term is primitive (contains only standard names)
isPrimitiveTerm :: Term -> Bool
isPrimitiveTerm (StdNameTerm _) = True
isPrimitiveTerm (FuncAppTerm _ args) = all isStdName args
  where isStdName (StdNameTerm _) = True
        isStdName _ = False
isPrimitiveTerm _ = False

-- Checks if an atom is primitive
isPrimitiveAtom :: Atom -> Bool
isPrimitiveAtom (Pred _ args) = all isStdName args
  where isStdName (StdNameTerm _) = True
        isStdName _ = False


\end{code}

\textbf{Term Evaluation}\\
To evaluate a ground term in a world state, we define a function \verb?evalTerm? that takes a \verb?WorldState? and a \verb?Term? and returns a \verb?StdName?. 
The idea is to map syntactic terms to their semantic values (standard names) in a given world state. 
The function uses pattern matching to handle the three possible forms of \verb?Term?:
\begin{itemize}
\item[1.] \verb?VarTerm? $\mathunderscore$ \\
If the term is a variable (e.g., x), it throws an error.
This enforces a precondition that \verb?evalTerm? only works on ground terms (terms with no free variables). 
In $\mathcal{KL}$, variables must be substituted with standard names before evaluation, aligning with the semantics where only ground terms have denotations (\cite{Lokb}, p. 24). 
This is a runtime check to catch ungrounded inputs. 
\item[2.] \verb?StdNameTerm n?\\
If the term is a standard name wrapped in \verb?StdNameTerm? (e.g., \verb?StdNameTerm (StdName "n1")?), it simply returns the underlying \verb?StdName? (e.g., \verb?StdName "n1"?).
Standard names in $\mathcal{KL}$ are constants that denote themselves (ibid., p.22). 
For example, if \verb?n = StdName "n1"?, it represents the individual \verb?n1?, and its value in any world is \verb?n1?. 
In this case, no lookup or computation is needed.
\item[3.] \verb?FuncAppTerm f args?\\
If the term is a function application (e.g., f(n1,n2)), \verb?evalTerm? evaluates the argument, by recursively computing the \verb?StdName? values of each argument in \verb?args? using \verb?evalTerm w?. 
Next, the ground term is constructed: It builds a new \verb?FuncAppTerm? term where all arguments are standard names (wrapped in \verb?StdNameTerm?), ensuring it's fully ground.
We then look up the value by querying the \verb?termValues? map in the worldstate w for the denotation of this ground term, erroring on undefined terms.
\end{itemize}

\begin{code}
-- Evaluates a ground term to its standard name in a WorldState
evalTerm :: WorldState -> Term -> StdName
evalTerm w t = case t of
  VarTerm _ -> error "evalTerm: Variables must be substituted"  -- Variables are not ground
  StdNameTerm n -> n   -- Standard names denote themselves
  FuncAppTerm f args ->
    let argValues = map (evalTerm w) args   -- Recursively evaluate arguments
        groundTerm = FuncAppTerm f (map StdNameTerm argValues)   -- Construct ground term
    in case Map.lookup groundTerm (termValues w) of
        Just n -> n   -- Found in termValues
        Nothing -> error $ "evalTerm: Undefined ground term " ++ show groundTerm   -- Error if undefined
\end{code} 

\textbf{Groundness and Substitution}\\
To support formula evaluation, \verb?isGround? and \verb?isGroundFormula? check for the absence of variables, while \verb?substTerm? and \verb?subst? perform substitution of variables with standard names, respecting quantifier scope to avoid a capture.
We need these functions to be able to define a function that checks whether a formula is satisfiable in a worldstate and epistemic state.

\begin{code}
-- Check if a term is ground (contains no variables).
isGround :: Term -> Bool
isGround t = case t of
  VarTerm _ -> False
  StdNameTerm _ -> True
  FuncAppTerm _ args -> all isGround args

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
  VarTerm v | v == x -> StdNameTerm n -- Replace variable with name
  VarTerm _ -> t
  StdNameTerm _ -> t
  FuncAppTerm f args -> FuncAppTerm f (map (substTerm x n) args)

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

\textbf{Model and Satisfiability}\\
Since we want to check for satisfiability in a model, we want to make the model explicit:
\begin{code}
-- Represents a model with an actual world, epistemic state, and domain
data Model = Model
  { actualWorld :: WorldState      -- The actual world state
  , epistemicState :: EpistemicState -- Set of possible world states
  , domain :: Set StdName          -- Domain of standard names
  } deriving (Show, Eq)

instance Arbitrary Model where 
  arbitrary:: Gen Model 
  arbitrary = Model <$> arbitrary <*> arbitrary <*> arbitrary
\end{code}

A \verb?Model? encapsulates an actual world, an epistemic state, and a domain, enabling the evaluation of formulas with the $\mathcal{K}$-operator. 
\verb?satisfiesModel? implements $\mathcal{KL}$'s satisfaction relation, checking truth across worlds.

\begin{code}
-- Checks if a formula is satisfied in a model
satisfiesModel :: Model -> Formula -> Bool
satisfiesModel m = satisfies (epistemicState m) (actualWorld m)
  where
    satisfies e w formula = case formula of
      Atom (Pred p terms) ->
        if all isGround terms
          then Map.findWithDefault False (Pred p terms) (atomValues w)   -- Default False for undefined atoms
          else error "Non-ground atom in satisfies!"
      Equal t1 t2 ->
        if isGround t1 && isGround t2   -- Equality of denotations
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

\textbf{Grounding and Model Checking}\\
Building on this we can implement a function \verb?checkModel? that checks whether a formula holds in a given model.
\verb?checkModel? ensures a formula holds by grounding it with all possible substitutions of free variables, using \verb?groundFormula? and \verb?freeVars? to identify and replace free variables systematically.

\begin{code}
-- Checks if a formula holds in a model by grounding it
checkModel :: Model -> Formula -> Bool
checkModel m phi = all (satisfiesModel m) (groundFormula phi (domain m))
\end{code}

Note that we use the function \verb?groundFormula? here. 
Since we have implemented \verb?satisfiesModel? such that it assumes ground formulas or errors out, we decided to handle free variables by grounding formulas, given a set of free standard names to substitute. 
Alternatives would be to throw an error or always substitute the same standard name. The implementation that we have chosen is more flexible and allows for more varied usage, however it is computationally expensive (We would appreciate it if you have suggestions to improve this).
We implement \verb?groundFormula? as follows:

\begin{code}
-- Generates all ground instances of a formula
groundFormula :: Formula -> Set StdName -> [Formula]
groundFormula f dom = groundFormula' f >>= groundExists dom
  where
    -- Ground free variables at the current level
    groundFormula' formula = do
      let fvs = Set.toList (freeVars formula)
      subs <- mapM (\_ -> Set.toList dom) fvs
      return $ foldl (\acc (v, n) -> subst v n acc) formula (zip fvs subs)

    -- Recursively eliminate Exists in a formula
    groundExists domainEx formula = case formula of
      Exists x f' -> map (\n -> subst x n f') (Set.toList domainEx) >>= groundExists domainEx
      Atom a -> [Atom a]
      Equal t1 t2 -> [Equal t1 t2]
      Not f' -> map Not (groundExists domainEx f')
      Or f1 f2 -> do
        g1 <- groundExists domainEx f1
        g2 <- groundExists domainEx f2
        return $ Or g1 g2
      K f' -> map K (groundExists domainEx f')


\end{code}

This function takes a formula and a domain of standard names and returns a list of all possible ground instances of the formula by substituting its free variables with elements from the domain.
We use a function \verb?variables? that identifies all the variables in a formula that need grounding or substitution. 
If the Boolean '\verb?includeBound?' is '\verb?True?', \verb?variables? returns all variables (free and bound) in the formula.
If '\verb?includeBound?' is '\verb?False?', it returns only free variables, excluding those bound by quantifiers.
This way, we can use the function to support both '\verb?freeVars?' (free variables only) and '\verb?allVariables?' (all variables).

\begin{code}
-- Collects variables in a formula, with a flag to include bound variables
variables :: Bool -> Formula -> Set Variable
variables includeBound = vars 
  where
    -- Helper function to recursively compute variables in a formula
    vars formula = case formula of
      -- Union of variables from all terms in the predicate
      Atom (Pred _ terms) -> Set.unions (map varsTerm terms)
      -- Union of variables from both terms in equality
      Equal t1 t2 -> varsTerm t1 `Set.union` varsTerm t2
      Not f' -> vars f'
      Or f1 f2 -> vars f1 `Set.union` vars f2
      Exists x f' -> if includeBound
                     then Set.insert x (vars f') -- Include bound variable x if includeBound is True
                     else Set.delete x (vars f') -- Exclude bound variable x if includeBound is False
      K f' -> vars f'  -- Variables in the subformula under K (no binding)

    varsTerm term = case term of
      VarTerm v -> Set.singleton v  -- A variable term contributes itself to the set
      StdNameTerm _ -> Set.empty  -- A standard name has no variables
      FuncAppTerm _ args -> Set.unions (map varsTerm args)  -- Union of variables from all function arguments

-- Collects free variables in a formula
freeVars :: Formula -> Set Variable
freeVars = variables False

-- Collects all variables (free and bound) in a formula
allVariables :: Formula -> Set Variable
allVariables = variables True
\end{code}