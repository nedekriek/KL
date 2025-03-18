\section{Tableau-Based Satisfiability and Validity Checking in $\mathcal{KL}$}\label{subsec:tableau}

Note: For the Beta-version, we omitted function symbol evaluation, limiting the satisfiability and validity checking to a propositional-like subset.\\
\\
This subsection implements satisfiability and validity checkers for  $\mathcal{KL}$ using the tableau method, a systematic proof technique that constructs a tree to test formula satisfiability by decomposing logical components and exploring possible models.
In $\mathcal{KL}$, this requires handling both first-order logic constructs (quantifiers, predicates) and the epistemic operator $K$, which requires tracking possible worlds.
Note that the full first-order epistemic logic with infinite domains is in general undecidable (\cite{Lokb} p. 173), so we adopt a semi-decision procedure: it terminates with "satisfiable" if an open branch is found but may loop infinitely for unsatisfiable cases due to the infinite domain $\mathcal{N}$.
The Tableau module builds on SyntaxKL and SemanticsKL:
\begin{code}
module Tableau where

import SyntaxKL
import SemanticsKL
import Data.Set (Set)
import qualified Data.Set as Set
\end{code}

\textbf{Tableau Approach}\\
The tableau method tests satisfiability as follows:  
A formula $\alpha$ is satisfiable if there exists an epistemic state $e$ and a world $w\in e$ such that $e,w \models \alpha$.
    The tableau starts with $\alpha$ and expands it, seeking an open (non-contradictory) branch representing a model.
A formula $\alpha$ is valid if it holds in all possible models $(e,w \models \alpha$ for all $e,w)$.
    We test validity by checking if $\neg \alpha$ unsatisfiable (i.e., all tableau branches close).
For $\mathcal{KL}$ we have to handle two things:
\begin{itemize}
    \item Infinite domains: $\mathcal{KL}$ assumes a countably infinite set of standard names (\cite{Lokb}, p.23).
    The tableau method handles this via parameters (free variables) and $\delta$-rules (existential instantiation), introducing new names as needed.
    This means that we Use a countably infinite supply of parameters (e.g., a1, a2,...) instead of enumerating all standard names.
    \item Modal handling: The K-operator requires branching over possible worlds within an epistemic state.
\end{itemize}

First, we define new types for the tableau node and branch: Nodes pair formulas with world identifiers, and branches track nodes and used parameters.
\begin{code}
-- A tableau node: formula labeled with a world
data Node = Node Formula World deriving (Eq, Show)

type World = Int    -- World identifier (0, 1, ...)

-- A tableau branch: list of nodes and set of used parameters
data Branch = Branch { nodes :: [Node], params :: Set StdName } deriving (Show)
\end{code}

\textbf{Tableau Rules}\\
Rules decompose formulas, producing either a closed branch (contradictory) or open branches (consistent). 
applyRule implements these rules, handling logical and epistemic operators.
The rules are applied iteratively to unexpanded nodes until all branches are either closed or fully expanded (open).
\begin{code}
-- Result of applying a tableau rule
data RuleResult = Closed | Open [Branch] deriving (Show)

-- Generates fresh parameters not in the used set
newParams :: Set StdName -> [StdName]
newParams used = [StdName ("a" ++ show i) | i <- [(1::Int)..], StdName ("a" ++ show i) `Set.notMember` used]

-- Applies tableau rules to a node on a branch
applyRule :: Node -> Branch -> RuleResult
applyRule (Node f w) branch = case f of
  Atom _ -> Open [branch]   -- If formula is an atom: Do nothing; keep the formula in the branch.
  Not (Atom _) -> Open [branch]  -- Negated atoms remain, checked by isClosed
  Equal _ _ -> Open [branch]  -- Keep equality as is; closure checks congruence
  Not (Equal _ _) -> Open [branch]  -- Keep negated equality 
  Not (Not f') -> Open [Branch (Node f' w : nodes branch) (params branch)] -- Case: double negation, e.g., replace $\neg \neg \varphi$ with $\varphi$
  Not (Or f1 f2) -> Open [Branch (Node (Not f1) w : Node (Not f2) w : nodes branch) (params branch)] -- Case: negated disjunction
  Not (Exists x f') -> Open [Branch (Node (klforall x (Not f')) w : nodes branch) (params branch)] -- Case:: negated existential
  Not (K f') -> Open [expandKNot f' w branch] -- Case: negated knowledge
  Or f1 f2 -> Open [ Branch (Node f1 w : nodes branch) (params branch)
                   , Branch (Node f2 w : nodes branch) (params branch) ] -- Disjunction rule, split the branch
  Exists x f' ->   -- Existential rule ($\delta$-rule), introduce a fresh parameter a (e.g., a1​) not used elsewhere, substitute x with a, and continue
    let newParam = head (newParams (params branch))
        newBranch = Branch (Node (subst x newParam f') w : nodes branch)
                          (Set.insert newParam (params branch))
    in Open [newBranch]
  K f' -> Open [expandK f' w branch] -- Knowledge rule, add formula to a new world

-- Expands formula K \varphi to a new world
expandK :: Formula -> World -> Branch -> Branch
expandK f w branch = Branch (Node f (w + 1) : nodes branch) (params branch)

-- Expands \not K \varphi to a new world
expandKNot :: Formula -> World -> Branch -> Branch
expandKNot f w branch = Branch (Node (Not f) (w + 1) : nodes branch) (params branch)
\end{code}

\textbf{Branch Closure}\\
isClosed determines whether a tableau branch is contradictory (closed) or consistent (open). 
A branch closes if it contains an explicit contradiction, meaning no model can satisfy all the formulas in that branch. 
If a branch is not closed, it is potentially part of a satisfiable interpretation.
The input is a Branch, which has nodes :: [Node] (each Node f w is a formula f in world w) and params :: Set StdName (used parameters).
The function works as follows: first, we collect the atoms ((a, w, True) for positive atoms (Node (Atom a) w); (a, w, False) for negated Atoms (Node (Not (Atom a)) w)).
For example, if nodes = [Node (Atom P(n1)) 0, Node (Not (Atom P(n1))) 0], then atoms = [(P(n1), 0, True), (P(n1), 0, False)].
Next, we collect the equalities. After this, we check the atom contradictions. There we use $any$ to find pairs in $atoms$ and return True if a contradiction exists.
In a subsequent step, we check for equality contradictions. 
The result of the function is atomContra || eqContra: this is True if either type of contradiction is found and False otherwise.
This function reflects the semantic requirement that a world state w in an epistemic state e can not assign both True and False to the same ground atom or equality

\begin{code}
-- Branch closure with function symbols
isClosed :: Branch -> Bool
isClosed b =
  let atoms = [(a, w, True) | Node (Atom a) w <- nodes b]
             ++ [(a, w, False) | Node (Not (Atom a)) w <- nodes b]
      equals = [((t1, t2), w, True) | Node (Equal t1 t2) w <- nodes b]
              ++ [((t1, t2), w, False) | Node (Not (Equal t1 t2)) w <- nodes b]
      atomContra = any (\(a1, w1, b1) -> any (\(a2, w2, b2) -> a1 == a2 && w1 == w2 && b1 /= b2) atoms) atoms
      eqContra = any (\((t1, t2), w1, b1) -> any (\((t3, t4), w2, b2) -> 
                   t1 == t3 && t2 == t4 && w1 == w2 && b1 /= b2) equals) equals
  in atomContra || eqContra  -- True if any contradiction exists
\end{code}

\textbf{Tableau Expasion}\\
Next, we have the function expandTableau. 
expandTableau iteratively applies tableau rules to expand all branches, determining if any remain open (indicating satisfiability). 
It returns Just branches if at least one branch is fully expanded and open, and Nothing if all branches close.
This function uses recursion. It continues until either all branches are closed or some are fully expanded
\begin{code}
-- Expands the tableau, returning open branches if satisfiable
expandTableau :: [Branch] -> Maybe [Branch]
expandTableau branches
  | all isClosed branches = Nothing --If every branch is contradictory, return Nothing
  | any (null . nodes) branches = Just branches --If any branch has no nodes left to expand (and isn't closed), it's open and complete
  | otherwise = do
      let (toExpand, rest) = splitAt 1 branches --Take the first branch (toExpand) and leave the rest.
          branch = head toExpand --Focus on this branch.
          node = head (nodes branch) --Pick the first unexpanded node.
          remaining = Branch (tail (nodes branch)) (params branch) --he branch minus the node being expanded.
      case applyRule node remaining of
        Closed -> expandTableau rest --Skip this branch, recurse on rest.
        Open newBranches -> expandTableau (newBranches ++ rest) --Add the new branches (e.g., from \lor or \exists) to rest, recurse.
\end{code}

\textbf{Top-Level Checkers}\\
As top-level function we use isSatisfiable and isValid. 
isSatisfiable tests whether a formula $f$ has a satisfying model. 
It starts the tableau process and interprets the result. 
This function gets a Formula $f$ as an input and then creates a single branch with Node f 0 (formula f in world 0) and an empty set of parameters. Next, it calls expandTablaeu on this initial branch.
It then interprets the result: if expandTableau returns Just $\mathunderscore$, this means, that at least one open branch exists, thus, the formula is satisfiable. 
If expandTableau returns Nothing, this means that all branches are closed and the formula is unsatisfiable.
\begin{code}

-- Tests if a formula is satisfiable
isSatisfiable :: Formula -> Bool
isSatisfiable f = case expandTableau [Branch [Node f 0] Set.empty] of 
  Just _ -> True
  Nothing -> False

\end{code}
The three function isSatisfiable, expandTableau, and isClosed interact as follows: isSatisfiable starts the process with a single branch containing the formula.
expandTableau recursively applies applyRule to decompose formulas, creating new branches as needed (e.g., for $\lor$, $\exists$).
isClosed checks each branch for contradictions, guiding expandTableau to prune closed branches or halt with an open one.

\begin{code}
-- Tests if a formula is valid
isValid :: Formula -> Bool
isValid f = not (isSatisfiable (Not f))
\end{code}

