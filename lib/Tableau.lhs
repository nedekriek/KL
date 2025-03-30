\section{Tableau-Based Satisfiability and Validity Checking in \texorpdfstring{$\mathcal{KL}$}{KL}}\label{subsec:tableau}

In this section we will explain our implementation of satisfiability and validity checkers for the language $\mathcal{KL}$ using the tableau method - a systematic proof technique that constructs a tree to test formula satisfiability by decomposing logical components and exploring possible models.
We have decided to simplify this tableau checking by restricting it to the logic $\mathcal{KL}$ without function applications, to reduce the complexity.
In $\mathcal{KL}$, implementing tableau checking requires handling both first-order logic constructs (quantifiers, predicates) and the epistemic operator $\mathbf{K}$, which requires tracking possible worlds.
Full first-order epistemic logic with infinite domains is in general undecidable (\cite{Lokb} p. 173), so we adopt a semi-decision procedure: terminating with "satisfiable" if an open branch is found but may loop infinitely for unsatisfiable cases due to the infinite domain $\mathcal{N}$.
The \verb?Tableau? module builds on \verb?SyntaxKL? and \verb?SemanticsKL?/ modules.

\hide{
\begin{code}
module Tableau where

import SyntaxKL
import SemanticsKL
import Data.Set (Set)
import qualified Data.Set as Set
import Test.QuickCheck

\end{code}
}
\textbf{Tableau Approach}\\
The tableau method tests satisfiability as follows:  
A formula $\alpha$ is satisfiable if there exists an epistemic state $e$ and a world $w\in e$ such that $e,w \models \alpha$.
    The tableau starts with $\alpha$ and expands it, seeking an open (non-contradictory) branch representing a model.
A formula $\alpha$ is valid if it holds in all possible models $(e,w \models \alpha$ for all $e,w)$.
    We test validity by checking if $\neg \alpha$ unsatisfiable (i.e., all tableau branches close).

With $\mathcal{KL}$ we have to make sure that the following to things are handled correctly:
\begin{itemize}
    \item Infinite domains: $\mathcal{KL}$ assumes a countably infinite set of standard names (\cite{Lokb}, p.23).
    The tableau method handles this via parameters (free variables) and $\delta$-rules (existential instantiation), introducing new names as needed.
    This means that we use a countably infinite supply of parameters (e.g., n1, n2,...) instead of enumerating all standard names.
    \item Modal handling: The $\mathbf{K}$-operator requires branching over possible worlds within an epistemic state.
\end{itemize}

First, we define new types for the tableau node and branch: A \verb?Node? pairs formulas with world identifiers (of type \verb?TabWorld?), and a \verb?Branch? tracks nodes, used standard names, and eliminated nodes of atoms. The inclusion of \verb?eliminatedAtomicNodes? is important for the tableau expansion process, as it allows us to keep track of the atomic formulas that could be used to close a branch (see \verb?isClosed?) while differentiating from formula that can be further processed (see \verb?applyRule?).
\begin{code}
type TabWorld = Int    -- World identifier (0, 1, ...)

data Node = Node Formula TabWorld deriving (Eq, Show)

data Branch = Branch { nodes :: [Node],  params :: Set StdName, eliminatedAtomicNodes :: [Node] } deriving (Eq, Show)

\end{code}

\hide{
\begin{code}
-- Arbitrary instance for Node
instance Arbitrary Node where
  arbitrary = do
    formula <- arbitrary
    world <- choose (0, 10) -- Example range for world identifiers
    return $ Node formula world

-- Arbitrary instance for Branch
instance Arbitrary Branch where
    arbitrary = do
        let stdNameSetForBranch :: Gen (Set StdName)
            stdNameSetForBranch = sized $ \n -> do
                let m = min n 10
                size <- choose (0, m)
                Set.fromList <$> vectorOf size arbitrary
        ns <- resize 10 (listOf arbitrary) :: Gen [Node] -- Limit to 0-5 nodes
        ps <- stdNameSetForBranch
        ks <- resize 10 (listOf arbitrary) :: Gen [Node] -- Generate a list of Nodes for eliminatedAtomicNodes
        return $ Branch ns ps ks
\end{code}
}

\textbf{Tableau Rules}\\
Rules decompose formulas, producing either a closed branch (contradictory) or open branches (consistent). The function\verb?applyRule? implements these rules, handling logical and epistemic operators. The rules are applied iteratively to unexpanded nodes until all branches are either closed or fully expanded (open).
\vspace{10pt}
\begin{code}
data RuleResult = Closed | Open [Branch] deriving (Eq, Show)

-- Generates fresh standard names not in the used set
newParams :: Set StdName -> [StdName]
newParams used = [StdName ("n" ++ show i) | i <- [(1::Int)..], StdName ("n" ++ show i) `Set.notMember` used]

-- Decomposes a formula in a node, returning Closed for contradictions or Open with updated branches
applyRule :: Node -> Branch -> RuleResult
applyRule (Node f w) branch = case f of
  Atom g -> Open [Branch (nodes branch) (params branch) (eliminatedAtomicNodes branch ++ [Node (Atom g) w])]    -- Add atom to eliminated nodes
  Not (Atom g) -> Open [Branch (nodes branch) (params branch) (eliminatedAtomicNodes branch ++ [Node (Not (Atom g)) w])]     -- Add negated atom
  Equal t1 t2 -> if t1 == t2 then Open [branch] else Closed     -- t1 = t2: open if true, else closed
  Not (Equal t1 t2) -> if t1 == t2 then Closed else Open [branch]    -- t1 /= t2: closed if equal, else open
  Not (Not f') -> Open [Branch (Node f' w : nodes branch) (params branch) (eliminatedAtomicNodes branch)]    -- Double negation, e.g., replace not not phi with phi
  Not (Or f1 f2) -> Open [Branch (Node (Not f1) w : Node (Not f2) w : nodes branch) (params branch) (eliminatedAtomicNodes branch)]    -- De Morgan: ~(f1 v f2) -> ~f1 & ~f2
  Not (Exists x f') -> Open [Branch (Node (klforall x (Not f')) w : nodes branch) (params branch) (eliminatedAtomicNodes branch)]    -- Negated existential
  Not (K f') -> Open [expandKNot f' w branch]     --   Negated knowledge
  Or f1 f2 -> Open [ Branch (Node f1 w : nodes branch) (params branch) (eliminatedAtomicNodes branch)
                   , Branch (Node f2 w : nodes branch) (params branch) (eliminatedAtomicNodes branch)] -- Disjunction rule, split the branch
  Exists x f' ->   -- Existential rule: ∃x f': add f'[x/a] with fresh parameter a
    let newParamsList = newParams (params branch)
        newParam = case newParamsList of
            (p:_) -> p -- Safely extract the first fresh parameter
            [] -> error "newParams returned an empty list, which should never happen"
        substitutedFormula = subst x newParam f' -- Substitute x with the fresh parameter
        newBranch = Branch (Node substitutedFormula w : nodes branch)
                           (Set.insert newParam (params branch)) (eliminatedAtomicNodes branch)
    in Open [newBranch]
  K f' -> Open [expandK f' w branch] -- Knowledge rule, add formula to a new world

-- Adds formula f to world 1 for K operator, modeling knowledge in all worlds.
expandK :: Formula -> TabWorld -> Branch -> Branch
expandK f _ branch = Branch (Node f 1 : nodes branch) (params branch) (eliminatedAtomicNodes branch) --- Only world 1

-- Adds ~f to world 2 for ~K operator, modeling f false in some world.
expandKNot :: Formula -> TabWorld -> Branch -> Branch
expandKNot f _ branch = Branch (Node (Not f) 2 : nodes branch) (params branch) (eliminatedAtomicNodes branch) ---Only world 2
\end{code}

\hide{
\begin{code}
instance Arbitrary RuleResult where
    arbitrary = oneof [ return Closed
                      , Open <$> resize 5 (listOf arbitrary) ] -- Limit to 0-5 branches
\end{code}
}

\textbf{Branch Closure}\\
The \verb?isClosed? function determines if a tableau branch is closed by identifying contradictions among its formulas, ensuring no consistent model can satisfy them. 
A branch closes if it contains an explicit contradiction, meaning no model can satisfy all the formulas in that branch. If a branch is not closed, it is potentially part of a satisfiable interpretation.
The function \verb?isClosed? examines both active nodes and eliminated atomic nodes, collecting positive and negated atoms (e.g., $P(n1)$ and $\neg P(n1)$) as well as equalities (e.g., $t1 = t2$ and $\neg(t1 = t2)$), each tagged with their world identifier. 
The function checks for conflicts in two contexts: the actual world (w=0), where it looks for direct contradictions like an atom being both true and false, and modal worlds (w=1, w=2), where it assesses consistency across epistemic states introduced by the $\mathbf{K}$ and $\neg\mathbf{K}$ operators. 
For example, it flags a branch as closed if $P(n1)$ is true in world 1 but false in world 2, reflecting a violation of knowledge constraints. 
A branch closes if any such contradiction - among atoms or equalities - is found in the same or related worlds, ensuring the tableau accurately tests satisfiability. 
The function returns \verb?True? for a closed branch, indicating an unsatisfiable state, and \verb?False? for an open branch, suggesting a potentially satisfiable interpretation.
This function reflects the semantic requirement that a world state $w$ in an epistemic state $e$ can not assign both \verb?True? and \verb?False? to the same ground atom or equality.

\vspace{10pt}
\begin{code}
-- Checks if a branch is closed (contradictory) by detecting conflicting atoms or equalities.
isClosed :: Branch -> Bool
isClosed b =
  let atoms = [(a, w, True) | Node (Atom a) w <- nodes b]   -- Positive atoms from nodes
              ++ [(a, w, False) | Node (Not (Atom a)) w <- nodes b]   -- Negated atoms from nodes
      retainedAtoms = [(a, w, True) | Node (Atom a) w <- eliminatedAtomicNodes b]   -- Positive atoms from eliminated nodes
              ++ [(a, w, False) | Node (Not (Atom a)) w <- eliminatedAtomicNodes b]   -- Negated atoms from eliminated nodes
      equals = [((t1, t2), w, True) | Node (Equal t1 t2) w <- nodes b]   -- Positive equalities from nodes
              ++ [((t1, t2), w, False) | Node (Not (Equal t1 t2)) w <- nodes b]   -- Negated equalities from nodes
      retainedAtomsContraActual = any (\(a1, w1, b1) -> any (\(a2, w2, b2) -> 
                    a1 == a2 && w1 == 0 && w2 == 0 && b1 /= b2) retainedAtoms) retainedAtoms   -- Contradiction in retained atoms, world 0
      retainedAtomsContraModal = any (\(a1, w1, b1) -> any (\(a2, w2, b2) -> 
                    a1 == a2 && ((w1 == 1 && w2 == 2) || (w1 == 2 && w2 == 1) || (w1 == 1 &&  w2 == 1)) && b1 /= b2) retainedAtoms) retainedAtoms   -- Contradiction in retained atoms, modal worlds
      atomContraActual = any (\(a1, w1, b1) -> any (\(a2, w2, b2) -> 
                    a1 == a2 && w1 == 0 && w2 == 0 && b1 /= b2) atoms) atoms   -- Contradiction in nodes’ atoms, world 0
      atomContraModal = any (\(a1, w1, b1) -> any (\(a2, w2, b2) -> 
                    a1 == a2 && ((w1 == 1 && w2 == 2) || (w1 == 2 && w2 == 1) || (w1 == 1 && w2 == 1)) && b1 /= b2) atoms) atoms   -- Contradiction in nodes’ atoms, modal worlds
      eqContraActual = any (\((t1, t2), w1, b1) -> any (\((t3, t4), w2, b2) -> 
                    t1 == t3 && t2 == t4 && w1 == 0 && w2 == 0 && b1 /= b2) equals) equals   -- Contradiction in equalities, world 0
      eqContraModal = any (\((t1, t2), w1, b1) -> any (\((t3, t4), w2, b2) -> 
                    t1 == t3 && t2 == t4 && ((w1 == 1 && w2 == 2) || (w1 == 2 && w2 == 1) || (w1 == 1 && w2 == 1)) && b1 /= b2) equals) equals   -- Contradiction in equalities, modal worlds
  in atomContraActual || atomContraModal || eqContraActual || eqContraModal || retainedAtomsContraActual || retainedAtomsContraModal -- True if any contradiction exists
\end{code}

\textbf{Tableau Expansion}\\
Next, we have the function \verb?expandTableau?. 
It iteratively applies tableau rules to expand all branches, determining if any remain open (indicating satisfiability). 
It returns \verb?Just branches? if at least one branch is fully expanded and open, and \verb?Nothing? if all branches close.
This function uses recursion. It continues until either all branches are closed or some are fully expanded.
\vspace{10pt}

\begin{code}
-- Expands a list of tableau branches, returning Nothing if all branches close or Just with open branches.
expandTableau :: [Branch] -> Maybe [Branch]
expandTableau branches
  | null branches = Nothing   -- No branches to expand, return Nothing
  | all isClosed branches = Nothing   -- All branches closed, unsatisfiable, return Nothing
  | otherwise =
      let openBranches = filter (not . isClosed) branches   -- Keep only open (non-contradictory) branches
          expandable = filter (not . null . nodes) openBranches   -- Filter branches with nodes to expand
      in if null expandable
         then Just openBranches   -- No nodes left to expand, return open branches
         else case expandable of
             (branch:rest) ->
                 let ruleResult = applyRule (head (nodes branch)) (Branch (tail (nodes branch)) (params branch) (eliminatedAtomicNodes branch))   -- Apply rule to first node
                 in case ruleResult of
                      Closed -> expandTableau rest   -- Branch closed, recurse on remaining branches
                      Open newBranches -> case expandTableau rest of   -- Rule opens new branches
                          Nothing -> expandTableau newBranches   -- Rest unsatisfiable, try new branches
                          Just restBranches -> case expandTableau newBranches of   -- Rest satisfiable, expand new branches
                              Nothing -> Just restBranches   -- New branches unsatisfiable, keep rest
                              Just newBs -> Just (newBs ++ restBranches)   -- Combine expanded new and rest branches
             [] -> Nothing   -- Unreachable due to prior null check on expandable
\end{code}

\textbf{Top-Level Checkers}\\
As top-level functions we use \verb?isSatisfiable? and \verb?isValid?. 
The function \verb?isSatisfiable? tests whether a formula $f$ has a satisfying model. 
It starts the tableau process and interprets the result. 
This function gets a \verb?Formula f? as an input and then creates a single branch with \verb?Node f 0? (formula \verb?f? in world \verb?0?) and an empty set of parameters. Next, it calls \verb?expandTablaeu? on this initial branch.
It then interprets the result: if \verb?expandTableau? returns \verb?Just? $\mathunderscore$, this means, that at least one open branch exists, thus, the formula is satisfiable. 
If \verb?expandTableau? returns \verb?Nothing?, this means that all branches are closed and the formula is unsatisfiable.
\vspace{10pt}
\begin{code}
-- Checks if a formula is satisfiable
isSatisfiable :: Formula -> Bool
isSatisfiable f = case expandTableau [Branch [Node f 0] Set.empty []] of 
  Just _ -> True
  Nothing -> False
\end{code}
The three functions \verb?isSatisfiable?, \verb?expandTableau?, and \verb?isClosed? interact as follows: \verb?isSatisfiable? starts the process with a single branch containing the formula. 
Then, \verb?expandTableau? recursively applies \verb?applyRule? to decompose formulas, creating new branches as needed (e.g., for $\lor$, $\exists$).
In a next step, \verb?isClosed? checks each branch for contradictions, guiding \verb?expandTableau? to prune closed branches or halt with an open one.

\vspace{10pt}
\begin{code}
-- Checks if a formula is valid
isValid :: Formula -> Bool
isValid f = not (isSatisfiable (Not f))
\end{code}




