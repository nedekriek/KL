\section{Ask & Tell Operators}\label{sec:AskTell}

% Needs satisfies function from previous Repo


\begin{code}
module AskTell (ask, initial) where
import qualified Data.Map as Map
import qualified Data.Set as Set
import SyntaxKL
import SemanticsKL
\end{code}

Levesque defines two operators on epistemic states: ASK and TELL. The ASK operator determines whether a formula is known to a knowledge base.
Formally, given an epistemic state $e$ and any sentence $\alpha$ of $\mathcal{KL}$,
$$ASK(e,\alpha) = \begin{cases} 
            True &\text{ if } e \models K \alpha \\
            False &\text{ otherwise }
            \end{cases}
$$
% It's worth noting that Levesque abuses notation here by using "$e \models$", but by the semantics of $K$ it is clear that $\alpha$ must be true in all worlds of $e$.

When implementing $ASK$ in Haskell, we must take into account that a domain is implied by "$\models$" so that we can evaluate sentences with quantifiers. As such, we will take a domain as our first argument.

\begin{code}
-- ASK (Definition 5.2.1)
ask :: Set.Set StdName -> EpistemicState -> Formula -> Bool
ask d e alpha | Set.null e = False
              | otherwise = satisfiesModel newModel (K alpha) where
              newModel = Model {actualWorld = (Set.findMin e), epistemicState = e, domain = d}

\end{code}

We can simplify this into an askModel function that takes only a model and sentence as input.

\begin{code}
askModel :: Model -> Formula -> Bool
askModel m alpha |  Set.null (epistemicState m) = False
             |  otherwise = satisfiesModel m (K alpha)

\end{code}

The second operation, $TELL$, asserts that a sentence is true and in doing so reduces which worlds are possible. In practice, $TELL[\varphi, e]$ filters the epistemic state $e$ to worlds where the sentence $\varphi$ holds.
That is,
$$TELL[\varphi,e] = e \cap \{w \; | \; w \models \varphi \}$$

Again, we run into the issue that "$\models$" requires a domain, and so a domain must be specified to evaluate sentences with quantifiers.

\begin{code}
-- TELL operation (Definition 5.5.1)
tell :: Set.Set StdName -> EpistemicState -> Formula -> EpistemicState
tell d e alpha = Set.filter filterfunc e where
    filterfunc = (\w -> satisfiesModel (Model {actualWorld = w, epistemicState = e, domain = d}) alpha)
\end{code}

We can again simplify to a function tellModel, that takes as input a model and formula and produces a model with a modified epistemic state.

\begin{code}
tellModel :: Model -> Formula -> Model
tellModel m alpha = Model {actualWorld = actualWorld m, epistemicState = Set.filter filterfunc  (epistemicState m), domain = domain m} where
    filterfunc = (\w -> satisfiesModel (Model {actualWorld = w, epistemicState = epistemicState m, domain = domain m}) alpha)

\end{code}

In addition to ASK and TELL, it is valuable to define an inital epistemic state. $INITIAL[]$ is the epistemic state before any $TELL$ operations. This state contains all possible world states as there is nothing known that eliminates any possible world.

\begin{code}
-- INITIAL operation (Section 5.3)
-- Generate all possible world states for a finite set of atoms and terms
allWorldStates :: [Atom] -> [Term] -> [StdName] -> [WorldState]
allWorldStates atoms terms domain = do
  atomVals <- mapM (\_ -> [True, False]) atoms
  termVals <- mapM (\t -> domain) terms
  return $ mkWorldState (zip atoms atomVals) (zip terms termVals)

-- Helper to create a world state from atom and term assignments
mkWorldState :: [(Atom, Bool)] -> [(Term, StdName)] -> WorldState
mkWorldState atoms terms =
  WorldState (Map.fromList atoms) (Map.fromList terms)


initial :: [Atom] -> [Term] -> [StdName] -> EpistemicState
initial atoms terms domain = Set.fromList (allWorldStates atoms terms domain)


\end{code}

