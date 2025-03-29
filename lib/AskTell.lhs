\section{Ask and Tell Operators}\label{sec:AskTell}

To use $\mathcal{KL}$ to interact with a knowledge base, \textcite{Lokb} defines two operators on epistemic states: $\emph{ask}$ and $\emph{tell}$. Informally, $\emph{ask}$ is used to determine if a sentence is known to a knowledge base, whereas $\emph{tell}$ is used to add a sentence to the knowledge base. Since epistemic states are sets of possible worlds, the more known sentences there are, the smaller the set of possible worlds. For this purpose, an $\emph{initial}$ epistemic state is also defined to contain all possible worlds given a finite set of atoms and terms.

\vspace{10pt}
\begin{code}
module AskTell (ask,askModel, tell, tellModel, initial) where

import SyntaxKL
import SemanticsKL
import qualified Data.Set as Set
\end{code}

The $\emph{ask}$ operator determines whether or not a formula is known to a knowledge base. Formally, given an epistemic state $e$ and any sentence $\alpha$ of $\mathcal{KL}$,
$$ask[e,\alpha] = \begin{cases} 
            True &\text{ if } e \models \mathbf{K }\alpha \\
            False &\text{ otherwise }
            \end{cases}
$$
% It's worth noting that Levesque abuses notation here by using "$e \models$", but by the semantics of $K$ it is clear that $\alpha$ must be true in all worlds of $e$.

When implementing $\emph{ask}$ in Haskell, we must take into account that a domain is implied by "$\models$" so that we can evaluate sentences with quantifiers. As such, we will take a domain as our first argument.

\vspace{10pt}
\begin{code}
-- ask (Definition 5.2.1)
ask :: Set.Set StdName -> EpistemicState -> Formula -> Bool
ask d e alpha | Set.null e = False
              | otherwise = satisfiesModel newModel (K alpha) where
              newModel = Model {actualWorld = (Set.findMin e), epistemicState = e, domain = d}

\end{code}

We can simplify this into an \verb?askModel? function that takes only a model and a formula as input.

\vspace{10pt}
\begin{code}
askModel :: Model -> Formula -> Bool
askModel m alpha |  Set.null (epistemicState m) = False
             |  otherwise = satisfiesModel m (K alpha)

\end{code}

The second operation, $\emph{tell}$, asserts that a sentence is true and in doing so reduces which worlds are possible. In practice, $\emph{tell}[\varphi, e]$ filters the epistemic state $e$ to worlds where the sentence $\varphi$ holds. That is,
$$\emph{tell}[\varphi,e] = e \cap \{w \; | \; w \models \varphi \}$$

Again, we run into the issue that "$\models$" requires a domain, and so a domain must be specified to evaluate sentences with quantifiers.

\vspace{10pt}
\begin{code}
-- tell operation
tell :: Set.Set StdName -> EpistemicState -> Formula -> EpistemicState
tell d e alpha = Set.filter filterfunc e where
    filterfunc = (\w -> satisfiesModel (Model {actualWorld = w, epistemicState = e, domain = d}) alpha)
\end{code}

We can again simplify to a function \verb?tellModel?, that takes as input a model and formula and produces a model with a modified epistemic state.

\vspace{10pt}
\begin{code}
tellModel :: Model -> Formula -> Model
tellModel m alpha = Model {actualWorld = actualWorld m, epistemicState = Set.filter filterfunc  (epistemicState m), domain = domain m} where
    filterfunc = (\w -> satisfiesModel (Model {actualWorld = w, epistemicState = epistemicState m, domain = domain m}) alpha)

\end{code}

In addition to $\emph{ask}$ and $\emph{tell}$, it is valuable to define an initial epistemic state. $\emph{initial}$ is the epistemic state before any $\emph{tell}$ operations. This state contains all possible world states as there is nothing known that eliminates any possible world.

\vspace{10pt}
\begin{code}
-- initial operation
-- Generate all possible world states for a finite set of atoms and terms
allWorldStates :: [PrimitiveAtom] -> [PrimitiveTerm] -> [StdName] -> [WorldState]
allWorldStates atoms terms dom = do
   atomVals <- mapM (\_ -> [True, False]) atoms
   termVals <- mapM (\_ -> dom) terms
   return $ mkWorldState (zip atoms atomVals) (zip terms termVals)

initial :: [PrimitiveAtom] -> [PrimitiveTerm] -> [StdName] -> EpistemicState
initial atoms terms dom = Set.fromList (allWorldStates atoms terms dom)


\end{code}

