\section{Comparing KL and Epistemic Logic}
\begin{code}
module Translator where

import Data.List
import Data.Maybe
import GHC.Num
import Test.QuickCheck
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad (replicateM)

-- importing syntax and semantics of KL
import SyntaxKL
import SemanticsKL
\end{code}

\subsection{Preliminaries}
We want to compare $\mathcal{KL}$ and Standard Epistemic Logic based on Kripke frames. (Call this SEL). For example, we might want to compare the complexity of model checking for $\mathcal{KL}$ and SEL. To do this, we need some way of "translating" between formulas of $\mathcal{KL}$ and formulas of SEL, and between $\mathcal{KL}$-models and Kripke frames. This would allow us to, e.g., (1) take a set of $\mathcal{KL}$-formulas of various lengths and a set of $\mathcal{KL}$-models of various sizes; (2) translate both formulas and models into SEL; (3) do model checking for both (i.e.. on the $\mathcal{KL}$ side, and on the SEL side); (4) compare how time and memory scale with length of formula.\\
\noindent Three things need to be borne in mind when designing the translation functions:
\begin{enumerate}
    \item The language of $\mathcal{KL}$ is predicate logic, plus a knowledge operator $\mathbf{K}$. The language of SEL, on the other hand, is propositional logic, plus a knowledge operator. So we can only translate from a fragment of the language of $\mathcal{KL}$ to SEL.
    \item Kripke models are much more general than $\mathcal{KL}$-models. So we can only translate from a fragment of the set of Kripke models into $\mathcal{KL}$-models.
    \item In Kripke models, there is such a thing as evaluating a formula at various different worlds, whereas this has no equivalent in $\mathcal{KL}$-models. We need to take this fact into account when thinking about adequacy criteria for a translation function.
\end{enumerate}

\subsection{Syntax and Semantics of SEL}

The syntax and semantics of SEL is well-known: the language is just the language of basic modal logic, where the Box operator $\Box$ is interpreted as "It is known that...". Models are Kripke models. A mathematical description of all this can be found in any standard textbook on modal logic, so we focus on the implementation, here.\\
\\
\noindent \textbf{Implementation}\\
\textbf{Syntax}\\

\begin{code}
data ModForm = P Proposition
             | Neg ModForm
             | Dis ModForm ModForm
             | Box ModForm
             deriving (Eq,Ord,Show)

dia :: ModForm -> ModForm
dia f = Neg (Box (Neg f))

con :: ModForm -> ModForm -> ModForm
con f g = Neg (Dis (Neg f) (Neg g))

impl :: ModForm -> ModForm -> ModForm
impl f = Dis (Neg f)

-- this will be useful for testing later
instance Arbitrary ModForm where
  arbitrary = resize 16 (sized randomForm) where
    randomForm :: Int -> Gen ModForm
    randomForm 0 = P <$> elements [1..5]
    randomForm n = oneof [ Neg <$> randomForm (n `div` 2)
                         , Dis <$> randomForm (n `div` 2)
                                <*> randomForm (n `div` 2)
                         , Box <$> randomForm (n `div` 2) ]
\end{code}

\underline{\textbf{Semantics}}

For some parts of our project, it will be most convenient to let Kripke models have \verb?WorldState?s (as defined in \verb?SemanticsKL?) as worlds; for others, to have the worlds be \verb?Integer?s. We therefore implement Kripke models as a polymorphic data type, as follows: 

\begin{code}
--definition of models
type World a = a
type Universe a = [World a]
type Proposition = Int

type Valuation a = World a -> [Proposition]
type Relation a = [(World a,World a)]

data KripkeModel a = KrM 
   { universe :: Universe a
   , valuation :: Valuation a
   , relation :: Relation a}

--definition of truth for modal formulas
--truth at a world
makesTrue :: Eq a => (KripkeModel a, World a) -> ModForm -> Bool
makesTrue (KrM _ v _, w) (P k)     = k `elem` v w
makesTrue (m,w)          (Neg f)   = not (makesTrue (m,w) f)
makesTrue (m,w)          (Dis f g) = makesTrue (m,w) f || makesTrue (m,w) g
makesTrue (KrM u v r, w) (Box f)   = all (\w' -> makesTrue (KrM u v r,w') f) (r ! w)

(!) :: Eq a => Relation a -> World a -> [World a]
(!) r w = map snd $ filter ((==) w . fst) r

--truth in a model
trueEverywhere :: Eq a => KripkeModel a -> ModForm -> Bool
trueEverywhere (KrM x y z) f = all (\w -> makesTrue (KrM x y z, w) f) x

\end{code}

Sometimes it will be useful to convert between models of type \verb?KripkeModel WorldState? and models of type \verb?KripkeModel Integer?. To enable this, we provide the following functions:

\begin{code}
--KripkeModel to IntKripkeModel
translateKrToKrInt :: KripkeModel WorldState -> KripkeModel Integer
translateKrToKrInt (KrM u v r) = KrM u' v' r' where
   ur = nub u -- the function first gets rid of duplicate worlds in the model
   u' = take (length ur) [0..] 
   v' n = v (intToWorldState ur n) where
      intToWorldState :: Universe WorldState -> Integer -> WorldState
      intToWorldState urc nq = urc !! integerToInt nq
   r' = [(worldStateToInt ur w, worldStateToInt ur w') | (w,w') <- r] where
      worldStateToInt :: Universe WorldState-> WorldState -> Integer
      worldStateToInt uni w = toInteger $ fromJust $ elemIndex w uni 

convertToWorldStateModel :: KripkeModel Integer -> KripkeModel WorldState
convertToWorldStateModel (KrM intUniv intVal intRel) =
  let worldStates = map makeWorldState intUniv
      worldToInt :: WorldState -> Integer
      worldToInt ws = case find (\(_, w) -> w == ws) (zip intUniv worldStates) of
                        Just (i, _) -> i
                        Nothing -> error "WorldState not found in universe"
      newVal :: Valuation WorldState
      newVal ws = intVal (worldToInt ws)
      newRel :: Relation WorldState
      newRel = [(makeWorldState i, makeWorldState j) | (i, j) <- intRel]
  in KrM worldStates newVal newRel

makeWorldState :: Integer -> WorldState
makeWorldState n =
  let uniqueAtom = PPred "WorldID" [StdName (show n)]
  in mkWorldState [(uniqueAtom, True)] []

\end{code}

To be able to print models, we define a \verb?Show? instance for \verb?KripkeModel a?:
\begin{code}
instance Show a => Show (KripkeModel a) where
   show (KrM uni val rel) = "KrM\n" ++ show uni ++ "\n" ++ show [(x, val x) | x <- uni ] ++ "\n" ++ show rel
\end{code}

Later, we will want to compare models for equality; so we'll also define an \verv?Eq? instance. Comparison for equality will work, at least as long as models are finite. The way this comparison works is by checking that the valuations agree on all worlds in the model. By sorting before checking for equality, we ensure that the order in which worlds appear in the list of worlds representing the universe, the order in which true propositions at a world appear, and the order in which pairs appear in the relation doesn't affect the comparison.
\begin{code}
instance (Eq a, Ord a) => Eq (KripkeModel a) where
   (KrM u v r) == (KrM u' v' r') = 
      (nub. sort) u == (nub. sort) u' && all (\w -> (nub. sort) (v w) ==  (nub. sort) (v' w)) u && (nub. sort) r == (nub. sort) r'
\end{code}
\emph{NB:} the following is possible: Two models of type \verb?KripkeModel WorldState?s are equal, we convert both to models of type \verb?KripkeModel Integer?s and the resulting models are not equal. \\

Why is this possible? Because when checking for equality between models of type \verb?KripkeModel WorldState?s, we ignore the order of worlds in the list that defines the universe; but for the conversion to \verb?KripkeModel Integer?, the order matters!

\subsection{Translation functions: KL to Kripke}
\textbf{Desiderata}\\
In our implementation, to do justice to the the fact that translation functions can only sensibly be defined for \emph{some} Kripke models, and \emph{some} $\mathcal{KL}$ formulas, we use the \verb?Maybe? monad provided by Haskell.\\
To do justice to the fact that evaluating in a $\mathcal{KL}$-model is more like evaluating a formula at a specific world in a Kripke model, than like evaluating a formula with respect to a whole Kripke model, we translate from pairs of Kripke models and worlds to $\mathcal{KL}$-models, rather than just from Kripke models to $\mathcal{KL}$-models. \\
Thus, these are the types of our translation functions:
\begin{enumerate}
\item \begin{verbatim}
translateFormToKr :: Formula -> Maybe ModForm
\end{verbatim}

\item \begin{verbatim}
translateFormToKL :: ModForm -> Formula
\end{verbatim}

\item \begin{verbatim}
translateModToKr :: Model -> KripkeModel WorldState
\end{verbatim}

\item \begin{verbatim}
kripkeToKL :: KripkeModel WorldState -> WorldState -> Maybe Model
\end{verbatim}
\end{enumerate}

What constraints do we want our translation functions to satisfy? We propose that reasonable translation functions should at least satisfy these constraints: for any $\mathcal{KL}$ model \verb?Model w e d?, any translatable $\mathcal{KL}$ formula \verb?f?, any translatable Kripke model \verb?KrM uni val rel?, and any modal formula \verb?g?,
\begin{enumerate}
\item Truth values should be preserved by the translations:
  \begin{itemize}
  \item \verb?Model w e d |= f? iff
  \newline
  \verb?(translateModToKr (Model w e d)) w |= fromJust (translateFormToKr f)?

  \item \verb?(KrM uni val rel) w |= g? iff 
  \newline
  \verb?fromJust (kripkeToKL (KrM uni val rel) w) |= translateFormToKL g?
  \end{itemize}

\item Translating formulas back and forth shouldn't change them:
  \begin{itemize}
  \item \verb?translateFormToKL (fromJust (translateFormToKr f)) = f?
  \item \verb?fromJust (translateFormToKr (translateFormToKL g)) = g?
  \end{itemize}
\end{enumerate}

We check that our translation formulas do indeed satisfy these constraint in the test suite (in \verb?TranslatorSpec.lhs?).

\textbf{Implementation}\\
Now we get to the implementation of our translation functions.

\subsection{Translation functions from $\mathcal{KL}$ to Kripke}
\textbf{Translation functions for formulas}\\
\verb?translateFormToKr? replaces all of the atomic
subformulas consisting of the predicate letter "P", followed by a standard name by propositional variables; it returns \verb?Nothing? if the input formula doesn't satisfy this constraint.
\begin{code}
translateFormToKr :: Formula -> Maybe ModForm
translateFormToKr (Atom (Pred "P" [StdNameTerm (StdName nx)])) = Just $ P (read (drop 1 nx))    
translateFormToKr (Not f)                        =  Neg <$> translateFormToKr f           
translateFormToKr (Or f g)                       = fmap Dis (translateFormToKr f) <*> translateFormToKr g 
translateFormToKr (K f)                          = Box <$> translateFormToKr f
translateFormToKr _                              = Nothing
\end{code}

\textbf{Translation functions for models}\\
\verb?translateModToKr? takes a $\mathcal{KL}$ model, and returns a Kripke model, where 
\begin{itemize}
\item the worlds are all the world states in the epistemic state of the $\mathcal{KL}$ model, plus the actual world state;
\item for each world, the propositional variables true at it are the translations of the atomic formulas consisting of "P" followed by a standard name that are true at the world state;
\item the from within the epistemic state all see each other, and the actual world sees all other worlds.
\end{itemize}
\begin{code}
translateModToKr :: Model -> KripkeModel WorldState
translateModToKr (Model w e _) = KrM (nub (w:Set.toList e)) val (nub rel) where
   val = trueAtomicPropsAt
   rel = [(v, v') | v <- Set.toList e, v' <- Set.toList e] ++ [(w,v) | v <- Set.toList e]

--the next two are helper functions:

--identifies true atomic formulas at a world that consist of the predicate "P" followed by a standard name
trueAtomicPropsAt :: WorldState -> [Proposition]
trueAtomicPropsAt w = 
   map actualAtomToProp trueActualAtoms where
      trueActualAtoms = filter isActuallyAtomic $ map fst (filter snd (Map.toList (atomValues w)))
      actualAtomToProp :: Atom -> Proposition 
      actualAtomToProp (Pred "P" [StdNameTerm (StdName nx)]) = read (drop 1 nx)
      actualAtomToProp _ = error "actualAtomToProp should only be given atoms of the form 'P(standardname)' as input"

--checks whether an atomic formula consists of the predicate "P" followed by a standard name
isActuallyAtomic :: Atom -> Bool
isActuallyAtomic (Pred "P" [StdNameTerm (StdName _)]) = True
isActuallyAtomic _ = False
\end{code}

\subsection{Translation functions from Kripke to $\mathcal{KL}$}

\textbf{Translation functions for formulas}\\
\verb?translateFormToKL? takes a formula of SEL
and computes the translated $\mathcal{KL}$ formula. Since SEL is a propositional logic, we will immitate this in the language of $\mathcal{KL}$
by translating it to a unique corresponding atomic formula in $\mathcal{KL}$.

\begin{code}
-- Translates an SEL formula (propositional modal logic) to a KL formula (predicate logic with knowledge operator).
translateFormToKL :: ModForm -> Formula
translateFormToKL (P n) = Atom (Pred "P" [StdNameTerm (StdName ("n" ++ show n))])  -- Maps proposition P n to atom P(n), e.g., P 1 -> P(n1)
translateFormToKL (Neg form) = Not (translateFormToKL form)                          -- Negation is preserved recursively
translateFormToKL (Dis form1 form2) = Or (translateFormToKL form1) (translateFormToKL form2)
translateFormToKL (Box form) = K (translateFormToKL form)                            -- Box becomes K, representing knowledge

\end{code}

\textbf{Translation functions for models}\\
\verb?kripkeToKL? takes a Kripke model and a world in its universe
and computes a corresponding $\mathcal{KL}$-model which is satisfiability equivalent with the given world in the given model.\\

\noindent $\mathcal{KL}$ models and Kripke models are frameworks used to represent an agent's knowledge in epistemic logic, but they differ in their structure and approach. A $\mathcal{KL}$ model explicitly separates:
\begin{itemize}
\item An \textit{actual world state}, representing what is true in the real world.
\item A set of \textit{epistemic world states}, representing the worlds the agent considers possible based on their knowledge.
\end{itemize}
In contrast, a Kripke model consists of:
\begin{itemize}
\item A set of possible worlds;
\item An accessibility relation between worlds, where an agent knows a proposition \( p \) at a world \( w \) if \( p \) is true in all worlds accessible from \( w \).
\end{itemize}
The task of translating a Kripke model into a $\mathcal{KL}$-model involves preserving both:
\begin{enumerate}
  \item \textit{What is true} in the actual world.
  \item \textit{What the agent knows} in that world.
\end{enumerate}
To perform this translation, we take a Kripke model and a specified world \( w \) (designated as the actual world) and construct a $\mathcal{KL}$-model where:
\begin{itemize}
\item The \textit{actual world state} corresponds to \( w \).
\item The \textit{epistemic state} consists of all worlds accessible from \( w \) in the Kripke model.
\end{itemize}
However, not all Kripke models can be straightforwardly translated into $\mathcal{KL}$-models while maintaining the semantics of knowledge as defined in $\mathcal{KL}$. In $\mathcal{KL}$, knowledge of a proposition \( p \) means that \( p \) is true in all world states within the epistemic state. 
This imposes specific requirements on the structure of the Kripke model's accessibility relation to ensure compatibility with KL's properties of knowledge.\\

\noindent \textbf{Restrictions on Kripke Models: Transitivity and Euclideanness}\\

In $\mathcal{KL}$, knowledge exhibits introspective properties, such as:
\begin{itemize}
\item \textit{Positive introspection}: If an agent knows \( p \), then they know that they know \( p \) (formally, \( Kp \rightarrow KKp \)).
\item \textit{Negative introspection}: If an agent does not know \( p \), then they know that they do not know \( p \) (formally, \( \neg Kp \rightarrow K\neg Kp \)).
\end{itemize}
These properties imply that the epistemic state must be consistent and stable across all worlds the agent considers possible. 
Specifically, for any proposition \( p \), the formula \( KKp \) (the agent knows that they know \( p \)) should hold if and only if \( Kp \) (the agent knows \( p \)) holds. 
This equivalence requires the set of worlds in the epistemic state to have a uniform structure.\\
To capture these introspective properties in a Kripke model, the accessibility relation must satisfy:
\begin{itemize}
  \item \textit{Transitivity}: If world \( w \) can access world \( v \) (i.e., \( w \rightarrow v \)), and \( v \) can access world \( u \) (i.e., \( v \rightarrow u \)), then \( w \) must access \( u \) (i.e., \( w \rightarrow u \)). 
  This ensures that the agent's knowledge extends consistently across all accessible worlds, supporting positive introspection.
  \item \textit{Euclideanness}: If \( w \rightarrow v \) and \( w \rightarrow u \), then \( v \rightarrow u \). 
  This means that any two worlds accessible from \( w \) must be accessible to each other, which is necessary for negative introspection.
\end{itemize}
When a Kripke model's accessibility relation is both transitive and Euclidean, the set of worlds accessible from \( w \) forms an \textit{equivalence class}. 
In an equivalence class, every world is accessible from every other world (including itself, implying reflexivity), and the set is fully connected, meaning the agent's knowledge is uniform across all worlds in the epistemic state.\\
This fully connected structure aligns with the $\mathcal{KL}$ model's epistemic state, where a proposition is known only if it holds in all possible worlds the agent considers. 
If the worlds accessible from \( w \) did not "see each other" (i.e., were not mutually accessible), introspective knowledge claims like \( KKp \leftrightarrow Kp \) could not be preserved, as the agent's knowledge would vary inconsistently across the accessible worlds.

\subsubsection*{The Actual World and the Possibility of Knowing Falsehoods}

A key feature of $\mathcal{KL}$ models is that the agent can know something false. 
This means that the actual world state (representing the true state of affairs) does not necessarily belong to the epistemic state (the worlds the agent considers possible). 
For example, an agent might believe a false proposition, leading them to exclude the actual world from their epistemic state. In the translation from a Kripke model to a $\mathcal{KL}$  model, we designate \( w \) as the actual world state. The epistemic state includes only the worlds accessible from \( w \), which may or may not include \( w \) itself.\\

This flexibility distinguishes $\mathcal{KL}$  models from some traditional Kripke-based systems (e.g., S5, where the actual world is typically accessible due to reflexivity), allowing $\mathcal{KL}$ to model scenarios where an agent's knowledge deviates from reality.

\subsubsection*{Conditions for Translation}

To successfully translate a Kripke model into a $\mathcal{KL}$ model, the accessibility relation must be \textit{transitive and Euclidean}, ensuring that the worlds accessible from \( w \) form an equivalence class. The translation process then sets the actual world state of the KL model to \( w \), and defines the epistemic state as the set of all worlds accessible from \( w \) in the Kripke model.\\

If the Kripke model's accessibility relation is not transitive and Euclidean, the translation cannot preserve the introspective properties of knowledge required by $\mathcal{KL}$, and thus it fails. 
In practice, this restriction is implemented in the function below, which takes a Kripke model and a world \( w \) as input, verifies that the accessibility relation satisfies transitivity and Euclideanness, and then returns a $\mathcal{KL}$ model if the conditions are met, or an indication of failure (e.g.,\verb?Nothing?) otherwise.

\subsubsection*{Example and Intuition}

Consider a Kripke model with worlds \( \{w, v, u\} \), where:
\begin{itemize}
  \item \( w \rightarrow v \) and \( w \rightarrow u \), but \( v \not\rightarrow u \) (not Euclidean).
  \item At \( w \), the agent knows \( p \) if \( p \) is true in \( v \) and \( u \).
\end{itemize}
If \( p \) is true in \( v \) and \( u \), then \( \mathbf{K}p \) holds at \( w \). However, for \( \mathbf{K}\mathbf{K}p \) to hold, \( \mathbf{K}p \) must be true in both \( v \) and \( u \). If \( v \not\rightarrow u \), then \( \mathbf{K}p \) might not hold at \( v \) (since \( v \) does not access \( u \)), breaking the equivalence \( \mathbf{K}\mathbf{K}p \leftrightarrow \mathbf{K}p \). 
In a $\mathcal{KL$} model, the epistemic state must ensure mutual accessibility to avoid such inconsistencies, which is why transitivity and Euclideanness are required.

\begin{code}
-- Main function: Convert Kripke model to KL model
kripkeToKL :: KripkeModel WorldState -> WorldState -> Maybe Model
kripkeToKL kr@(KrM univ val rel) w
  | not (isEuclidean kr && isTransitive kr) || not (isInUniv w univ) = Nothing
  | otherwise = Just (Model newWorldState newEpistemicState newDomain)
  where
    -- New actual world based on valuation of w
    newWorldState = createWorldState (val w)
    -- Accessible worlds from w
    accessibleWorlds = [v | (u, v) <- rel, u == w]
    -- New epistemic state: one WorldState per accessible world
    newEpistemicState = Set.fromList [createWorldState (val v) | v <- accessibleWorlds]
    -- Domain (empty for simplicity)
    newDomain = Set.empty

-- Maps an SEL proposition to a KL atom
propToAtom :: Proposition -> Atom
propToAtom n = Pred "P" [StdNameTerm (StdName ("n" ++ show n))]  -- e.g., 1 -> P(n1)

-- Creates a KL WorldState from a list of propositions
createWorldState :: [Proposition] -> WorldState
createWorldState props =
  let atomVals = Map.fromList [(propToAtom p, True) | p <- props]  -- Maps each proposition to True
      termVals = Map.empty                                          -- No term valuations needed here
  in WorldState atomVals termVals

-- Checks if a world is in the Kripke model’s universe
isInUniv :: WorldState -> [WorldState] -> Bool
isInUniv = elem  -- Simple membership test

-- Helper: functions as provided
uniqueProps :: ModForm -> [Proposition]
uniqueProps f = nub (propsIn f)
  where
    propsIn (P k)       = [k]
    propsIn (Neg g)     = propsIn g
    propsIn (Dis g h)   = propsIn g ++ propsIn h
    propsIn (Box g)     = propsIn g

-- Generate all possible valuations explicitly
allValuations :: Ord a => [World a] -> [Proposition] -> [Valuation a]
allValuations univ props = 
  let subsetsP = subsequences props
      allAssignments = replicateM (length univ) subsetsP
  in [ \w -> Map.findWithDefault [] w (Map.fromList (zip univ assignment))
     | assignment <- allAssignments ]

-- Checks whether a Kripke formula is valid on a given Kripke model 
isValidKr :: (Eq a, Ord a) => ModForm -> KripkeModel a -> Bool
isValidKr f (KrM univ _ rel) = 
  let props = uniqueProps f
      valuations = allValuations univ props
  in all (\v -> all (\w -> makesTrue (KrM univ v rel, w) f) univ) valuations

-- Checks if a Kripke model is Euclidean
isEuclidean :: (Eq a, Ord a) => KripkeModel a -> Bool
isEuclidean = isValidKr (Dis (Box (Neg (P 1))) (Box (dia (P 1))))
  -- \Box \neg P1 \lor \Box \Diamond P1 holds for Euclidean relations

-- Checks if a Kripke model is transitive
isTransitive :: (Eq a, Ord a) => KripkeModel a -> Bool
isTransitive = isValidKr (Dis (Neg (Box (P 1))) (Box (Box (P 1))))  -- \neg \Box P1 \lor \Box \Box P1 holds for transitive relations
\end{code}