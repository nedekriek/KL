\section{Comparing KL and Epistemic Logic}
\hide{
\begin{code}
module Translator where

import Data.List
import Data.Maybe
import GHC.Num
import Test.QuickCheck
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad (replicateM)

-- importing syntax and semantics of KL
import SyntaxKL
import SemanticsKL
\end{code}
}

% \subsection{Preliminaries}
We want to compare $\mathcal{KL}$ and Propositional Modal Logic based on Kripke frames (denoted PML). For example, we might want to compare the complexity of model checking for $\mathcal{KL}$ and PML. To do this, we need some way of "translating" between formulas of $\mathcal{KL}$ and formulas of PML, and between $\mathcal{KL}$-models and Kripke models. This would allow us to, e.g., (1) take a set of $\mathcal{KL}$-formulas of various lengths and a set of $\mathcal{KL}$-models of various sizes; (2) translate both formulas and models into PML; (3) do model checking for both (i.e. on the $\mathcal{KL}$ side, and on the PML side).\\
\noindent Three things need to be borne in mind when designing the translation functions:
\begin{itemize}
    \item The language of $\mathcal{KL}$ is predicate logic, plus a knowledge operator $\mathbf{K}$. The language of PML, on the other hand, is propositional logic, plus a knowledge operator. 
    \item Kripke models are much more general than $\mathcal{KL}$ models since epistemic states act as equivalence classes on the accessibility relation.
    \item In Kripke models, there is such a thing as evaluating a formula at various different worlds, whereas this has no equivalent in $\mathcal{KL}$-models. 
\end{itemize}
We deal with the first two points by making some of the translation functions partial; we deal with the third, by, in effect, translating $\mathcal{KL}$ models to pointed Kripke models. Details will be explained in the sections on the respective translation functions below.

\subsection{Syntax and Semantics of PML}

The syntax and semantics of PML is well-known: the language is just the language of basic modal logic, where the Box operator $\Box$ is interpreted as "It is known that...". Models are Kripke models. A mathematical description of all this can be found in any standard textbook on modal logic, so we focus on the implementation, here.\\
\\
% \noindent \textbf{Implementation}\\
\textbf{Syntax}\\
The implementation of PML syntax in Haskell is straightforward.

\vspace{10pt}
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

\end{code}
\hide{
\begin{code}
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
}
\textbf{Semantics}\\
For some parts of our project, it will be most convenient to let Kripke models have \verb?WorldState?s (as defined in \verb?SemanticsKL?) as worlds; for others, to have the worlds be \verb?Integer?s. We therefore implement Kripke models as a polymorphic data type, as follows: 

\vspace{10pt}
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
We will also have to be able to check whether a formula is valid on the frame underlying a Kripke model. This is implemented as follows:
\vspace{10pt}
\begin{code}
-- Maps Propositional Modal Logic to a KL atom
propToAtom :: Proposition -> Atom
propToAtom n = Pred "P" [StdNameTerm (StdName ("n" ++ show n))]  -- e.g., 1 -> P(n1)

-- Creates a KL WorldState from a list of propositional variables????
createWorldState :: [Proposition] -> WorldState
createWorldState props =
  let atomVals = Map.fromList [(propToAtom p, True) | p <- props]  -- Maps each proposition to True
      termVals = Map.empty                                          -- No term valuations needed here
  in WorldState atomVals termVals

-- extract all the propositional variables of a Propositional Modal Logic formula
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

\end{code}

Sometimes it will be useful to convert between models of type \verb?KripkeModel WorldState? and models of type \verb?KripkeModel Integer?. To enable this, we provide the following functions:

\vspace{10pt}
\begin{code}
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
\vspace{10pt}
\begin{code}
instance Show a => Show (KripkeModel a) where
   show (KrM uni val rel) = "KrM\n" ++ show uni ++ "\n" ++ show [(x, val x) | x <- uni ] ++ "\n" ++ show rel
\end{code}

Later, we will want to compare models for equality; so we'll also define an \verb?Eq? instance. Comparison for equality will work, at least as long as models are finite. The way this comparison works is by checking that the valuations agree on all worlds in the model. By sorting before checking for equality, we ensure that the order in which worlds appear in the list of worlds representing the universe, the order in which true propositions at a world appear, and the order in which pairs appear in the relation doesn't affect the comparison.
\vspace{10pt}
\begin{code}
instance (Eq a, Ord a) => Eq (KripkeModel a) where
   (KrM u v r) == (KrM u' v' r') = 
      (nub. sort) u == (nub. sort) u' && all (\w -> (nub. sort) (v w) ==  (nub. sort) (v' w)) u && (nub. sort) r == (nub. sort) r'
\end{code}
\emph{NB:} The following is possible: two models of type \verb?KripkeModel WorldState?s are equal, we convert both to models of type \verb?KripkeModel Integer?s and the resulting models are not equal. Why is this possible? Because when checking for equality between models of type \verb?KripkeModel WorldState?s, we ignore the order of worlds in the list that defines the universe; but for the conversion to \verb?KripkeModel Integer?, the order matters!

\subsection{Translation functions: KL to Kripke}
In our implementation, to do justice to the the fact that translation functions can only sensibly be defined for \emph{some} Kripke models, and \emph{some} $\mathcal{KL}$ formulas, we use the \verb?Maybe? monad provided by Haskell. To do justice to the fact that evaluating in a $\mathcal{KL}$-model is more like evaluating a formula at a specific world in a Kripke model, than like evaluating a formula with respect to a whole Kripke model, we translate from pairs of Kripke models and worlds to $\mathcal{KL}$-models, rather than just from Kripke models to $\mathcal{KL}$-models. Thus, these are the types of our translation functions:
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

We propose that reasonable translation functions should at least satisfy the following constraints: for any $\mathcal{KL}$ model \verb?Model w e d?, any translatable $\mathcal{KL}$ formula \verb?f?, any translatable Kripke model \verb?KrM uni val rel?, and any modal formula \verb?g?,
\begin{enumerate}
\item \emph{Translating formulas back and forth shouldn't change them:}
  \begin{itemize}
  \item \verb?translateFormToKL (fromJust (translateFormToKr f)) = f?
  \item \verb?fromJust (translateFormToKr (translateFormToKL g)) = g?
  \end{itemize}

\item \emph{Truth values should be preserved by the translations:}
  \begin{itemize}
  \item \verb?Model w e d |= f? iff
  \newline
  \verb?(translateModToKr (Model w e d)) w |= fromJust (translateFormToKr f)?

  \item \verb?(KrM uni val rel) w |= g? iff 
  \newline
  \verb?fromJust (kripkeToKL (KrM uni val rel) w) |= translateFormToKL g?
  \end{itemize}
\end{enumerate}

We check that our translation formulas do indeed satisfy these constraint in the test suite (in \verb?TranslatorSpec.lhs?).

\subsection{Translating from $\mathcal{KL}$ to Kripke}
\textbf{Translation Functions for Formulas}\\
As mentioned above, we translate from a fragment of the language of $\mathcal{KL}$ to the language of propositional modal logic. Specifically, only formulas whose atomic subformulas consist of the predicate letter "P", followed by exactly one standard name, are translated; in this case the function \verb?translateFormToKr? replaces all of the atomic subformulas by propositional variables.
\vspace{10pt}
\begin{code}
translateFormToKr :: Formula -> Maybe ModForm
translateFormToKr (Atom (Pred "P" [StdNameTerm (StdName nx)])) = Just $ P (read (drop 1 nx))    
translateFormToKr (Not f)                        =  Neg <$> translateFormToKr f           
translateFormToKr (Or f g)                       = fmap Dis (translateFormToKr f) <*> translateFormToKr g 
translateFormToKr (K f)                          = Box <$> translateFormToKr f
translateFormToKr _                              = Nothing
\end{code}

\textbf{Translation Functions for Models}\\
The function \verb?translateModToKr? takes a $\mathcal{KL}$ model, and returns a Kripke model, where 
\begin{itemize}
\item the worlds are all the world states in the epistemic state of the $\mathcal{KL}$ model, plus the actual world state;
\item for each world, the propositional variables true at it are the translations of the atomic formulas consisting of "P" followed by a standard name that are true at the world state;
\item the worlds from within the epistemic state all see each other, and themselves; and the actual world sees all other worlds.
\end{itemize}
\vspace{10pt}
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

\subsection{Translating from Propositional Modal Logic to $\mathcal{KL}$}

\textbf{Translation Functions for Formulas}\\
The function \verb?translateFormToKL? takes a formula of propositional modal logic and computes the translated $\mathcal{KL}$ formula. Since PML is a propositional logic, we will immitate this in the language of $\mathcal{KL}$ by translating it to a unique corresponding atomic formula in $\mathcal{KL}$.

\vspace{10pt}
\begin{code}
-- Translates a formula of propositional modal logic to a KL formula (predicate logic with knowledge operator).
translateFormToKL :: ModForm -> Formula
translateFormToKL (P n) = Atom (Pred "P" [StdNameTerm (StdName ("n" ++ show n))])  -- Maps proposition P n to atom P(n), e.g., P 1 -> P(n1)
translateFormToKL (Neg form) = Not (translateFormToKL form)                          -- Negation is preserved recursively
translateFormToKL (Dis form1 form2) = Or (translateFormToKL form1) (translateFormToKL form2)
translateFormToKL (Box form) = K (translateFormToKL form)                            -- Box becomes K, representing knowledge

\end{code}

\textbf{Translation Functions for Models}\\
The function \verb?kripkeToKL? takes a Kripke model and a world in its universe, and computes a corresponding $\mathcal{KL}$-model which is satisfiability equivalent with the given world in the given model.\\
\noindent $\mathcal{KL}$ models and Kripke Models can both be used to represent an agent's knowledge, but they do it in a very different way. A $\mathcal{KL}$ model $(e,w)$ is an ordered pair of a \textit{world state} $w$, representing what is true in the real world, and an \textit{epistemic state} $e$, representing what the agent considers possible. By contrast, a Kripke model $\mathcal{M} = (W,R,V)$ consists of a universe $W$, an accessibility relation $R \subseteq W\times W$, and a valuation function $V: Prop \rightarrow \mathcal{P}(W)$ that assigns to each propositional letter the set of worlds in which it is true.\\
There are two key differences between $\mathcal{KL}$ models and Kripke Models. First, $\mathcal{KL}$ models have a fixed actual world and can only evaluate non-modal formulas at this particular world while Kripke Models can evaluate what is true at each of the worlds in their Universe. Second, the \textit{world states} in the \textit{epistemic state} of a $\mathcal{KL}$ model form an equivalence class in the sense that no matter how many nested \textit{K-Operators} there are in a formula, each level is evaluated on the whole epistemic state. Among other things, this implies that positive introspection ($\mathbf{K}\varphi \rightarrow \mathbf{K}\mathbf{K}\varphi$) and negative introspection ($\neg\mathbf{K} \varphi \rightarrow \mathbf{K}\neg\mathbf{K}\varphi$) are valid in $\mathcal{KL}$. Informally, positive introspection says that if an agent knows \( \varphi \), then they know that they know \( \varphi \) and negative introspection says that if an agent does not know \( \varphi \), then they know that they do not know \( \varphi \). In Kripke models, however, this is not generally the case and the worlds accessible from each world do not always form an equivalence class under the accessibility relation $R$.\\
We address the first difference by not translating the entire Kripke Model but by selecting an actual world in the Kripke model and then translating the submodel point generated at this world into a $\mathcal{KL}$ model. By design, the selected actual world is translated to the actual \textit{world state} and the set of worlds accessible from the selected world is translated to the \textit{epistemic state}. Further, we restrict the translation function to only translate the fragment of Kripke Models where the set of worlds accessible from each world in the universe form an equivalence class with respect to $R$.\\
This gives us a translation function \verb?kripkeToKL? of type\\ \verb?kripkeToKL :: KripkeModel WorldState -> WorldState -> Maybe Model? \\

\textbf{Constraints on Translatable Kripke Models}\\
To ensure that the set of worlds accessible from each world in the universe form an equivalence class with respect to $R$, we require the Kripke model to be transitive ($\forall u,v,w ((Ruv \wedge Rvw) \rightarrow Ruw)$) and euclidean ($\forall u,v,w ((Ruv \wedge Ruw) \rightarrow Rvw)$). 
For this, we implement the following two functions that check whether a Kripke model is transitive and euclidean, respectively:
\vspace{10pt}
\begin{code}
-- Checks whether a Kripke model is Euclidean
isEuclidean :: (Eq a, Ord a) => KripkeModel a -> Bool
isEuclidean = isValidKr (Dis (Box (Neg (P 1))) (Box (dia (P 1))))  -- \Box \neg P1 \lor \Box \Diamond P1 holds for Euclidean relations

-- Checks whether a Kripke model is transitive
isTransitive :: (Eq a, Ord a) => KripkeModel a -> Bool
isTransitive = isValidKr (Dis (Neg (Box (P 1))) (Box (Box (P 1))))  -- \neg \Box P1 \lor \Box \Box P1 holds for transitive relations

\end{code}

We further need the constraint that the world selected to be the actual world in the Kripke Model is in the universe of the given Kripke Model. This is ensured by the \verb?isInUniv? function.

\vspace{10pt}
\begin{code}
-- Checks whether a world is in the Kripke model’s universe
isInUniv :: WorldState -> [WorldState] -> Bool
isInUniv = elem  -- Simple membership test

\end{code}

\textbf{Main Function to Translate Kripke Models}\\
With this, we can now define the \verb?kripkeToKL? function that maps a Kripke Model of type \verb?KripkeModel WorldState? and a \verb?WorldState? to a \verb?Just? $\mathcal{KL}$? \verb?Model? if the Kripke Model is transitive and euclidean and the selected world state is in the universe of the Kripke Model and to \verb?Nothing? otherwise.

\vspace{10pt}
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
\end{code}