{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
\section{Comparing KL and Epistemic Logic}
\begin{code}
module Translator where

import Data.List
import Data.Maybe
import GHC.Num

-- importing syntax and semantics of KL
import SyntaxKL
import SemanticsKL

import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
\end{code}

\subsection{Preliminaries}
We want to compare KL and Standard Epistemic Logic based on Kripke frames.
(Call this SEL).
For example, we might want to compare the complexity of model checking
for KL and SEL. 
To do this, we need some way of “translating” between formulas of KL and
formulas of SEL, and between KL-models and Kripke frames. This would allow us to,
e.g., (1) take a set of KL formulas of various lengths and a set of KL models
of various sizes; (2) translate both formulas and models into SEL; (3) do model
checking for both (i.e.. on the KL side, and on the SEL side); (4) compare how 
time/memory scales with length of formula.

Three things to note:
\begin{enumerate}
    \item The language of KL is predicate logic, plus a knowledge operator.
    The language of SEL, on the other hand, is propositional logic, plus
    a knowledge operator. So we can only translate from a fragment of 
    the language of KL to SEL.
    \item Kripke models are much more general than KL models. So we can only
    translate from a fragment of the set of Kripke models into KL models.
    \item In Kripke models, there is such a thing as evaluating a formula 
    at a specific world, whereas this has no equivalent in KL models. We need
    to take this fact into account when thinking about adequacy criteria for
    a translation function.
\end{enumerate}

\subsection{Syntax and Semantics of SEL}

The syntax and semantics of SEL is well-known: the language is just 
the language of basic modal logic, where the Box operator is interpreted
as “It is known that…”. Models are Kripke models. All this is known from HW2,
so we focus on the implementation, here.

\subsubsection{Implementation}
\subsubsubsection{Syntax}

\begin{code}
data ModForm = P Proposition
             | Neg ModForm
             | Con ModForm ModForm
             | Box ModForm
             | Dia ModForm
             deriving (Eq,Ord,Show)

disj :: ModForm -> ModForm -> ModForm
disj f g = Neg (Con (Neg f) (Neg g))

impl :: ModForm -> ModForm -> ModForm
impl f = disj (Neg f)
\end{code}

This is taken from HW2, with one modification: we use "Neg" instead of "Not" as a type constructor 
for negated modal formula, since "Not" is already being used as a type constructor for KL-formulas 
(see "SyntaxKL" for details).

\subsubsubsection{Semantics}

To represent Kripke Models, we will use the types from HW 2, with a twist: we let
the worlds be WorldStates, as defined in "Semantics". This simplifies the translation
functions, and doesn't matter mathematically, as the internal constitution
of the worlds in a Kripke Model is mathematically irrelevant.

\begin{code}
--definition of models
type World = WorldState
type Universe = [World]
type Proposition = Int

type Valuation = World -> [Proposition]
type Relation = [(World,World)]

data KripkeModel = KrM 
   { universe :: Universe
   , valuation :: Valuation 
   , relation :: Relation }

--definition of truth for modal formulas
--truth at a world
makesTrue :: (KripkeModel,World) -> ModForm -> Bool
makesTrue (KrM _ v _, w) (P k)     = k `elem` v w
makesTrue (m,w)          (Neg f)   = not (makesTrue (m,w) f)
makesTrue (m,w)          (Con f g) = makesTrue (m,w) f && makesTrue (m,w) g
makesTrue (KrM u v r, w) (Dia f)   = any (\w' -> makesTrue (KrM u v r, w') f) (r ! w)
makesTrue (KrM u v r, w) (Box f)   = all (\w' -> makesTrue (KrM u v r,w') f) (r ! w)

(!) :: Relation -> World -> [World]
(!) r w = map snd $ filter ((==) w . fst) r

--truth in a model
trueEverywhere :: KripkeModel -> ModForm -> Bool
trueEverywhere (KrM x y z) f = all (\w -> makesTrue (KrM x y z, w) f) x
\end{code}

Sometimes, it will still be useful to represent Kripke Models in the old way,
using Integers as worlds. We therefore define an additional type IntKripkeModel:

\begin{code}
type IntWorld = Integer
type IntUniverse = [IntWorld]
type IntValuation = IntWorld -> [Proposition]
type IntRelation = [(IntWorld, IntWorld)]
data IntKripkeModel = IntKrM IntUniverse IntValuation IntRelation
\end{code}

Sometimes it will also be usefuel to convert between KripkeModels and IntKripkeModels. 
To enable this, we provide the following functions:

\begin{code}

--KripkeModel to IntKripkeModel
translateKrToKrInt :: KripkeModel -> IntKripkeModel
translateKrToKrInt (KrM u v r) = IntKrM u' v' r' where
   ur = nub u -- the function first gets rid of duplicate worlds in the model
   u' = take (length ur) [0..] 
   v' n = v (intToWorldState ur n) where
      intToWorldState :: Universe -> Integer -> WorldState
      intToWorldState urc nq = urc !! integerToInt nq
   r' = [(worldStateToInt ur w, worldStateToInt ur w') | (w,w') <- r] where
      worldStateToInt :: Universe -> WorldState -> Integer
      worldStateToInt uni w = toInteger $ fromJust $ elemIndex w uni 

convertToWorldStateModel :: IntKripkeModel -> KripkeModel
convertToWorldStateModel (IntKrM intUniv intVal intRel) =
  let worldStates = map makeWorldState intUniv
      worldToInt :: WorldState -> Integer
      worldToInt ws = case find (\(i, w) -> w == ws) (zip intUniv worldStates) of
                        Just (i, _) -> i
                        Nothing -> error "WorldState not found in universe"
      newVal :: Valuation
      newVal ws = intVal (worldToInt ws)
      newRel :: Relation
      newRel = [(makeWorldState i, makeWorldState j) | (i, j) <- intRel]
  in KrM worldStates newVal newRel

makeWorldState :: Integer -> WorldState
makeWorldState n =
  let uniqueAtom = PPred "WorldID" [StdName (show n)]
  in mkWorldState [(uniqueAtom, True)] []

\end{code}

To be able to print Models, let's define a Show instance for IntKripkeModels, and for KripkeModels:
\begin{code}
instance Show IntKripkeModel where
   show (IntKrM uni val rel) = "IntKrM\n" ++ show uni ++ "\n" ++ show [(x, val x) | x <- uni ] ++ "\n" ++ show rel
\end{code}
We also define a Show Instance for KripkeModels, which just shows the KripkeModel, converted to an
IntKripkeModel; the rationale for this is that Integers look much nicer than WorldStates when printed.
\begin{code}
instance Show KripkeModel where
   show m = show $ translateKrToKrInt m
\end{code}
Note that we are breaking with the convention that the show function should return what you need to type into 
ghci to define the object; however, we feel justified in doing this because of the greater user friendliness 
it provides.

Later, we will want to compare models for equality; so we'll also define an Eq instance. Comparison for
equality will work, at least as long as models are finite. The way this comparison works is by checking that 
the valuations agree on all worlds in the model. By sorting before checking for equality, we ensure that the order in which 
worlds appear in the list of worlds representing the universe, the order in which true propositions at a world appear, 
and the order in which pairs appear in the relation doesn't affect the comparison.
\begin{code}
instance Eq KripkeModel where
   (KrM u v r) == (KrM u' v' r') = 
      (nub. sort) u == (nub. sort) u' && all (\w -> (nub. sort) (v w) ==  (nub. sort) (v' w)) u && (nub. sort) r == (nub. sort) r'

instance Eq IntKripkeModel where 
   (IntKrM u v r) == (IntKrM u' v' r') = 
      (nub. sort) u == (nub. sort) u' && all (\w -> (nub. sort) (v w) ==  (nub. sort) (v' w)) u && (nub. sort) r == (nub. sort) r'
\end{code}
\emph{NB:} the following is possible: Two KripkeModels are equal, we convert both to IntKripkeModels,
and the resulting IntKripkeModels are not equal. 

Why is this possible? Because when checking for equality of KripkeModels, we ignore the order of worlds in the
list that defines the universe; but for the conversion to IntKripkeModels, the order matters!

Similarly, we may get translateModToKr model1 == kripkeM1, but when we print 
the lhs and rhs of the equation, we get different results. This is perfectly fine, and not unexpected, 
since printing of KripkeModels works via converting them to IntKripkeModels, and then printing them.

\subsection{Translation functions: KL to Kripke}
\subsubsection{Desiderata}
First, what are the types of our translation functions? As mentioned at the beginning,
we need to bear several things in mind when deciding this question:
\begin{enumerate}
    \item The language of KL is predicate logic, plus a knowledge operator.
    The language of SEL, on the other hand, is propositional logic, plus
    a knowledge operator. So we can only translate from a fragment of 
    the language of KL to SEL.
    \item Kripke models are much more general than KL models. So we can only
    translate from a fragment of the set of Kripke models into KL models.
    \item In Kripke models, there is such a thing as evaluating a formula 
    at a specific world, whereas this has no equivalent in KL models. In fact, 
    evaluating a formula in a KL model is much more closely related to 
    evaluating a formula at a world in a Kripke model, than to evaluating it
    with respect to a whole Kripke model.
\end{enumerate}

In our implementation, to do justice to the the fact that translation functions
can only sensibly be defined for \emph{some} Kripke models, and \emph{some} 
KL formulas, we use the Maybe monad provided by Haskell.

To do justice to the fact that evaluating in a KL model is more like evaluating a 
formula at a specific world in a Kripke Model, than like evaluating a formula with
respect to a whole Kripke model, we translate from pairs of Kripke models and worlds 
to KL models, rather than just from Kripke models to KL models. 

Thus, these are the types of our translation functions:
\begin{enumerate}
\item \begin{verbatim}
translateFormToKr :: Formula -> Maybe ModForm
\end{verbatim}

\item \begin{verbatim}
translateFormToKr :: Formula -> Maybe ModForm
\end{verbatim}

\item \begin{verbatim}
translateModToKr :: Model -> KripkeModel
\end{verbatim}

\item \begin{verbatim}
kripkeToKL :: KripkeModel -> WorldState -> Maybe Model
\end{verbatim}
\end{enumerate}

What constraints do we want our translation functions to satisfy? We propose that reasonable
translation functions should at least satisfy these constraints: for any KL model 
\begin{verbatim} Model w e d \end{verbatim}, any translatable KL formula \begin{verbatim} f \end{verbatim},
any translatable Kripke model \begin{verbatim} KrM uni val rel \end{verbatim}, and any SEL formula
\begin{verbatim} g \end{verbatim},
\begin{enumerate}
%truth values should be preserved
\item \begin{verbatim} Model w e d |= f \end{verbatim} iff
\begin{verbatim} (translateModToKr (Model w e d)) w |= fromJust (translateFormToKr f )\end{verbatim}

\item \begin{verbatim} (KrM uni val rel) w |= g \end{verbatim} iff 
\begin{verbatim} fromJust (kripkeToKL (KrM uni val rel) w) |= translateFormToKL g\end{verbatim}

%Translating formulas back and forth shouldn't change anything:
\item \begin{verbatim} fromJust (translateFormToKL (translateFormToKr f )) = f\end{verbatim}
\item \begin{verbatim} translateFormToKr (fromJust (translateFormToKL g )) = g\end{verbatim}

%Translating models back and forth shouldn't change anything:
\item \begin{verbatim} fromJust (kripkeToKL (translateModToKr (Model w e d)) w) = Model w e d\end{verbatim}
\item \begin{verbatim} translateModToKr ( fromJust (kripkeToKL (KrM uni val rel) w)) = KrM uni val rel \end{verbatim}
\end{enumerate}

\subsubsection{Implementation}

Now we get to the implementation of our translation functions.

\subsection{Translation functions from $\mathcal{KL}$ to Kripke}


\underline{Translation functions for formulas:} \begin{verbatim} translateFormToKr \end{verbatim} replaces all of the atomic
subformulas consisting of the predicate letter "P", followed by a standard name
by propositional variables; it returns Nothing if the input formula doesn't satisfy
this constraint.
\begin{code}
translateFormToKr :: Formula -> Maybe ModForm
translateFormToKr (Atom (Pred "P" [StdNameTerm (StdName nx)])) = Just $ P (read (drop 1 nx))    
translateFormToKr (Not f)                        =  Neg <$> translateFormToKr f           
translateFormToKr (Or f g)                       = fmap disj (translateFormToKr f) <*> translateFormToKr g 
translateFormToKr (K f)                          = Box <$> translateFormToKr f
translateFormToKr _                              = Nothing
\end{code}

\underline{Translation functions for models:} \begin{verbatim} translateModToKr \end{verbatim} takes an epistemic model, and creates a Kripke model, where 
\begin{itemize}
\item the worlds are all the world states in the epistemic state, plus the actual world state;
\item for each world, the propositional variables true at it are the translations of the atomic formulas
consisting of "P" followed by a standard name that are true at the world state;
\item the from within the epistemic state all see each other, and the actual world sees all other worlds.
\end{itemize}
\begin{code}
translateModToKr :: Model -> KripkeModel
translateModToKr (Model w e _) = KrM (nub (w:Set.toList e)) val (nub rel) where
   val = trueAtomicPropsAt
   rel = [(v, v') | v <- Set.toList e, v' <- Set.toList e] ++ [(w,v) | v <- Set.toList e]

--the next two are helper functions:

--identifies true atomic formulas at a world that consist of the predicate "P" followed by a standard name
trueAtomicPropsAt :: WorldState -> [Proposition]
trueAtomicPropsAt w = 
   map (\(Pred "P" [StdNameTerm (StdName nx)]) -> read (drop 1 nx)) trueActualAtoms where
      trueActualAtoms = filter isActuallyAtomic $ map fst (filter snd (Map.toList (atomValues w)))

--checks whether an atomic formula consists of the predicate "P" followed by a standard name
isActuallyAtomic :: Atom -> Bool
isActuallyAtomic (Pred "P" [StdNameTerm (StdName _)]) = True
isActuallyAtomic _ = False
\end{code}

\subsection{Translation functions from Kripke to $\mathcal{KL}$}

\underline{Translation functions for formulas:} \begin{verbatim} translateFormToKL \end{verbatim} takes a formula of SEL
and computes the translated $\mathcal{KL}$ formula. Since SEL is a propositional logic, we will immitate this in the language of $\mathcal{KL}$
by translating it to a unique corresponding atomic formula in $\mathcal{KL}$.

\begin{code}

-- Translates an SEL formula (propositional modal logic) to a KL formula (predicate logic with knowledge operator).
translateFormToKL :: ModForm -> Formula
translateFormToKL (P n) = Atom (Pred "P" [StdNameTerm (StdName ("n" ++ show n))])  -- Maps proposition P n to atom P(n), e.g., P 1 -> P(n1)
translateFormToKL (Neg form) = Not (translateFormToKL form)                          -- Negation is preserved recursively
translateFormToKL (Con form1 form2) = Not (Or (Not (translateFormToKL form1)) (Not (translateFormToKL form2)))  -- Conjunction as ¬(¬f1 ∨ ¬f2)
translateFormToKL (Box form) = K (translateFormToKL form)                            -- Box (□) becomes K, representing knowledge
translateFormToKL (Dia form) = Not (K (Not (translateFormToKL form)))                -- Diamond (◇) as ¬K¬, representing possibility

\end{code}

\underline{Translation functions for models:} \begin{verbatim} kripkeToKL \end{verbatim} takes a Kripke model and a world in its universe
and computes a corresponding $\mathcal{KL}$ model which is satisfiability equivalent with the given world in the given model.

KL models (Knowledge Logic models) and Kripke models are frameworks used to represent an agent's knowledge in epistemic logic, but they differ in their structure and approach. A KL model explicitly separates:
- An \textbf{actual world state}, representing what is true in the real world.
- A set of \textbf{epistemic world states}, representing the worlds the agent considers possible based on their knowledge.

In contrast, a Kripke model consists of:
- A set of possible worlds.
- An accessibility relation between worlds, where an agent knows a proposition \( p \) at a world \( w \) if \( p \) is true in all worlds accessible from \( w \).

The task of translating a Kripke model into a KL model involves preserving both:
1. \textbf{What is true} in the actual world.
2. \textbf{What the agent knows} in that world.

To perform this translation, we take a Kripke model and a specified world \( w \) (designated as the actual world) and construct a KL model where:
- The \textbf{actual world state} corresponds to \( w \).
- The \textbf{epistemic state} consists of all worlds accessible from \( w \) in the Kripke model.

However, not all Kripke models can be straightforwardly translated into KL models while maintaining the semantics of knowledge as defined in KL. In KL, knowledge of a proposition \( p \) means that \( p \) is true in all world states within the epistemic state. This imposes specific requirements on the structure of the Kripke model’s accessibility relation to ensure compatibility with KL’s properties of knowledge.

\subsubsection*{Restrictions on Kripke Models: Transitivity and Euclideanness}

In KL, knowledge exhibits introspective properties, such as:
- \textbf{Positive introspection}: If an agent knows \( p \), then they know that they know \( p \) (formally, \( Kp \rightarrow KKp \)).
- \textbf{Negative introspection}: If an agent does not know \( p \), then they know that they do not know \( p \) (formally, \( \neg Kp \rightarrow K\neg Kp \)).

These properties imply that the epistemic state must be consistent and stable across all worlds the agent considers possible. Specifically, for any proposition \( p \), the formula \( KKp \) (the agent knows that they know \( p \)) should hold if and only if \( Kp \) (the agent knows \( p \)) holds. This equivalence requires the set of worlds in the epistemic state to have a uniform structure.

To capture these introspective properties in a Kripke model, the accessibility relation must satisfy:
- \textbf{Transitivity}: If world \( w \) can access world \( v \) (i.e., \( w \rightarrow v \)), and \( v \) can access world \( u \) (i.e., \( v \rightarrow u \)), then \( w \) must access \( u \) (i.e., \( w \rightarrow u \)). This ensures that the agent’s knowledge extends consistently across all accessible worlds, supporting positive introspection.
- \textbf{Euclideanness}: If \( w \rightarrow v \) and \( w \rightarrow u \), then \( v \rightarrow u \). This means that any two worlds accessible from \( w \) must be accessible to each other, which is necessary for negative introspection.

When a Kripke model’s accessibility relation is both transitive and Euclidean, the set of worlds accessible from \( w \) forms an \textbf{equivalence class}. In an equivalence class:
- Every world is accessible from every other world (including itself, implying reflexivity).
- The set is fully connected, meaning the agent’s knowledge is uniform across all worlds in the epistemic state.

This fully connected structure aligns with the KL model’s epistemic state, where a proposition is known only if it holds in all possible worlds the agent considers. If the worlds accessible from \( w \) did not "see each other" (i.e., were not mutually accessible), introspective knowledge claims like \( KKp \leftrightarrow Kp \) could not be preserved, as the agent’s knowledge would vary inconsistently across the accessible worlds.

\subsubsection*{The Actual World and the Possibility of Knowing Falsehoods}

A key feature of KL models is that the agent can know something false. This means that the actual world state (representing the true state of affairs) does not necessarily belong to the epistemic state (the worlds the agent considers possible). For example, an agent might believe a false proposition, leading them to exclude the actual world from their epistemic state. In the translation from a Kripke model to a KL model:
- We designate \( w \) as the actual world state.
- The epistemic state includes only the worlds accessible from \( w \), which may or may not include \( w \) itself.

This flexibility distinguishes KL models from some traditional Kripke-based systems (e.g., S5, where the actual world is typically accessible due to reflexivity), allowing KL to model scenarios where an agent’s knowledge deviates from reality.

\subsubsection*{Conditions for Translation}

To successfully translate a Kripke model into a KL model:
- The accessibility relation must be \textbf{transitive and Euclidean}, ensuring that the worlds accessible from \( w \) form an equivalence class.
- The translation process then:
  - Sets the actual world state of the KL model to \( w \).
  - Defines the epistemic state as the set of all worlds accessible from \( w \) in the Kripke model.

If the Kripke model’s accessibility relation is not transitive and Euclidean, the translation cannot preserve the introspective properties of knowledge required by KL, and thus it fails. In practice, this restriction is implemented in the function below, which:
- Takes a Kripke model and a world \( w \) as input.
- Verifies that the accessibility relation satisfies transitivity and Euclideanness.
- Returns a KL model if the conditions are met, or an indication of failure (e.g., `Nothing`) otherwise.

\subsubsection*{Example and Intuition}

Consider a Kripke model with worlds \( \{w, v, u\} \), where:
- \( w \rightarrow v \) and \( w \rightarrow u \), but \( v \not\rightarrow u \) (not Euclidean).
- At \( w \), the agent knows \( p \) if \( p \) is true in \( v \) and \( u \).

If \( p \) is true in \( v \) and \( u \), then \( Kp \) holds at \( w \). However, for \( KKp \) to hold, \( Kp \) must be true in both \( v \) and \( u \). If \( v \not\rightarrow u \), then \( Kp \) might not hold at \( v \) (since \( v \) does not access \( u \)), breaking the equivalence \( KKp \leftrightarrow Kp \). In a KL model, the epistemic state must ensure mutual accessibility to avoid such inconsistencies, which is why transitivity and Euclideanness are required.


\begin{code}

-- Main function: Convert Kripke model to KL model
kripkeToKL :: KripkeModel -> WorldState -> Maybe Model
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
    propsIn (Con g h)   = propsIn g ++ propsIn h
    propsIn (Box g)     = propsIn g
    propsIn (Dia g)     = propsIn g

-- Generate all possible valuations explicitly
allValuations :: [World] -> [Proposition] -> [Valuation]
allValuations univ props = 
  let subsetsP = subsequences props
--      assignToWorlds = sequence (replicate (length univ) subsetsP)
  in [ \w -> let idx = length (takeWhile (/= w) univ)
             in if idx < length univ then assignToWorlds !! idx else []
     | assignToWorlds <- replicate (length univ) subsetsP  ----DRAMA?????
 ]

-- Checks whether a Kripke formula is valid on a given Kripke model 
isValidKr :: ModForm -> KripkeModel -> Bool
isValidKr f (KrM univ _ rel) = 
  let props = uniqueProps f
      valuations = allValuations univ props
  in all (\v -> all (\w -> makesTrue (KrM univ v rel, w) f) univ) valuations

-- Checks if a Kripke model is Euclidean
isEuclidean :: KripkeModel -> Bool
isEuclidean = isValidKr (disj (Box (Neg (P 1))) (Box (Dia (P 1))))
  -- □¬P1 ∨ □◇P1 holds for Euclidean relations

-- Checks if a Kripke model is transitive
isTransitive :: KripkeModel -> Bool
isTransitive = isValidKr (disj (Neg (Box (P 1))) (Box (Box (P 1))))  -- ¬□P1 ∨ □□P1 holds for transitive relations
\end{code}


\subsection{Tests}

Here are some tests which, for now, you can run simply by typing the name of the test into ghci. 
They should all return True. They are not yet complete, and after beta, we will integrate testing 
of the translation functions with testing of the rest of the modules.

\begin{code}
-- tests for translateFormToKr
formula1, formula2, formula3 :: Formula
formula1 = Atom (Pred "P" [StdNameTerm n1]) 
formula2 = K (Atom (Pred "P" [StdNameTerm n1]))
formula3 = Not (K (Atom (Pred "P" [StdNameTerm n1])))
-- for these, the translation function should return, respectively:
trFormula1, trFormula2, trFormula3 :: ModForm
trFormula1 = P 1
trFormula2 = Box (P 1)
trFormula3 = Neg (Box (P 1))

ftest1, ftest2, ftest3 :: Bool
ftest1 = fromJust (translateFormToKr formula1) == trFormula1
ftest2 = fromJust (translateFormToKr formula2) == trFormula2
ftest3 = fromJust (translateFormToKr formula3) == trFormula3

--for the next ones, translateFormToKr should return Nothing
form4, form5 :: Formula
form4 = Atom (Pred "Teach" [StdNameTerm n1, StdNameTerm n2]) 
form5 = Not (K (Atom (Pred "Q" [StdNameTerm n1])))

ftest4, ftest5 :: Bool
ftest4 = isNothing $ translateFormToKr form4 
ftest5 = isNothing $ translateFormToKr form5

-- tests for translateModToKr
-- standard name abbreviations:
n1, n2, n3, n4 :: StdName
n1 = StdName "n1" -- ted
n2 = StdName "n2" -- sue
n3 = StdName "n3" -- tina
n4 = StdName "n4" -- tara

-- a model where the actual world is part of the epistemic state
w1, w2, w3, w4 :: WorldState
w1 = mkWorldState [ (PPred "P" [n1], True) ] []
w2 = mkWorldState [ (PPred "P" [n2], True)
                  , (PPred "P" [n3], True) ] []
w3 = mkWorldState [ (PPred "P" [n4], True) ] []
w4 = mkWorldState [] []

e1 :: EpistemicState
e1 = Set.fromList [w1, w2, w3, w4]

domain1 :: Set StdName
domain1 = Set.fromList [n1, n2, n3, n4]

model1 :: Model
model1 = Model w1 e1 domain1

-- if all goes well, this should be converted to the following KripkeModel
kripkeM1 :: KripkeModel
kripkeM1 = KrM uni val rel where
   uni = [w1, w2, w3, w4]
   val world | world == w1 = [1]
             | world == w2 = [2, 3]
             | world == w3 = [4]
             | otherwise   = []
   rel = [(v, v') | v <- uni, v' <- uni]

test1 :: Bool
test1 = translateModToKr model1 == kripkeM1 

-- a model where the actual world is NOT part of the epistemic state
e2 :: EpistemicState
e2 = Set.fromList [w2, w3, w4]

model2 :: Model
model2 = Model w1 e2 domain1

-- if all goes well, this should be converted to the following KripkeModel
kripkeM2 :: KripkeModel
kripkeM2 = KrM uni val rel where
   uni = [w1, w2, w3, w4]
   val world | world == w1 = [1]
             | world == w2 = [2, 3]
             | world == w3 = [4]
             | otherwise   = []
   rel = [(v, v') | v <- es, v' <- es] ++ [(w1, v) | v <- es] where
      es = [w2, w3, w4]

test2 :: Bool
test2 = translateModToKr model2 == kripkeM2

-- a model that contains non-atomic formulas
w2' :: WorldState
w2' = mkWorldState [ (PPred "P" [n2], True)
                  , (PPred "P" [n3], True) 
                  , (PPred "R" [n4, n1], True)] []

e1' :: EpistemicState
e1' = Set.fromList [w1, w2', w3, w4]

-- model1' is like model1, except for extra formulas true in w2' that aren't
-- true in w2
model1' :: Model
model1' = Model w1 e1' domain1

-- if all goes well, this should be converted to a model that "looks the same as"
-- the one model1 gets converted to
test3 :: Bool
test3 = translateKrToKrInt (translateModToKr model1) == translateKrToKrInt (translateModToKr model1')

-- Add tests for seeing whether the translations interact with their
-- “inverses” in the right way
\end{code}

\subsection{Tests for Translation from Kripke to KL}

\subsection{Tests for formulae}

\begin{code}
-- | Check if two SEL formulae are logically equivalent across a set of Kripke models
areEquivalent :: [KripkeModel] -> ModForm -> ModForm -> Bool
areEquivalent models f1 f2 = 
  all (\m -> all (\w -> makesTrue (m, w) f1 == makesTrue (m, w) f2) (universe m)) models

-- | A small set of predefined Kripke models for testing equivalence
smallModels :: [KripkeModel]
smallModels = [exampleModel1, exampleModel2, exampleModel3, exampleModel4, 
               exampleModel5, exampleModel6, exampleModel7]

-- Test translation of atomic proposition
testAtomic :: Bool
testAtomic = let klForm = translateFormToKL (P 1)
                 expected = Atom (Pred "P" [StdNameTerm (StdName "n1")])
             in klForm == expected

-- Test translation of negation
testNegation :: Bool
testNegation = let g = Neg (P 1)
                   klForm = translateFormToKL g
                   expected = Not (Atom (Pred "P" [StdNameTerm (StdName "n1")]))
               in klForm == expected

-- Test translation of conjunction
testConjunction :: Bool
testConjunction = let g = Con (P 1) (P 2)
                      klForm = translateFormToKL g
                      expected = Not (Or (Not (Atom (Pred "P" [StdNameTerm (StdName "n1")]))) 
                                        (Not (Atom (Pred "P" [StdNameTerm (StdName "n2")]))))
                  in klForm == expected

-- Test translation of box operator
testBox :: Bool
testBox = let g = Box (P 1)
              klForm = translateFormToKL g
              expected = K (Atom (Pred "P" [StdNameTerm (StdName "n1")]))
          in klForm == expected

-- Test translation of diamond operator
testDiamond :: Bool
testDiamond = let g = Dia (P 1)
                  klForm = translateFormToKL g
                  expected = Not (K (Not (Atom (Pred "P" [StdNameTerm (StdName "n1")]))))
              in klForm == expected

-- Test invertibility of a simple formula using logical equivalence
testFormInvertSimple :: Bool
testFormInvertSimple = 
  let g = Box (P 1)                      -- Original formula: □P1
      klForm = translateFormToKL g       -- Translate to KL
      selForm = fromJust (translateFormToKr klForm)  -- Back-translate to SEL
  in areEquivalent smallModels g selForm  -- Check equivalence

-- Test invertibility of a complex formula using logical equivalence
testFormInvertComplex :: Bool
testFormInvertComplex = 
  let g = Box (Con (P 1) (Neg (P 2)))   -- Original formula: □(P1 ∧ ¬P2)
      klForm = translateFormToKL g       -- Translate to KL
      selForm = fromJust (translateFormToKr klForm)  -- Back-translate to SEL
  in areEquivalent smallModels g selForm  -- Check equivalence

-- Aggregate all formula tests with diagnostic output
testAllFormulae :: String
testAllFormulae = 
  let results = [ ("testAtomic", testAtomic)
                , ("testNegation", testNegation)
                , ("testConjunction", testConjunction)
                , ("testBox", testBox)
                , ("testDiamond", testDiamond)
                , ("testFormInvertSimple", testFormInvertSimple)
                , ("testFormInvertComplex", testFormInvertComplex)
                ]
      failures = [name | (name, result) <- results, not result]
  in if null failures
     then "All formula tests passed"
     else "Failed formula tests: " ++ unwords failures
\end{code}

\subsection{Tests for Models}

\begin{code}
-- | Simplified check if two Kripke models are bisimilar.
areBisimilar :: KripkeModel -> KripkeModel -> Bool
areBisimilar km1 km2 = 
  let univ1 = universe km1
      univ2 = universe km2
      rel1 = relation km1
      rel2 = relation km2
      val1 = valuation km1
      val2 = valuation km2
      initialRel = [(w1, w2) | w1a <- univ1, w2a <- univ2, val1 w1a == val2 w2a]
      satisfiesBackForth r (w1b, w2b) =
        all (\v1 -> any (\v2 -> (v1, v2) `elem` r) (successors w2b rel2)) 
             (successors w1b rel1) &&
        all (\v2 -> any (\v1 -> (v1, v2) `elem` r) (successors w1b rel1)) 
             (successors w2b rel2)
      largestBisimulation = until (\r -> r == filter (satisfiesBackForth r) r)
                                  (\r -> filter (satisfiesBackForth r) r)
                                  initialRel
  in not (null largestBisimulation) && 
     all (\w1c -> any (\(w1', _) -> w1c == w1') largestBisimulation) univ1 && 
     all (\w2c -> any (\(_, w2'd) -> w2c == w2'd) largestBisimulation) univ2
  
-- | Get successor worlds in a relation
successors :: WorldState -> [(WorldState, WorldState)] -> [WorldState]
successors w rel = [v | (u, v) <- rel, u == w]

-- Helper function to test truth preservation
testTruthPres :: KripkeModel -> WorldState -> ModForm -> Bool
testTruthPres km w g = 
  case kripkeToKL km w of
    Nothing -> False  -- Translation failed, so truth not preserved
    Just klModel -> let klFormula = translateFormToKL g
                    in makesTrue (km, w) g == satisfiesModel klModel klFormula

-- Test translation succeeds for S5 model
testTranslationSucceedsModel3 :: Bool
testTranslationSucceedsModel3 = isJust (kripkeToKL exampleModel3 (makeWorldState 30))

-- Test translation succeeds for clustered model
testTranslationSucceedsModel6 :: Bool
testTranslationSucceedsModel6 = isJust (kripkeToKL exampleModel6 (makeWorldState 60))

-- Test translation fails for linear non-transitive model
testTranslationFailsModel2 :: Bool
testTranslationFailsModel2 = isNothing (kripkeToKL exampleModel2 (makeWorldState 20))

-- Test translation fails for cyclic non-transitive model
testTranslationFailsModel5 :: Bool
testTranslationFailsModel5 = isNothing (kripkeToKL exampleModel5 (makeWorldState 50))

-- Test truth preservation for atomic proposition in S5 model
testTruthPresP1Model3 :: Bool
testTruthPresP1Model3 = testTruthPres exampleModel3 (makeWorldState 30) (P 1)

-- Test truth preservation for box operator in S5 model
testTruthPresBoxP1Model3 :: Bool
testTruthPresBoxP1Model3 = testTruthPres exampleModel3 (makeWorldState 30) (Box (P 1))

-- Test truth preservation for diamond operator in S5 model
testTruthPresDiaP1Model3 :: Bool
testTruthPresDiaP1Model3 = testTruthPres exampleModel3 (makeWorldState 30) (Dia (P 1))

-- Test truth preservation for conjunction in clustered model
testTruthPresConModel6 :: Bool
testTruthPresConModel6 = testTruthPres exampleModel6 (makeWorldState 60) (Con (P 1) (P 2))

-- Test model invertibility for S5 model using bisimulation
testModelInvertModel3 :: Bool
testModelInvertModel3 = 
  let km = exampleModel3                -- Original S5 Kripke model
      w = makeWorldState 30             -- A starting world state
      klm = fromJust (kripkeToKL km w)  -- Translate to KL
      kmBack = translateModToKr klm     -- Back-translate to Kripke model
  in areBisimilar kmBack km             -- Check bisimulation

-- Test contradiction is false in modelKL7
testContradictionFalseModel7 :: Bool
testContradictionFalseModel7 = not (checkModel modelKL7 (translateFormToKL (Con (P 2) (Neg (P 2)))))


-- Test reflexivity axiom false in modelKL7 (w70 not reflexive)
testRefFalseModel7 :: Bool
testRefFalseModel7 = checkModel modelKL7 ref


-- Test reflexivity axiom true in modelKL7b (w71 in cluster)
testRefTrueModel7b :: Bool
testRefTrueModel7b = checkModel modelKL7b ref

-- Aggregate all model tests with diagnostic output
testAllModels :: String
testAllModels = 
  let results = [ ("testTranslationSucceedsModel3", testTranslationSucceedsModel3)
                , ("testTranslationSucceedsModel6", testTranslationSucceedsModel6)
                , ("testTranslationFailsModel2", testTranslationFailsModel2)
                , ("testTranslationFailsModel5", testTranslationFailsModel5)
                , ("testTruthPresP1Model3", testTruthPresP1Model3)
                , ("testTruthPresBoxP1Model3", testTruthPresBoxP1Model3)
                , ("testTruthPresDiaP1Model3", testTruthPresDiaP1Model3)
                , ("testTruthPresConModel6", testTruthPresConModel6)
                , ("testModelInvertModel3", testModelInvertModel3)
                , ("testContradictionFalseModel7", testContradictionFalseModel7)
                , ("testRefFalseModel7", testRefFalseModel7)
                , ("testRefTrueModel7b", testRefTrueModel7b)
                ]
      failures = [name | (name, result) <- results, not result]
  in if null failures
     then "All model tests passed"
     else "Failed model tests: " ++ unwords failures
\end{code}

\subsection{example models used to test the translations from Kripke to KL}

\begin{code}
--IntegerKripkeModel to KripkeModel

--Example 1 : Reflexive, isolated worlds
intW0, intW1, intW2 :: IntWorld
intW0 = 0
intW1 = 1
intW2 = 2

intUniverse1 :: IntUniverse
intUniverse1 = [intW0, intW1, intW2]

intValuation1 :: IntValuation
intValuation1 w
  | w == 0 || w == 1 = [1]  -- Proposition 1 holds in worlds 0 and 1
  | w == 2           = []   -- No propositions hold in world 2
  | otherwise        = []

intRelation1 :: IntRelation
intRelation1 = [(0, 0), (0, 1), (1, 0), (1, 1), (2, 2)]

intModel1 :: IntKripkeModel
intModel1 = IntKrM intUniverse1 intValuation1 intRelation1

-- Convert to WorldState-based model
exampleModel1 :: KripkeModel
exampleModel1 = convertToWorldStateModel intModel1

--Example2 : Linear
-- Integer-based model
intW20, intW21, intW22 :: IntWorld
intW20 = 20
intW21 = 21
intW22 = 22

intUniverse2 :: IntUniverse
intUniverse2 = [intW20, intW21, intW22]

intValuation2 :: IntValuation
intValuation2 w
  | w == 20 = [1]  -- Proposition 1 holds in world 20
  | w == 21 = []   -- No propositions in world 21
  | w == 22 = [1]  -- Proposition 1 holds in world 22
  | otherwise = []

intRelation2 :: IntRelation
intRelation2 = [(20, 21), (21, 22)]  -- Linear: 20 -> 21 -> 22

intModel2 :: IntKripkeModel
intModel2 = IntKrM intUniverse2 intValuation2 intRelation2

exampleModel2 :: KripkeModel
exampleModel2 = convertToWorldStateModel intModel2

--Example3 : S5
-- Integer-based model
intW30, intW31, intW32 :: IntWorld
intW30 = 30
intW31 = 31
intW32 = 32

intUniverse3 :: IntUniverse
intUniverse3 = [intW30, intW31, intW32]

intValuation3 :: IntValuation
intValuation3 w
  | w == 30 = [1]  -- Proposition 1 holds in world 30
  | otherwise = [] -- No propositions elsewhere

intRelation3 :: IntRelation
intRelation3 = [(w1e, w2e) | w1e <- intUniverse3, w2e <- intUniverse3]  -- Fully connected

intModel3 :: IntKripkeModel
intModel3 = IntKrM intUniverse3 intValuation3 intRelation3

exampleModel3 :: KripkeModel
exampleModel3 = convertToWorldStateModel intModel3

--Example 4 : Empty relation
-- Integer-based model
intW40, intW41, intW42 :: IntWorld
intW40 = 40
intW41 = 41
intW42 = 42

intUniverse4 :: IntUniverse
intUniverse4 = [intW40, intW41, intW42]

intValuation4 :: IntValuation
intValuation4 w
  | w == 40 = [1]  -- Proposition 1 holds in world 40
  | w == 41 = []   -- No propositions in world 41
  | w == 42 = [2]  -- Proposition 2 holds in world 42
  | otherwise = []

intRelation4 :: IntRelation
intRelation4 = []  -- Empty relation

intModel4 :: IntKripkeModel
intModel4 = IntKrM intUniverse4 intValuation4 intRelation4

exampleModel4 :: KripkeModel
exampleModel4 = convertToWorldStateModel intModel4

--Example5 : Cyclic with multiple propositions
-- Integer-based model
intW50, intW51, intW52 :: IntWorld
intW50 = 50
intW51 = 51
intW52 = 52

intUniverse5 :: IntUniverse
intUniverse5 = [intW50, intW51, intW52]

intValuation5 :: IntValuation
intValuation5 w
  | w == 50 = [1, 2]  -- Propositions 1 and 2 hold in world 50
  | w == 51 = [1]     -- Proposition 1 holds in world 51
  | w == 52 = []      -- No propositions in world 52
  | otherwise = []

intRelation5 :: IntRelation
intRelation5 = [(50, 51), (51, 52), (52, 50)]  -- Cycle: 50 -> 51 -> 52 -> 50

intModel5 :: IntKripkeModel
intModel5 = IntKrM intUniverse5 intValuation5 intRelation5

exampleModel5 :: KripkeModel
exampleModel5 = convertToWorldStateModel intModel5

--Example 6 : Euclidean, Transitive, and Reflexive Frame
-- Integer-based model
intW60, intW61, intW62, intW63, intW64 :: IntWorld
intW60 = 60
intW61 = 61
intW62 = 62
intW63 = 63
intW64 = 64

intUniverse6 :: IntUniverse
intUniverse6 = [intW60, intW61, intW62, intW63, intW64]

intValuation6 :: IntValuation
intValuation6 w
  | w == 60 = [1]        -- Proposition 1 holds in world 60
  | w == 61 = [1, 2]     -- Propositions 1 and 2 hold in world 61
  | w == 62 = []         -- No propositions in world 62
  | w == 63 = [2]        -- Proposition 2 holds in world 63
  | w == 64 = [1, 2]     -- Propositions 1 and 2 hold in world 64
  | otherwise = []

intRelation6 :: IntRelation
intRelation6 = let cluster1 = [60, 61, 62]  -- First cluster: fully connected
                   cluster2 = [63, 64]      -- Second cluster: fully connected
               in [(w1f, w2f) | w1f <- cluster1, w2f <- cluster1] ++
                  [(w1f, w2f) | w1f <- cluster2, w2f <- cluster2]

intModel6 :: IntKripkeModel
intModel6 = IntKrM intUniverse6 intValuation6 intRelation6

exampleModel6 :: KripkeModel
exampleModel6 = convertToWorldStateModel intModel6


--Example 7: Euclidean, Transitive, but not Reflexive Frame
-- Integer-based model
intW70, intW71, intW72, intW73, intW74, intW75 :: IntWorld
intW70 = 70
intW71 = 71
intW72 = 72
intW73 = 73
intW74 = 74
intW75 = 75

intUniverse7 :: IntUniverse
intUniverse7 = [intW70, intW71, intW72, intW73, intW74, intW75]

intValuation7 :: IntValuation
intValuation7 w
  | w == 70 = [1]
  | w == 71 = [1, 2]
  | w == 72 = [2]
  | w == 73 = []
  | w == 74 = [1]
  | w == 75 = [1, 2]
  | otherwise = []

intRelation7 :: IntRelation
intRelation7 = let cluster = [71, 72, 73, 74, 75]
               in [(70, w) | w <- cluster] ++ [(w1g, w2g) | w1g <- cluster, w2g <- cluster]

intModel7 :: IntKripkeModel
intModel7 = IntKrM intUniverse7 intValuation7 intRelation7

exampleModel7 :: KripkeModel
exampleModel7 = convertToWorldStateModel intModel7

-- Define modelKL7 and modelKL7b from exampleModel7
modelKL7 :: Model
modelKL7 = fromJust (kripkeToKL exampleModel7 (makeWorldState 70))

modelKL7b :: Model
modelKL7b = fromJust (kripkeToKL exampleModel7 (makeWorldState 71))

-- Define ref as the reflexivity axiom K P(n1) -> P(n1)
ref :: Formula
ref = translateFormToKL (impl (Box (P 99)) (P 99))

\end{code}