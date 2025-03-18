\section{Comparing KL and Epistemic Logic}
\begin{code}
module Translator where

import Data.List

import Data.Maybe
import GHC.Num

-- importing syntax and semantics of KL
import SyntaxKL
import SemanticsKL
--import Data.Map (Map)
--import qualified Data.Map as Map
--import Data.Set (Set)
--import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Integer (bitInteger)


--import HW1 (Form)

-- we need a few definitions that were in Lou's original ModelKL, but are not in 
-- SyntaxKL or SemanticsKL:

-- Helper to create a world state from atom and term assignments
mkWorldState :: [(Atom, Bool)] -> [(Term, StdName)] -> WorldState
mkWorldState atoms terms =
      WorldState (Map.fromList atoms) (Map.fromList terms)

-- Infinite set of standard names (simulated as a generator).
standardNames :: [StdName]
standardNames = map (StdName . ("n" ++) . show) [1..]
\end{code}

\subsection{Preliminaries}
We want to compare KL and Standard Epistemic Logic based on Kripke frames.
(Call this SEL).
For example, we might want to compare the complexity of model checking
for KL and SEL. 
To do this, we need some way of “translating” between formulas of KL and
formulas of SEL, and between KL-models and Kripke frames.
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

\subsubsection{Mathematical Description of the Syntax and Semantics of SEL}
\subsubsubsection{Syntax}
\subsubsubsection{Semantics}
This is just basic modal logic, as we know it.
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
(!) :: Relation -> World -> [World]
(!) r w = map snd $ filter ((==) w . fst) r

--truth at a world
makesTrue :: (KripkeModel,World) -> ModForm -> Bool
makesTrue (KrM _ v _, w) (P k)     = k `elem` v w
makesTrue (m,w)          (Neg f)   = not (makesTrue (m,w) f)
makesTrue (m,w)          (Con f g) = makesTrue (m,w) f && makesTrue (m,w) g
makesTrue (KrM u v r, w) (Dia f)   = any (\w' -> makesTrue (KrM u v r, w') f) (r ! w)
makesTrue (KrM u v r, w) (Box f)   = all (\w' -> makesTrue (KrM u v r,w') f) (r ! w)

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

Sometime it will also be usefuel to convert between KripkeModels and IntKripkeModels. 
To enable this, we provide the following functions:

\begin{code}

--KripkeModel to IntKripkeModel
translateKrToKrInt :: KripkeModel -> IntKripkeModel
translateKrToKrInt (KrM u v r) = IntKrM u' v' r' where
   ur = nub u -- the function first gets rid of duplicate worlds in the model
   u' = take (length ur) [0..] 
   v' n = v (intToWorldState ur n) where
      intToWorldState :: Universe -> Integer -> WorldState
      intToWorldState ur n = ur !! integerToInt n
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
  let uniqueAtom = Pred "WorldID" [StdNameTerm (StdName (show n))]
  in mkWorldState [(uniqueAtom, True)] []

\end{code}

Note to self: Some helper functions for Milan's stuff -> Could it make sense to 
put them into another section, in the place where they are needed?
\begin{code}

-- Helper functions as provided
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
      assignToWorlds = sequence (replicate (length univ) subsetsP)
  in [ \w -> let idx = length (takeWhile (/= w) univ)
             in if idx < length univ then assignToWorlds !! idx else []
     | assignToWorlds <- sequence (replicate (length univ) subsetsP) ]

-- Corrected isValid
isValidKr :: ModForm -> KripkeModel -> Bool
isValidKr f (KrM univ _ rel) = 
  let props = uniqueProps f
      valuations = allValuations univ props
  in all (\v -> all (\w -> makesTrue (KrM univ v rel, w) f) univ) valuations
\end{code}

To be able to print Models, let's define a Show instance for IntKripkeModels, and for KripkeModels:
\begin{code}
-- I realise that following the convention that show should return what you need to type in to get define the object,
-- we shouldn't really call this a Show instance, but instead something like a print function
instance Show IntKripkeModel where
   show (IntKrM uni val rel) = "IntKrM\n" ++ show uni ++ "\n" ++ show [(x, val x) | x <- uni ] ++ "\n" ++ show rel

-- we also define a Show Instance for KripkeModels, which just shows the KripkeModel, converted to an
-- IntKripkeModel
instance Show KripkeModel where
   show m = show $ translateKrToKrInt m
\end{code}

Later, we will want to compare models for equality. So we'll also define an Eq instance. Comparison for
equality will work, at least as long as models are finite.
\begin{code}
-- we check that the valuations agree on all worlds in the model
instance Eq KripkeModel where
   (KrM u v r) == (KrM u' v' r') = 
      (nub. sort) u == (nub. sort) u' && all (\w -> (nub. sort) (v w) ==  (nub. sort) (v' w)) u && (nub. sort) r == (nub. sort) r'

instance Eq IntKripkeModel where 
   (IntKrM u v r) == (IntKrM u' v' r') = 
      (nub. sort) u == (nub. sort) u' && all (\w -> (nub. sort) (v w) ==  (nub. sort) (v' w)) u && (nub. sort) r == (nub. sort) r'
-- NB: the following is possible:
-- Two KripkeModels are equal, we convert both to IntKripkeModels,
-- and the resulting IntKripkeModels are not equal.
-- Why is this possible? 
-- Because when checking for equality of KripkeModels, we ignore the order of worlds in the
-- list that defines the universe;
-- but when we convert to IntKripkeModels, the order matters!
-- So we may get translateModToKr model1 == kripkeM1, but when we print
-- the lhs and rhs of the equation, we get different results.
-- This is perfectly fine, and not unexpected, since printing works
-- via converting to IntKripkeModels.
\end{code}

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
%I always wrote down, first, the type of the mathematical function, and then,
%the Haskell type. But maybe that's unnecessary, and just the Haskell type would suffice?
\begin{enumerate}
\item A partial translation function $ translateFormToKr : \mathcal{L}_{KL} \to \mathcal{L}_{SEL} $.

In Haskell: 
\begin{verbatim}
translateFormToKr :: Formula -> Maybe ModForm
\end{verbatim}

\item A translation function $ translateFormToKL : \mathcal{L}_{SEL} \to \mathcal{L}_{KL} $.

In Haskell: 
\begin{verbatim}
translateFormToKr :: Formula -> Maybe ModForm
\end{verbatim}

\item A translation function $ translateModToKr : \mathcal{E} \to \mathcal{Kr} $, 
where $ \mathcal{E}$ is the set of epistemic models, and $ \mathcal{Kr} $ is the 
set of Kripke models.

In Haskell: 
\begin{verbatim}
translateModToKr :: Model -> KripkeModel
\end{verbatim}

\item A partial translation function $ kripkeToKL : \mathcal {KrP} \to \mathcal{E} $,
where $ \mathcal{KrP} $ is the set of pointed Kripke models.

In Haskell:
\begin{verbatim}
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
%@Milan, do these look like the requirements we want to you?
%We should add some tests to check that our functions actually do satisfy these!


\subsubsection{Mathematical description of the translation functions}
- definitions of the functions in terms of the mathematical description of KL models
(this is provided by Lou), and the mathematical description of Kripke Models (from the
previous section)
- ideally a proof that the functions, so defined, satisfy the desiderata laid out
in the previous section
\subsubsection{Implementation}

Now we finally get to the implementation of our translation functions.

Translation functions for formulas:
\begin{code}
-- from SEL Formula to KL formula
translateFormToKr :: Formula -> Maybe ModForm
translateFormToKr (Atom (Pred "P" [StdNameTerm (StdName nx)])) = Just $ P (read (drop 1 nx))    
translateFormToKr (Not f)                        = fmap Neg $ translateFormToKr f           
translateFormToKr (Or f g)                       = fmap disj (translateFormToKr f) <*> (translateFormToKr g)  
translateFormToKr (K f)                          = fmap Box $ translateFormToKr f
translateFormToKr _                              = Nothing

\end{code}

Translation functions for models:
\begin{code}
-- from KL model to Kripke Model
translateModToKr :: Model -> KripkeModel
translateModToKr (Model w e d) = KrM (nub (w:(Set.toList e))) val (nub rel) where
   val = trueAtomicPropsAt
   rel = [(v, v') | v <- Set.toList e, v' <- Set.toList e] ++ [(w,v) | v <- Set.toList e]

--the next three are helper functions:
atomicPropsKL :: [Atom]
atomicPropsKL = [Pred "P" [StdNameTerm n] | n <- standardNames] 

trueAtomicPropsAt :: WorldState -> [Proposition]
trueAtomicPropsAt w = 
   map (\(Pred "P" [StdNameTerm (StdName nx)]) -> read (drop 1 nx)) trueActualAtoms where
      trueActualAtoms = filter isActuallyAtomic $ map fst (filter (\p -> snd p == True) (Map.toList (atomValues w)))

isActuallyAtomic :: Atom -> Bool
isActuallyAtomic (Pred "P" [StdNameTerm (StdName _)]) = True
isActuallyAtomic _ = False
\end{code}

\subsection{Translation functions Kripke to KL}

\subsection{Formulae}

\begin{code}

translateFormToKL :: ModForm -> Formula
translateFormToKL (P n) = Atom (Pred "P" [StdNameTerm (StdName ("n" ++ show n))])
translateFormToKL (Neg form) = Not (translateFormToKL form)
translateFormToKL (Con form1 form2) = Not (Or (Not (translateFormToKL form1)) (Not (translateFormToKL form2)))
translateFormToKL (Box form) = K (translateFormToKL form)
translateFormToKL (Dia form) = Not (K (Not (translateFormToKL form)))

\end{code}

\subsection{Models}

\begin{code}

-- Helper: Map proposition to atom
propToAtom :: Proposition -> Atom
propToAtom n = Pred "P" [StdNameTerm (StdName ("n" ++ show n))]

-- Helper: Create a WorldState from a list of propositions
createWorldState :: [Proposition] -> WorldState
createWorldState props =
  let atomVals = Map.fromList [(propToAtom p, True) | p <- props]
      termVals = Map.empty  -- No term values for simplicity
  in WorldState atomVals termVals

-- Check if a world is in the universe
isInUniv :: WorldState -> [WorldState] -> Bool
isInUniv w univ = elem w univ

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
--Derive Dis
isEuclidean :: KripkeModel -> Bool
isEuclidean krm
        | isValidKr (disj (Box (Neg (P 1))) (Box (Dia (P 1)))) krm = True
        | otherwise = False


isTransitive :: KripkeModel -> Bool
isTransitive krm 
        | isValidKr (disj (Neg (Box (P 1))) (Box (Box (P 1)))) krm = True
        | otherwise = False


\end{code}


\subsection{Tests}

TODO: Now we write some tests to see whether these actually work.

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
w1 = mkWorldState [ (Pred "P" [StdNameTerm n1], True) ] []
w2 = mkWorldState [ (Pred "P" [StdNameTerm n2], True)
                  , (Pred "P" [StdNameTerm n3], True) ] []
w3 = mkWorldState [ (Pred "P" [StdNameTerm n4], True) ] []
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
w2' = mkWorldState [ (Pred "P" [StdNameTerm n2], True)
                  , (Pred "P" [StdNameTerm n3], True) 
                  , (Pred "R" [StdNameTerm n4, StdNameTerm n1], True)] []

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

-- once Milan's functions have been added:
-- tests for seeing whether the translations interact with their
-- “inverses” in the right way
\end{code}

MILAN'S EXAMPLES AND TESTS:

To be able to test this, I will add some Kripke Models

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
intRelation3 = [(w1, w2) | w1 <- intUniverse3, w2 <- intUniverse3]  -- Fully connected

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
               in [(w1, w2) | w1 <- cluster1, w2 <- cluster1] ++
                  [(w1, w2) | w1 <- cluster2, w2 <- cluster2]

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
               in [(70, w) | w <- cluster] ++ [(w1, w2) | w1 <- cluster, w2 <- cluster]

intModel7 :: IntKripkeModel
intModel7 = IntKrM intUniverse7 intValuation7 intRelation7

exampleModel7 :: KripkeModel
exampleModel7 = convertToWorldStateModel intModel7

\end{code}

\subsection{Tests}

\subsection{Tests for Kripke to KL}

\begin{code}

modelKL3 :: Model
modelKL3 = fromJust(kripkeToKL exampleModel3 (makeWorldState 30))

modelKL4 :: Model
modelKL4 = fromJust(kripkeToKL exampleModel4 (makeWorldState 40))

modelKL5 :: Model
modelKL5 = fromJust(kripkeToKL exampleModel5 (makeWorldState 50))

modelKL6 :: Model
modelKL6 = fromJust(kripkeToKL exampleModel6 (makeWorldState 60))

modelKL7 :: Model
modelKL7 = fromJust(kripkeToKL exampleModel7 (makeWorldState 70))

modelKL7b :: Model
modelKL7b = fromJust(kripkeToKL exampleModel7 (makeWorldState 71))

ref :: Formula
ref = translateFormToKL (impl (Box (P 1)) (P 1))

conTest :: Formula
conTest = translateFormToKL (Con (P 1) (P 2))

boxTest :: Formula
boxTest = translateFormToKL (Box (P 1))

diaTest :: Formula
diaTest = translateFormToKL (Dia (P 1))

negTest :: Formula
negTest = translateFormToKL (Neg (P 1))

test7 :: Bool
test7 = not (checkModel modelKL7 (translateFormToKL (Con (P 2) (Neg (P 2)))))

testref :: Bool
testref = checkModel modelKL7 ref

testrefb :: Bool
testrefb = checkModel modelKL7b ref


\end{code}