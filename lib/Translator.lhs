{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
\sec{Comparing KL and Epistemic Logic}
\begin{code}
module Translator where

import Data.List
--import Data.List (nub, subsequences, sequence)
import Data.Maybe --ADDTHISTOTHE ORIGINAL DOCUMENT

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
-- SyntaxKL or SemanticsKL

-- Helper to create a world state from atom and term assignments
--mkWorldState :: [(Atom, Bool)] -> [(Term, StdName)] -> WorldState
--mkWorldState atoms terms =
--  WorldState (Map.fromList atoms) (Map.fromList terms)

-- Infinite set of standard names (simulated as a generator).
--standardNames :: [StdName]
--standardNames = map (StdName . ("n" ++) . show) [1..]
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
This is just basic modal logic, as we know it.
\subsubsection{Implementation}

To represent Kripke Models, we will use the types from HW 2, with a twist: we let
the worlds be WorldStates, as defined in "Semantics". This simplifies the translation
functions, and doesn't matter mathematically, as the internal constitution
of the worlds in a Kripke Model is mathematically irrelevant.

\subsection{IntKripkeModel}
\begin{code}

type IntWorld = Integer
type IntUniverse = [IntWorld]
type IntValuation = IntWorld -> [Proposition]
type IntRelation = [(IntWorld, IntWorld)]
data IntKripkeModel = IntKrM IntUniverse IntValuation IntRelation

\end{code}

\subsection{KripkeModel}

Syntax:

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
impl f g = disj (Neg f) g
\end{code}

Semantics:
\begin{code}
type World = WorldState
type Universe = [World]
type Proposition = Int

type Valuation = World -> [Proposition]
type Relation = [(World,World)]

data KripkeModel = KrM Universe Valuation Relation

(!) :: Relation -> World -> [World]
(!) r w = map snd $ filter ((==) w . fst) r

makesTrue :: (KripkeModel,World) -> ModForm -> Bool
makesTrue (KrM _ v _, w) (P k)     = k `elem` v w
makesTrue (m,w)          (Neg f)   = not (makesTrue (m,w) f)
makesTrue (m,w)          (Con f g) = makesTrue (m,w) f && makesTrue (m,w) g
makesTrue (KrM u v r, w) (Dia f)   = any (\w' -> makesTrue (KrM u v r, w') f) (r ! w)
makesTrue (KrM u v r, w) (Box f)   = all (\w' -> makesTrue (KrM u v r,w') f) (r ! w)

trueEverywhere :: KripkeModel -> ModForm -> Bool
trueEverywhere (KrM x y z) f = all (\w -> makesTrue (KrM x y z, w) f) x

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

\subsection{IntKripkeModel to KripkeModel}

\begin{code}

makeWorldState :: Integer -> WorldState
makeWorldState n =
  let uniqueAtom = Pred "WorldID" [StdNameTerm (StdName (show n))]
  in mkWorldState [(uniqueAtom, True)] []

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

\end{code}

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


To be able to print Models, let's define a Show instance for KripkeModels:

\begin{code}
instance Show KripkeModel where
   show (KrM uni val rel) = "KrM\n" ++ show (map (pretty uni) uni) ++ "\n" ++ show [(pretty uni x, val x) | x <- uni ] ++ "\n" ++ prettyPrint uni rel where
      pretty :: Universe -> World -> Int
      pretty u w = Map.fromList (zip u (take (length u) [1..])) Map.! w 
      prettyPrint :: Universe -> Relation -> String
      prettyPrint u ((v, v'):pairs) = "(" ++ (show (pretty u v)) ++ ", " ++ (show (pretty u v')) ++ ") " ++ prettyPrint u pairs
      prettyPrint u [] = ""

--Add Eq      
instance Eq KripkeModel where
  (==) (KrM x y z) (KrM u v w) = sort x == sort u && all (\t ->sort (y t) == sort (v t)) x && sort z == sort w

\end{code}

All this is taken from HW 2, with only two slight modifications:
\begin{enumerate}
\item We use WorldStates (defined in the module "Semantics") as worlds in the Kripke Model.
\item We use "Neg" instead of "Not" as a type constructor for negated modal formula, since
"Not" is already being used as a type constructor for KL-formulas (see "Syntax" for details).
\end{enumerate}

\subsection{Translation functions: KL to Kripke}
\subsubsection{Desiderata}
This section should answer the questions:
- What are the types of the translation functions?
- What constraints do we want our translation functions to satisfy?
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
   val v = trueAtomicPropsAt v
   rel = [(v, v') | v <- Set.toList e, v' <- Set.toList e] ++ [(w,v) | v <- Set.toList e]

atomicPropsKL :: [Atom]
atomicPropsKL = [Pred "P" [StdNameTerm n] | n <- standardNames] 

trueAtomicPropsAt :: WorldState -> [Proposition]
trueAtomicPropsAt w = 
   map (\(Pred "P" [StdNameTerm (StdName nx)]) -> read (drop 1 nx)) trueActualAtoms where
      trueActualAtoms = filter (`elem` atomicPropsKL) $ map fst (filter (\p -> snd p == True) (Map.toList (atomValues w)))
      
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
test7 = checkModel modelKL7 (translateFormToKL (Con (P 2) (Neg (P 2))))

testref :: Bool
testref = checkModel modelKL7 ref

testrefb :: Bool
testrefb = checkModel modelKL7b ref


\end{code}


TODO: Now we write some tests to see whether these actually work.

\begin{code}
-- tests for translateFormToKr

-- tests for translateModToKr

-- once Milan's functions have been added:
-- tests for seeing whether the translations interact with their
-- “inverses” in the right way
\end{code}
