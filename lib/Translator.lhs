\sec{Comparing KL and Epistemic Logic}
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
\end{code}

To enable easier specification of models, and easier printing, we also define a Kripke Model
where worlds are of type Int:
type IntWorld = Integer
type IntUniverse = [IntWorld]
type IntValuation = IntWorld -> [Proposition]
type IntRelation = [(IntWorld, IntWorld)]
data IntKripkeModel = IntKrM IntUniverse IntValuation IntRelation
\end{code}
We define a function to convert from KripkeModels to IntKripkeModels:
\begin{code}
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
      
\end{code}

To be able to print Models, let's define a Show instance for IntKripkeModels, and for KripkeModels:
\begin{code}
-- I realise that following the convention that show should return what you need to type in to get define the object,
-- we shouldn't really call this a Show instance, but instead something like a print function
instance Show IntKripkeModel where
   show (IntKrM uni val rel) = "IntKrM\n" ++ show uni ++ "\n" ++ show [(x, val x) | x <- uni ] ++ "\n" ++ show rel
-- we define a Show Instance for KripkeModels, which just shows the KripkeModel, converted to an
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
   val = trueAtomicPropsAt
   rel = [(v, v') | v <- Set.toList e, v' <- Set.toList e] ++ [(w,v) | v <- Set.toList e]

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

\begin{code}

\end{code}
