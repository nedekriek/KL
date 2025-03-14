\sec{Comparing KL and Epistemic Logic}

\begin{code}

\end{code}

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
    translate some Kripke models into KL models.
    \item In Kripke models, there is such a thing as evaluating a formula 
    at a specific world, whereas this has no equivalent in KL models. We need
    to take this fact into account when thinking about adequacy criteria for
    a translation function.
\end{enumerate}

\subsection{Definitions of KL models and Kripke Models}

We will represent KL models using the definition from Main. To represent
Kripke Models, we will use the definition from HW 2, with a twist: we let
the worlds be WorldStates, as defined in Main. This simplifies the translation
functions, and doesn't matter mathematically, as the internal constitution
of the worlds in a Kripke Model is mathematically irrelevant. 

Here is the code copied from Lou that defines KL models:
\begin{code}
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (subsequences)

--extra import
import Data.List

-- Represent Standard names as strings (e.g., "n1", "n2", ...), infinite in theory
newtype StdName = StdName String deriving (Eq, Ord, Show)

-- Variables (e.g., "x", "y").
newtype Variable = Var String deriving (Eq, Ord, Show)

-- Terms: variables, standard names, or function applications.
data Term = VarTerm Variable
          | StdNameTerm StdName
          | FuncApp String [Term]
          deriving (Eq, Ord, Show)

-- Atomic propositions: predicates applied to terms.
data Atom = Pred String [Term] deriving (Eq, Ord, Show)

--KL formulas
data Formula = Atom Atom                -- Predicate (e.g. Teach(x, "n1"))
              | Equal Term Term         -- Equality (e.g., x = "n1")
              | Not Formula             -- Negation 
              | Or Formula Formula      -- Disjunction
              | Exists Variable Formula -- Existential (e.g., exists x (Teach x "sue")) TODO
              | K Formula               -- Knowledge Operator (e.g., K (Teach "ted" "sue"))
              deriving (Show)

-- TODO: model forall, rightarrow, leftrightarrow

-- World state: assigns values to primitive terms and atoms.
data WorldState = WorldState
  { atomValues :: Map Atom Bool        -- Truth values of ground atoms
  , termValues :: Map Term StdName     -- Values of ground terms
  } deriving (Eq, Ord, Show)

-- Infinite set of standard names (simulated as a generator).
standardNames :: [StdName]
standardNames = map (StdName . ("n" ++) . show) [1..]

-- Epistemic state: a set of possible world states.
type EpistemicState = Set WorldState

-- Helper to create a world state from atom and term assignments
mkWorldState :: [(Atom, Bool)] -> [(Term, StdName)] -> WorldState
mkWorldState atoms terms =
  WorldState (Map.fromList atoms) (Map.fromList terms)

-- Make Model explicit
data Model = Model
  { actualWorld :: WorldState      -- The actual world state
  , epistemicState :: EpistemicState -- Set of possible world states
  , domain :: Set StdName          -- Domain of standard names
  } deriving (Show)

\end{code}

Here is the definition of Kripke Models we will be using:

\begin{code}
type World = WorldState
type Universe = [World]
type Proposition = Int

type Valuation = World -> [Proposition]
type Relation = [(World,World)]

data KripkeModel = KrM Universe Valuation Relation
\end{code}

To be able to show Models, let's define a Show instance for KripkeModels:
\begin{code}
instance Show KripkeModel where
   show (KrM uni val rel) = "KrM\n" ++ show (map (pretty uni) uni) ++ "\n" ++ show [(pretty uni x, val x) | x <- uni ] ++ "\n" ++ prettyPrint uni rel where
      pretty :: Universe -> World -> Int
      pretty u w = Map.fromList (zip u (take (length u) [1..])) Map.! w 
      prettyPrint :: Universe -> Relation -> String
      prettyPrint u ((v, v'):pairs) = "(" ++ (show (pretty u v)) ++ ", " ++ (show (pretty u v')) ++ ") " ++ prettyPrint u pairs
      prettyPrint u [] = ""
\end{code}

And here the definition of the language for SEL:
\begin{code}
data ModForm = P Proposition
             | Neg ModForm
             | Con ModForm ModForm
             | Box ModForm
             | Dia ModForm
             deriving (Eq,Ord,Show)

disj :: ModForm -> ModForm -> ModForm
disj f g = Neg (Con (Neg f) (Neg g))
\end{code}

Translation functions for formulas:
\begin{code}
--stdname abbrevs copied from Lou
n1 = StdName "n1" -- ted
n2 = StdName "n2" -- sue
n3 = StdName "n3" -- tina
n4 = StdName "n4" -- tara
--example formulas to try out translators
form1 = Atom (Pred "P" [StdNameTerm n1]) 
form2 = K (Atom (Pred "P" [StdNameTerm n1]))
form3 = Not (K (Atom (Pred "P" [StdNameTerm n1])))
--for the next ones, translateFormToKr should return Nothing
form4 = Atom (Pred "Teach" [StdNameTerm n1, StdNameTerm n2]) 
form5 = Not (K (Atom (Pred "Q" [StdNameTerm n1])))

translateFormToKr :: Formula -> Maybe ModForm
translateFormToKr (Atom (Pred "P" [StdNameTerm (StdName nx)])) = Just $ P (read (drop 1 nx))    
translateFormToKr (Not f)                        = fmap Neg $ translateFormToKr f           
translateFormToKr (Or f g)                       = fmap disj (translateFormToKr f) <*> (translateFormToKr g)  
translateFormToKr (K f)                          = fmap Box $ translateFormToKr f
translateFormToKr _                              = Nothing

\end{code}

Translation functions for models:
\begin{code}
--TODO: remove duplicates in worlds, and rel
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

We check whether this works with an example adapted from Lou:
\begin{code}
w1 = mkWorldState [ (Pred "P" [StdNameTerm n1], True)
                  , (Pred "P" [StdNameTerm n3], True) ] []
w2 = mkWorldState [ (Pred "P" [StdNameTerm n1], False)
                  , (Pred "P" [StdNameTerm n4], True) ] []
w3 = mkWorldState [ (Pred "P" [StdNameTerm n1], False) ] []
e5 = Set.fromList [w1, w2, w3]
domain1 = Set.fromList [n1, n2, n3, n4]
m = Model w1 e5 domain1
\end{code}
