\section{Ask & Tell Operators}\label{sec:AskTell}

% Needs satisfies function from previous Repo

\begin{code}
module AskTell (ask, initial) where
import qualified Data.Map as Map
import qualified Data.Set as Set
import SyntaxKL
import SemanticsKL

-- the following satisfies works on formulas without quantifiers?

-- ASK (Definition 5.2.1)
ask :: Set.Set StdName -> EpistemicState -> Formula -> Bool
ask d e alpha | Set.null e = False
              | otherwise = satisfiesModel newModel (K alpha) where
              newModel = Model {actualWorld = (Set.findMin e), epistemicState = e, domain = d}


-- ask :: EpistemicState -> Formula -> Bool
-- ask e alpha | Set.null e = False
--             | otherwise = satisfies e (Set.findMin e) (K alpha) -- still need to define a satisfies function

askModel :: Model -> Formula -> Bool
askModel m alpha |  Set.null (epistemicState m) = False
             |  otherwise = satisfiesModel m (K alpha)

-- TELL operation (Definition 5.5.1)
-- tell :: EpistemicState -> Formula -> EpistemicState
-- tell e alpha = Set.filter (\w -> satisfies e w alpha) e

tellModel :: Model -> Formula -> Model
tellModel m alpha = Model {actualWorld = actualWorld m, epistemicState = Set.filter filterfunc  (epistemicState m), domain = domain m} where
    filterfunc = (\w -> satisfiesModel (Model {actualWorld = w, epistemicState = epistemicState m, domain = domain m}) alpha)

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

