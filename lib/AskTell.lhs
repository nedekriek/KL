\section{Ask & Tell Operators}\label{sec:AskTell}

% Needs satisfies function from previous Repo

\begin{code}
module AskTell (ask, tell, initial) where

import qualified Data.Set as Set
import SyntaxKL
import SemanticsKL


-- ASK (Definition 5.2.1)
ask :: EpistemicState -> Formula -> Bool
ask e alpha | Set.null e = False
            | otherwise = satisfies e (Set.findMin e) (K alpha)

askModel :: Model -> Formula -> Bool
askModel m alpha |  Set.null (epistemicState m) = False
             |  otherwise = satisfiesModel m (K alpha)

-- TELL operation (Definition 5.5.1)
tell :: EpistemicState -> Formula -> EpistemicState
tell e alpha = Set.filter (\w -> satisfies e w alpha) e

tellModel :: Model -> Formula -> Model
tellModel m alpha = {actualWorld m, Set.filter (\w -> satisfiesModel modelAtWorld alpha) e,  } where
    modelAtWorld = {w :: actualWorld,  }

-- INITIAL operation (Section 5.3)
-- Need to recreate the allWorldStates model
initial :: [Atom] -> [Term] -> [StdName] -> EpistemicState
initial atoms terms domain = Set.fromList (allWorldStates atoms terms domain)


\end{code}

