
\begin{code}
module TableauTests where

import SyntaxKL
import SemanticsKL
import Tableau
import Test.QuickCheck



instance Arbitrary StdName where
  arbitrary = StdName <$> elements ["n1", "n2", "n3"]

instance Arbitrary Variable where
  arbitrary = Var <$> elements ["x", "y", "z"]

instance Arbitrary Term where
  arbitrary = frequency
    [ (3, StdNameTerm <$> arbitrary)
    , (1, VarTerm <$> arbitrary)
    , (2, FuncApp <$> elements ["f", "g"] <*> resize 2 (listOf arbitrary))
    ]

instance Arbitrary Formula where
  arbitrary = sized formula
    where
      formula n
        | n <= 1 = oneof [ Atom . Pred "P" <$> resize 2 (listOf arbitrary)
                         , Equal <$> arbitrary <*> arbitrary ]
        | otherwise = oneof
            [ Atom . Pred "P" <$> resize 2 (listOf arbitrary)
            , Equal <$> arbitrary <*> arbitrary
            , Not <$> formula (n-1)
            , Or <$> formula (n `div` 2) <*> formula (n `div` 2)
            , Exists <$> arbitrary <*> formula (n-1)
            , K <$> formula (n-1)
            ]

prop_satisfiableTrue :: Formula -> Property
prop_satisfiableTrue f = isSatisfiable (Or f (Not f)) === True

prop_validTautology :: Property
prop_validTautology = forAll (resize 5 arbitrary) $ \f -> isValid (Or f (Not f)) === True

prop_notValidNonTautology :: Formula -> Property
prop_notValidNonTautology f = not (isValid f) || isValid (Not f)

prop_functionEquality :: StdName -> StdName -> Property
prop_functionEquality n1 n2 =
  let f = Equal (FuncApp "f" [StdNameTerm n1]) (StdNameTerm n2)
  in isSatisfiable f === True

prop_nestedFunctions :: StdName -> Property
prop_nestedFunctions n =
  let f = Exists (Var "x") (Equal (FuncApp "f" [FuncApp "g" [VarTerm (Var "x")]]) (StdNameTerm n))
  in isSatisfiable f === True
\end{code}