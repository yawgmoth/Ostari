module BaseTypes where

import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

type Actor = String
type VariableName = String
type ConstantValue = String
type SetName = String
type PredicateName = String
type PropertyName = String

type VarMap = Map.Map VariableName ConstantValue


data AtProp a = Predicate a [a]
            deriving (Show, Read, Eq, Ord)

            
            
{-symdiff :: Eq a => [a] -> [a] -> [a]-}
symdiff :: Ord a => Set.Set a -> Set.Set a -> Set.Set a
symdiff a b = (a Set.\\ b) `Set.union`  (b Set.\\ a)

