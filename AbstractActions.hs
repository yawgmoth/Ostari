module AbstractActions where

import BaseTypes
import Baltag
import qualified Data.Map as Map
import qualified Data.Set as Set

data Term = Variable VariableName
          | Property PropertyName Term
          | Property2 PropertyName Term Term
          | PropertyN PropertyName [Term]
          | Constant ConstantValue
           deriving (Show, Read, Eq)
           
termName :: Term -> String
termName (Variable name) = name
termName (Property name _) = name
termName (Property2 name _ _) = name
termName (PropertyN name _) = name
termName (Constant name) = name

getArgs :: Term -> [String]
getArgs (Property _ arg) = [termName arg]
getArgs (Property2 _ arg1 arg2) = map termName [arg1, arg2]
getArgs (PropertyN _ args) = map termName args
getArgs _ = []

{- 
   The difference between "Each" and "Forall" is:
      - "Forall" refers to the conjunction of all possibilities (e.g. "all cards in your hand are red")
      - "Each" refers to the disjunction of the conjunction of all subsets of possibilities (e.g. "which subset of your hand is red")
   In other words, "Forall" is true when something holds for all values, while "each" will tell you for which values it holds
   
   Similarly, the difference between "Exists" and "Which" is:
      - "Exists" refers to the disjunction of all possibilities (e.g. "there is a red card in your hand")
      - "Which" refers to a particular exemplar (e.g. "this is a red card in your hand")
   In other words, "Exists" is true when something holds for some value, while "which" will tell you ONE such value (this is particularly
   useful if it is known that something can only hold for one value ... e.g. there is a card such that the first card in your hand is that
   card ... "which" will tell you exactly which one that is)
-}
data Predicate = Forall VariableName SetName Predicate
                 | Each VariableName SetName Predicate
                 | Exists VariableName SetName Predicate
                 | Which VariableName SetName Predicate
                 | Equal Term Term
                 | NotEqual Term Term
                 | AndP Predicate Predicate
                 | OrP Predicate Predicate
                 | IsSet Term
                 | IsUnSet Term
                 | Believes Actor Predicate
                 | NotBelieves Actor Predicate
                 deriving (Show, Read, Eq)


data AbstractAction = Sequence [AbstractAction]
                  | PublicArgument VariableName SetName AbstractAction
                  | SecretArgument [Actor] VariableName SetName AbstractAction
                  | Inform [Actor] Predicate
                  | Suspect [Actor] Predicate
                  | InformElse [Actor] Predicate
                  | Initialize Term Term
                  | Set Term Term
                  | UnSet Term
                  | If Predicate AbstractAction
                  | Precondition Predicate
                  | IfElse Predicate AbstractAction AbstractAction
                  | PublicIfElse [Actor] Predicate AbstractAction AbstractAction
                  | Public [Actor] AbstractAction
                  | DEL (Action String)
                  deriving (Show, Read, Eq)

data Context = GameContext {
              sets :: Map.Map String [String],
              signatures :: Map.Map String [String], -- for predicates, which types the arguments should range over ... e.g. at(c, p, i) -> [Cards, Players, Indices]
              actors :: [String], -- All actors
              static_predicates :: Map.Map String [[String]], -- predicates that are never changed by actions
              restricted_predicates :: Map.Map String [[String]] -- predicates that are known to only hold on a subset (e.g. because of a functional dependency between arguments)
          }
          deriving (Show, Eq)

getArgNames :: AbstractAction -> [VariableName]
getArgNames (PublicArgument var _ act) = var:(getArgNames act)
getArgNames (SecretArgument _ var _ act) = var:(getArgNames act)
getArgNames _ = []

getArgTypes :: AbstractAction -> [SetName]
getArgTypes (PublicArgument _ set act) = set:(getArgTypes act)
getArgTypes (SecretArgument _ _ set act) = set:(getArgTypes act)
getArgTypes _ = []

getActionArgs :: AbstractAction -> [(VariableName,SetName)]
getActionArgs (PublicArgument var set act) = (var,set):(getActionArgs act)
getActionArgs (SecretArgument _ var set act) = (var,set):(getActionArgs act)
getActionArgs _ = []
          
getReturnType :: Context -> String -> String
getReturnType ctx name = head (getList (signatures ctx) name)


getList :: Map.Map String [String] -> String -> [String]
getList typemap name = Map.findWithDefault [] name typemap

getValues :: Context -> String -> [String]
getValues ctx setname = Map.findWithDefault [] setname $ sets ctx

nop = Sequence []

makeIDMap :: Context -> Map.Map String Int
makeIDMap ctx@(GameContext {sets=s, signatures=sigs}) = Map.fromList $ [("true", 0), ("false", 1)] ++ siglist ++ idlist
                       where
                           siglist = zip (Map.keys sigs) [3..]
                           idlist = foldl (++) [] [[(val,start set + id) | (val,id) <- zip (Map.findWithDefault [] set s) [1..]] | set <- Map.keys s]
                           start target = (length $ Map.keys sigs) + (sum $ map length [Map.findWithDefault [] set s | set <- takeWhile (/= target) $ Map.keys s] ) + 2

makeReverseIDMap :: Context -> Map.Map Int String
makeReverseIDMap ctx = Map.fromList [(v,k) | (k,v) <- Map.assocs $ makeIDMap ctx]

getValue :: Context -> PointedModel -> String -> [String] -> String
getValue ctx pm name args = getValue' ctx pm (convert name) $ map convert args
                         where
                               ids = makeIDMap ctx
                               convert x = Map.findWithDefault (-1) x ids
                               
getValue' :: Context -> PointedModel -> Int -> [Int] -> String
getValue' ctx (PM app fact _) name args = convert value
                                      where
                                         rids = makeReverseIDMap ctx
                                         convert x = Map.findWithDefault "unknown" x rids
                                         matches = Set.filter match fact
                                         match (Predicate p a) = p == name && and (map (\(x,y) -> x == y) $ zip a args)
                                         lastArg (Predicate p a) = last a
                                         value = if Set.null matches then (-1) else lastArg $ (Set.toList matches)!!0




