{-# LANGUAGE FlexibleInstances #-}
module Baltag where

import BaseTypes
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set


data Proposition a = Atom (AtProp a)
                 | Not (Proposition a)
                 | Or (Proposition a) (Proposition a)
                 | And (Proposition a) (Proposition a)
                 | Apply (Action a) (Proposition a)
                 | Know Actor (Proposition a)
                 | MutualKnowledge [Actor] (Proposition a)
                 deriving (Read, Show, Eq)

data Action a = Flip (AtProp a)
            | Test (Proposition a)
            | Choice (Action a) (Action a)
            | Composition (Action a) (Action a)
            | Learn (Action a) Actor
            | MutualLearn (Action a) [Actor]
              deriving (Read, Show, Eq)


true = Atom $ Predicate 0 []
false = Not $ true
testtrue = Test $ true
testfalse =  Test $ false
skip = testtrue

termCount :: Action a -> Int
termCount (Flip _) = 1
termCount (Test _) = 1
termCount (Choice a b) = (termCount a) + (termCount b)
termCount (Composition a b) = (termCount a) + (termCount b)
termCount (Learn a _) = termCount a
termCount (MutualLearn a _) = termCount a


sumAction :: [Action Int] -> Action Int
sumAction [] = testfalse
sumAction actions = foldr1 Choice $ actions



cleanChoice :: Action Int -> Action Int -> Action Int
cleanChoice a b | a == testtrue = testtrue
                | b == testtrue = testtrue
                | a == testfalse = b
                | b == testfalse = a
                | otherwise = Choice a b

cleanSum :: [Action Int] -> Action Int
cleanSum [] = testfalse
cleanSum actions = foldr1 cleanChoice $ nub actions



productAction :: [Action Int] -> Action Int
productAction [] = skip
productAction actions = foldr1 Composition $ nub actions

cleanComposition :: Action Int -> Action Int -> Action Int
cleanComposition a b | a == testtrue = b
                     | b == testtrue = a
                     | a == testfalse = testfalse
                     | b == testfalse = testfalse
                     | otherwise = Composition a b

cleanProduct :: [Action Int] -> Action Int
cleanProduct [] = skip
cleanProduct actions = foldr1 cleanComposition $ nub actions


cleanAnd :: Proposition Int -> Proposition Int -> Proposition Int
cleanAnd a b | a == false = false
             | b == false = false
             | a == true = b
             | b == true = a
             | otherwise = And a b
             

cleanOr :: Proposition Int -> Proposition Int -> Proposition Int
cleanOr a b | a == false = b
            | b == false = a
            | a == true = true
            | b == true = true
            | otherwise = Or a b

pre :: Action Int -> Proposition Int
pre (Test prop) = prop
pre (Choice a b) = cleanOr (pre a) (pre b)
pre (Composition a b) | hasChange a = cleanAnd (pre a) (Apply a (pre b))
                      | otherwise   = And (pre a) (pre b)
pre (MutualLearn act _) = pre act
pre _ = true

hasChange :: Action a -> Bool
hasChange (Test prop) = False
hasChange (Choice a b) = (hasChange a) || (hasChange b)
hasChange (Composition a b) = (hasChange a) || (hasChange b)
hasChange (MutualLearn act _) = hasChange act
hasChange _ = True

appearance :: Actor -> Action Int -> Action Int
appearance a (Learn act who) | who == a  = act
                             | otherwise = skip
appearance a (Choice act1 act2) = cleanChoice (appearance a act1) (appearance a act2)
appearance a (Composition act1 act2) = cleanComposition (appearance a act1) (appearance a act2)
appearance a (MutualLearn act actors) | a `elem` actors = cleanComposition (appearance a act) (MutualLearn act actors)
                                      | otherwise = appearance a act
appearance _ _ = skip

issimple :: Action a -> Bool
issimple (Flip _) = True
issimple (Test _) = True
issimple (Composition a b) = (issimple a) && (issimple b)
issimple (Learn _ _) = True
issimple (MutualLearn act _) = issimple act
issimple _ = False



content :: Ord a => Action a -> Set.Set (AtProp a)
content (Flip p) = Set.singleton p
content (Test _) = Set.empty
content (Composition a b) = symdiff (content a) (content b)
content (Learn _ _) = Set.empty
content (MutualLearn act _) = content act
content _ = Set.empty

choice :: Action Int -> [Action Int]
choice act | issimple act = [act]
           | otherwise = choice' act
           
choice' :: Action Int -> [Action Int]
choice' (Choice a b)             = (choice a) `union` (choice b)
choice' (Composition a b)        = [Composition a1 b1 | a1 <- (choice a), b1 <- (choice b)]
choice' (MutualLearn act actors) = [Composition a subaction | a <- (choice act)]
                                 where 
                                    subaction = productAction [Learn (MutualLearn act actors) a | a <- actors]
choice' _ = []

alternatives :: Actor -> Action Int -> [Action Int]
alternatives a act = choice $ appearance a act
    
data PointedModel = PM (String -> [PointedModel]) (Set.Set (AtProp Int)) [String]

truth :: Maybe PointedModel -> [AtProp Int]
truth (Just (PM app fact _)) = Set.toList fact
truth Nothing = []

fact (PM app f _) = f

factList (PM app f _) = Set.toList f

looksLike :: PointedModel -> String -> [PointedModel]
looksLike (PM app _ _) act = app act




type IDMap = Map.Map Int String

class PrettyPrint a where
    toString :: IDMap -> a -> String
    toLaTeX :: IDMap -> a -> String
    
instance PrettyPrint PointedModel where
    toLaTeX _ _ = ""
    toString ids (PM app f actors) = "Truth: " ++ (show $ Set.toList $ Set.map (toString ids) f) ++ " looks like: \n" ++ (intercalate "" $ map (\act -> (act ++ ": " ++ (show $ map (map (toString ids)) $ map factList $ app act) ++ "\n")) actors)
    
instance PrettyPrint (AtProp Int) where
    toString ids (Predicate name args) = (Map.findWithDefault "unknown" name ids) ++ "(" ++ (intercalate "," $ map (\a -> Map.findWithDefault "unknown" a ids) args) ++ ")"
    toLaTeX ids (Predicate name args) = (Map.findWithDefault "unknown" name ids) ++ "\\left(" ++ (intercalate "," $ map (\a -> Map.findWithDefault "unknown" a ids) args) ++ "\\right)"
    

    
instance PrettyPrint (Proposition Int) where
    toString ids (Atom prop) = toString ids prop
    toString ids (Not prop) = "!" ++ (toString ids prop)
    toString ids (And p1 p2) = "(" ++ (toString ids p1) ++ " ^ " ++ (toString ids p2) ++ ")"
    toString ids (Or p1 p2) = "(" ++ (toString ids p1) ++ " v " ++ (toString ids p2) ++ ")"
    toString ids (Apply act prop) = "[" ++ (toString ids act) ++ "]" ++ (toString ids prop)
    toString ids (Know act prop) = "B_" ++ act ++ " " ++ (toString ids prop)
    toString ids (MutualKnowledge acts prop) = "B*_" ++ (intercalate "," acts) ++ " " ++ (toString ids prop)
    
    toLaTeX ids (Atom prop) = toLaTeX ids prop
    toLaTeX ids (Not prop) = "\\neg" ++ (toLaTeX ids prop)
    toLaTeX ids (And p1 p2)= "\\left(" ++ (toLaTeX ids p1) ++ " \\wedge {" ++ (toLaTeX ids p2) ++ "}\\right)"
    toLaTeX ids (Or p1 p2)= "\\left(" ++ (toLaTeX ids p1) ++ " \\vee {" ++ (toLaTeX ids p2) ++ "}\\right)"
    toLaTeX ids (Apply act prop) = "\\left[" ++ (toLaTeX ids act) ++ "\right]" ++ (toLaTeX ids prop)
    toLaTeX ids (Know act prop) = "B_{" ++ act ++ "} " ++ (toLaTeX ids prop)
    toLaTeX ids (MutualKnowledge acts prop) = "B*_{" ++ (intercalate "," acts) ++ "} " ++ (toLaTeX ids prop)
    
instance PrettyPrint (Action Int) where
    toString ids (Flip prop) = "flip " ++ (toString ids prop)
    toString ids (Test prop) = "?" ++ (toString ids prop)
    toString ids (Choice a1 a2) = (toString ids a1) ++ " + " ++ (toString ids a2)
    toString ids (Composition (Choice a1 a2) (Choice b1 b2)) = "(" ++ (toString ids (Choice a1 a2)) ++ ") . (" ++ (toString ids (Choice b1 b2)) ++ ")"
    toString ids (Composition (Choice a1 a2) b) = "(" ++ (toString ids (Choice a1 a2)) ++ ") . " ++ (toString ids b)
    toString ids (Composition a (Choice b1 b2)) = (toString ids a) ++ " . (" ++ (toString ids (Choice b1 b2)) ++ ")"
    toString ids (Composition a1 a2) = (toString ids a1) ++ " . " ++ (toString ids a2)
    toString ids (Learn act actor) = "(" ++ (toString ids act) ++ ")^" ++ actor
    toString ids (MutualLearn act actors) = "(" ++ (toString ids act) ++ ")*^" ++ (intercalate "," actors) 
    
    toLaTeX ids (Flip prop) = "\\text{flip} " ++ (toLaTeX ids prop)
    toLaTeX ids (Test prop) = "\\?" ++ (toLaTeX ids prop)
    toLaTeX ids (Choice a1 a2) = "\\left(" ++ (toLaTeX ids a1) ++ " + " ++ (toLaTeX ids a2) ++ "\\right)"
    toLaTeX ids (Composition a1 a2) = "\\left(" ++ (toLaTeX ids a1) ++ " \\cdot " ++ (toLaTeX ids a2) ++ "\\right)"
    toLaTeX ids (Learn act actor) = "\\left(" ++ (toLaTeX ids act) ++ "\\right)^{" ++ actor ++ "}"
    toLaTeX ids (MutualLearn act actors) = "\\left(" ++ (toLaTeX ids act) ++ "\\right)*^{" ++ (intercalate "," actors) ++ "}"
    

    
