{-# LANGUAGE FlexibleInstances #-}
module BaltagString where

import Baltag hiding (true, false, testtrue, testfalse, skip, sumAction, productAction, cleanComposition, cleanChoice, cleanSum, cleanProduct, cleanAnd, cleanOr)
import BaseTypes
import Data.List
import qualified Data.Map as Map

optimize :: Map.Map String Int -> Action String -> Action Int
optimize ids (Flip p) = Flip $ optimizeAtProp ids p
optimize ids (Test p) = Test $ optimizeProposition ids p
optimize ids (Choice a b) = Choice (optimize ids a) (optimize ids b)
optimize ids (Composition a b) = Composition (optimize ids a) (optimize ids b)
optimize ids (Learn a actor) = Learn (optimize ids a) actor
optimize ids (MutualLearn a actors) = MutualLearn (optimize ids a) actors

optimizeProposition :: Map.Map String Int -> Proposition String -> Proposition Int
optimizeProposition ids (Atom atom) = Atom $ optimizeAtProp ids atom
optimizeProposition ids (Not p) = Not $ optimizeProposition ids p
optimizeProposition ids (Or a b) = Or (optimizeProposition ids a) $ optimizeProposition ids b
optimizeProposition ids (And a b) = And (optimizeProposition ids a) $ optimizeProposition ids b
optimizeProposition ids (Know act a) = Know act $ optimizeProposition ids a
optimizeProposition ids (MutualKnowledge act a) = MutualKnowledge act $ optimizeProposition ids a


optimizeAtProp :: Map.Map String Int -> AtProp String -> AtProp Int
optimizeAtProp _ (Predicate "true" []) = (Predicate 0 [])
optimizeAtProp ids (Predicate name args) = Predicate (Map.findWithDefault (-1) name ids) $ map (\a -> Map.findWithDefault (-1) a ids) args


resolveVarsBaltag :: Map.Map String String -> Action String -> Action String
resolveVarsBaltag varmap (Flip at) = Flip $ resolveVarsAtom varmap at
resolveVarsBaltag varmap (Test prop) = Test $ resolveVarsProposition varmap prop
resolveVarsBaltag varmap (Choice a b) = Choice (resolveVarsBaltag varmap a) $ resolveVarsBaltag varmap b
resolveVarsBaltag varmap (Composition a b) = Composition (resolveVarsBaltag varmap a) $ resolveVarsBaltag varmap b
resolveVarsBaltag varmap (Learn action actor) = Learn (resolveVarsBaltag varmap action) $ resolveVarsItem varmap actor
resolveVarsBaltag varmap (MutualLearn action actors) = MutualLearn (resolveVarsBaltag varmap action) $ map (resolveVarsItem varmap) actors


resolveVarsProposition :: Map.Map String String -> Proposition String -> Proposition String
resolveVarsProposition varmap (Atom at) = Atom $ resolveVarsAtom varmap at
resolveVarsProposition varmap (Not p) = Not $ resolveVarsProposition varmap p
resolveVarsProposition varmap (Or a b) = Or (resolveVarsProposition varmap a) $ resolveVarsProposition varmap b
resolveVarsProposition varmap (And a b) = And (resolveVarsProposition varmap a) $ resolveVarsProposition varmap b
resolveVarsProposition varmap (Know actor prop) = Know (resolveVarsItem varmap actor) $ resolveVarsProposition varmap prop
resolveVarsProposition varmap (MutualKnowledge actors prop) = MutualKnowledge (map (resolveVarsItem varmap) actors) $ resolveVarsProposition varmap prop
resolveVarsProposition varmap a = a


resolveVarsAtom :: Map.Map String String -> AtProp String -> AtProp String
resolveVarsAtom varmap (Predicate a args) = Predicate (resolveVarsItem varmap a) $ map (resolveVarsItem varmap) args

resolveVarsItem :: Map.Map String String -> String -> String
resolveVarsItem varmap a = Map.findWithDefault a a varmap



true = Atom $ Predicate "true" []
false = Not $ true
testtrue = Test $ true
testfalse =  Test $ false
skip = testtrue

sumAction :: [Action String] -> Action String
sumAction [] = testfalse
sumAction actions = foldr1 Choice $ actions


cleanChoice :: Action String -> Action String -> Action String
cleanChoice a b | a == testtrue = testtrue
                | b == testtrue = testtrue
                | a == testfalse = b
                | b == testfalse = a
                | otherwise = Choice a b

cleanSum :: [Action String] -> Action String
cleanSum [] = testfalse
cleanSum actions = foldr1 cleanChoice $ nub actions


productAction :: [Action String] -> Action String
productAction [] = skip
productAction actions = foldr1 Composition $ nub actions

cleanComposition :: Action String -> Action String -> Action String
cleanComposition a b | a == testtrue = b
                     | b == testtrue = a
                     | a == testfalse = testfalse
                     | b == testfalse = testfalse
                     | otherwise = Composition a b

cleanProduct :: [Action String] -> Action String
cleanProduct [] = skip
cleanProduct actions = foldr1 cleanComposition $ nub actions


cleanAnd :: Proposition String -> Proposition String -> Proposition String
cleanAnd a b | a == false = false
             | b == false = false
             | a == true = b
             | b == true = a
             | otherwise = And a b
             

cleanOr :: Proposition String -> Proposition String -> Proposition String
cleanOr a b | a == false = b
            | b == false = a
            | a == true = true
            | b == true = true
            | otherwise = Or a b
            
instance PrettyPrint (AtProp String) where
    toString ids (Predicate name args) = name ++ "(" ++ (intercalate ","  args) ++ ")"
    toLaTeX ids (Predicate name args) = name ++ "\\left(" ++ (intercalate "," args) ++ "\\right)"
            
instance PrettyPrint (Proposition String) where
    toString ids (Atom prop) = toString ids prop
    toString ids (Not prop) = "!" ++ (toString ids prop)
    toString ids (And p1 p2) = "(" ++ (toString ids p1) ++ " ^ " ++ (toString ids p2) ++ ")"
    toString ids (Apply act prop) = "[" ++ (toString ids act) ++ "]" ++ (toString ids prop)
    toString ids (Know act prop) = "B_" ++ act ++ " " ++ (toString ids prop)
    toString ids (MutualKnowledge acts prop) = "B*_" ++ (intercalate "," acts) ++ " " ++ (toString ids prop)
    
    toLaTeX ids (Atom prop) = toLaTeX ids prop
    toLaTeX ids (Not prop) = "\\neg" ++ (toLaTeX ids prop)
    toLaTeX ids (And p1 p2)= "\\left(" ++ (toLaTeX ids p1) ++ " ^ {" ++ (toLaTeX ids p2) ++ "}\\right)"
    toLaTeX ids (Apply act prop) = "\\left[" ++ (toLaTeX ids act) ++ "\right]" ++ (toLaTeX ids prop)
    toLaTeX ids (Know act prop) = "B_{" ++ act ++ "} " ++ (toLaTeX ids prop)
    toLaTeX ids (MutualKnowledge acts prop) = "B*_{" ++ (intercalate "," acts) ++ "} " ++ (toLaTeX ids prop)
    
instance PrettyPrint (Action String) where
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
