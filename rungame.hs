module Main where

import GameParser
import qualified System.Environment as E
import Text.ParserCombinators.Parsec
import Control.Monad
import Baltag
import AbstractActions
import ActionCompiler
import BaltagExecution
import AbstractActionParser
import qualified Data.ByteString as B
import qualified Data.Map as Map
import Data.List
import Debug.Trace
import Data.Either
import Data.Function
import Data.List.Split
import Control.Parallel.Strategies

extractResult (Right r) = r

main :: IO()
main = do
          args <- E.getArgs
          let fname = head args
          input <- processFile fname
          processParseResult input
          
processFile fname = do
          content <- readFile fname
          return $ parse parseGame fname content

processParseResult (Left err) = putStrLn $ show err
processParseResult (Right presult) = do
                                      let (ctx,init,execute,actions) = presult
                                      let ids = makeReverseIDMap ctx
                                      doExecute execute ctx [init] (Map.fromList actions) 

plan :: [PointedModel] -> Action Int -> Map.Map String AbstractAction -> Context -> Map.Map Int String -> [(PointedModel,[String])]
plan states goal actionmap ctx ids = plan' (map (\s -> (s,[])) states) goal actionmap ctx ids
                          
plan' :: [(PointedModel,[String])] -> Action Int -> Map.Map String AbstractAction -> Context -> Map.Map Int String -> [(PointedModel,[String])]
plan' states goal actionmap ctx ids = plan'' states goal allactions ctx ids
                          where
                              actionlist = foldl (++) [] [argAssignments action ctx name | (name,action) <- Map.toList actionmap]
                              suspectlist alist = foldl (++) [] [map (\act -> (Learn action act, act ++ " suspects " ++ aname)) $ actors ctx | (action,aname) <- alist]
                              slist = suspectlist actionlist
                              sslist = suspectlist slist
                              allactions = actionlist ++ slist -- ++ sslist
                              
plan'' :: [(PointedModel,[String])] -> Action Int -> [(Action Int,String)] -> Context -> Map.Map Int String -> [(PointedModel,[String])]
plan'' states goal allactions ctx ids = trace ("have: " ++ (show $ length states)) $ if null frontier then [] else if (or canexec) then map snd $ filter (fst) $ zip canexec states else plan'' frontier goal allactions ctx ids
                          where
                              canexec = map (\(s,t) -> canExecute s goal) states 
                              frontier =  frontier'
                              frontier' = foldl (++) [] [map (\s1 -> (s1,t++[repr])) $ (execute s compiled `using` rpar) | (s,t) <- states, (compiled,repr) <- allactions]

                              
argAssignments action ctx aname = [(compile action ctx $ Map.fromList $ zip argnames args, aname ++ "(" ++ (intercalate ", " args) ++ ")") | args <- sequence [getValues ctx arg | arg <- getArgTypes action] ]
                          where
                              argnames = getArgNames action
  
actionName :: String -> String  
actionName ('s':'u':'s':'p':'e':'c':'t':'(':xs) = actionName $ intercalate " " $ tail (splitOn " " xs)
actionName name = name

actionDecorations ('s':'u':'s':'p':'e':'c':'t':'(':xs) = head (splitOn ")" xs):(actionDecorations $ intercalate " " $ tail (splitOn " " xs))
actionDecorations name = []

decorate action [] = action
decorate action (x:xs) = Learn (decorate action xs) x
          
doExecute [] _ _ _ = putStrLn "Done."
doExecute ((name,args):xs) ctx states actionmap = 
                                                 do
                                                  let decorations = actionDecorations name
                                                  let actionname = actionName name
                                                  let action = Map.findWithDefault nop actionname actionmap
                                                  let argnames = getArgNames action
                                                  let argassignment = Map.fromList $ zip argnames args
                                                  let compiled = compile action ctx argassignment
                                                  let decorated = decorate compiled decorations
                                                  let goal = compilePredicate (read (args!!0)::Predicate) ctx
                                                  let goalstates = plan states goal actionmap ctx ids
                                                  if name == ":print" then
                                                        if (args!!0) == "facts" then putStrLn $ "State of the world is now: \n" ++ (intercalate "\n\nor:\n" $ map (\s -> intercalate ", " (map (toString ids) $ factList s)) states) ++ "\n" else 
                                                        if (args!!0) == "model" then putStrLn $ "The world is now: \n" ++ (intercalate "\nor:\n" $ map (toString ids) states) ++ "\n" else 
                                                        do
                                                            let (aname,aargs) = extractResult $ parseActionCall $ trace (show args) $ head args
                                                            let paction = Map.findWithDefault nop aname actionmap
                                                            let pargnames = getArgNames paction
                                                            let pargassignment = Map.fromList $ zip pargnames aargs
                                                            let pcompiled = compile paction ctx pargassignment
                                                            putStrLn $ show paction
                                                            putStrLn $ toString ids pcompiled
                                                            putStrLn $ intercalate "\n" ["appears to " ++ a ++" as:\n " ++ (intercalate " \nor\n " $ map (toString ids) $ alternatives a pcompiled) ++ "\n\n" | a <- actors ctx]
                                                            putStrLn $ "pre: " ++ (toString ids $ pre pcompiled)
                                                            putStrLn $ "applicable: " ++ (show $ interprets (head states) $ pre pcompiled)
                                                            
                                                  else
                                                      if name == ":query" then do
                                                          let query = compilePredicate (read (args!!0)::Predicate) ctx
                                                          putStrLn $ "Query: " ++ (toString ids $ query) ++ ": " ++ (show (and [canExecute state query | state <- states])) ++ "\n"
                                                      else if name == ":goal" then do
                                                          putStrLn $ "Finding trajectory to " ++ (toString ids $ goal)
                                                          putStrLn $ "For example: " ++ (show $ snd $ goalstates!!0) ++ "\n\n"
                                                      else do
                                                          putStrLn $ "Executing " ++ name ++ "(" ++ (intercalate ", " args) ++ ")\n"
                                                  
                                                  let newstates = if name == ":goal" then [head $ map fst goalstates] else
                                                                  if (name `elem` [":print", ":query"]) then states else take 1 $ foldl (++) [] [execute s decorated | s <- states]
                                                  doExecute xs ctx newstates actionmap
                                                where 
                                                  ids = makeReverseIDMap ctx
                                                  

     