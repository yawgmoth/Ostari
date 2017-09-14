module GameParser where

import AbstractActions
import AbstractActionParser
import BaseTypes
import Baltag
import BaltagString
import Text.ParserCombinators.Parsec
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Debug.Trace

parseListValue = identifier `sepBy` (symbol ",")
parseListValue1 = identifier `sepBy1` (symbol ",")

parseType = do 
               many space
               name <- identifier
               symbol "="
               values <- identifier `sepBy` (symbol ",")
               return $ (name,values)

parseIdentifierListValue = do
                               many space
                               value <- identifier
                               return value
                               
parseRestriction = do
                      value <- identifier
                      symbol ":"
                      domain <- identifier `sepBy` (symbol ",")
                      return (value, domain)
                      
                         
parseRestrictions = do
                       result <- parens $ parseRestriction `sepBy` (symbol ";")
                       return result

parseProperties = do
                     name <- identifier
                     symbol "::"
                     types <- identifier `sepBy` (symbol "->")
                     many $ string " "
                     restriction <- parseRestrictions
                     many space
                     return (name, types, restriction)

parsePermutation = do
                      symbol "permutation"
                      nr <- many1 digit
                      return nr
                     
parseOperation = do 
                    op <- (try $ string "any permutation") <|> parsePermutation
                    many space
                    symbol "of"
                    set <- identifier 
                    return (op,[set])


parseTemporary = do
                    symbol "let "
                    name <- identifier
                    symbol "="
                    operation <- parseOperation
                    return ("let",((name,[]),operation))

          
                    
parseProperty = do
                    many space
                    head <- parsePropertyHead
                    symbol "="
                    tail <- parsePropertyHead
                    return ("set",(head,tail))
                    
                     
parseAssignment = try parseTemporary <|> GameParser.parseProperty
                      
                    
parseInitial = do
                    many space
                    assignments <- many $ try parseAssignment
                    looksLike <- many $ try parseLooksLike
                    return (assignments,foldl (++) [] looksLike)

parseLooksLike = do
                     many space
                     symbol "looks like "
                     actors <- parens parseListValue1
                     symbol ":"
                     states <- identifier `sepBy` (symbol ",")
                     return [(a,states) | a <- actors]
                     
parsePropertyHead = do
                       name <- identifier
                       args <- parens parseListValue
                       many space
                       return (name, args)
                     
parseKnows = do
                 many space
                 symbol "knows "
                 actor <- identifier
                 symbol ":"
                 properties <- many $ try GameParser.parseProperty
                 return (actor,properties)
                     
parseState = do 
                many space
                symbol "state "
                name <- identifier
                symbol ":"
                content <- parseInitial
                return (name,content)

parseQuery = do
                many space
                symbol "query:"
                query <- parsePredicate
                return (":query", [show query])
                
parsePrint = try parsePrintAction <|> try parsePrintSimple
                
parsePrintSimple = do
                many space
                symbol "print:"
                query <- identifier
                return (":print", [query])
                

                
parsePrintAction = do
                many space
                symbol "print:"
                
                action <- identifier 
                args <- parens parseListValue
                return (":print", [action ++ "(" ++ (intercalate ", " args) ++ ")"])

parseGoal = do
                many space
                symbol "goal:"
                goal <- parsePredicate
                return (":goal", [show goal])
                

                
parsePlay = do
                many space
                symbol "play:"
                players <- parsePlayer `sepBy` (symbol ",")
                return (":play", players)
                
parsePlayer = do
                many space
                name <- identifier
                symbol ":"
                ai <- identifier
                many space
                return $ name ++ " " ++ ai
                 

parseExecuteAction = do
                 many space
                 action <- identifier
                 args <- parens parseListValue
                 return (action,args)
                 
parseSuspectAction = do
                 many space
                 actor <- identifier
                 symbol1 "suspects"
                 (action,args) <- try parseExecuteAction <|> try parseSuspectAction
                 return ("suspect(" ++ actor ++ ") " ++ action,args)

parseExecute = (try parseQuery <|> try parsePrint <|> try parseGoal <|> try parsePlay <|> try parseSuspectAction <|> parseExecuteAction)
                    
parseGame = do 
               symbol "Types:"
               types <- many1 $ try parseType
               many space
               symbol "Properties:"
               props <- many1 $ try parseProperties
               many space
               symbol "Actions:"
               actions <- many1 $ try abstractActionHeader
               many space
               symbol "Initial:"
               initial <- parseInitial
               many space
               states <- many $ try parseState
               many space
               knows <- many $ try parseKnows
               many space
               symbol "Execute:"
               execute <- many1 $ try parseExecute
               many space
               symbol "Done."
               let ctx = makeContext types props
               let acts = actors ctx
               let ids = makeIDMap ctx
               let state = if length knows == 0 then makeState ids "Initial" (Map.fromList (("Initial",initial):states)) acts else
                           if length states == 0 then buildStateGraph ids initial acts knows else makeState ids "Initial" (Map.fromList (("Initial",initial):states)) acts
               return $ (ctx,state,execute,map (\(a,b) -> (a, fixSets ctx b)) actions)
               
fixSet :: Context -> [String] -> [String]
fixSet ctx set | (length set == 1 && "set: " `isPrefixOf` (head set)) = Map.findWithDefault [] (drop 5 $ head set) (sets ctx)
               | otherwise                                            = set
               
fixSets :: Context -> AbstractAction -> AbstractAction
fixSets ctx (Sequence seq) = Sequence $ map (fixSets ctx) seq
fixSets ctx (PublicArgument v s act) = PublicArgument v s $ fixSets ctx act
fixSets ctx (SecretArgument acts v s act) = SecretArgument (fixSet ctx acts) v s $ fixSets ctx act
fixSets ctx (Inform acts pred) = Inform (fixSet ctx acts) $ fixSetsPredicate ctx pred
fixSets ctx (InformElse acts pred) = InformElse (fixSet ctx acts) $ fixSetsPredicate ctx pred
fixSets ctx (If pred act) = If (fixSetsPredicate ctx pred) $ fixSets ctx act
fixSets ctx (IfElse pred ifact elseact) = IfElse (fixSetsPredicate ctx pred) (fixSets ctx ifact) $ fixSets ctx elseact
fixSets ctx (PublicIfElse acts pred ifact elseact) = PublicIfElse (fixSet ctx acts) (fixSetsPredicate ctx pred) (fixSets ctx ifact) $ fixSets ctx elseact
fixSets ctx x = x               


fixSetsPredicate :: Context -> Predicate -> Predicate
fixSetsPredicate ctx (Forall v s pred) = Forall v s $ fixSetsPredicate ctx pred
fixSetsPredicate ctx (Each v s pred) = Each v s $ fixSetsPredicate ctx pred
fixSetsPredicate ctx (Exists v s pred) = Exists v s $ fixSetsPredicate ctx pred
fixSetsPredicate ctx (Which v s pred) = Which v s $ fixSetsPredicate ctx pred
fixSetsPredicate ctx (AndP a b) = AndP (fixSetsPredicate ctx a) $ fixSetsPredicate ctx b
fixSetsPredicate ctx (OrP a b) = OrP (fixSetsPredicate ctx a) $ fixSetsPredicate ctx b
fixSetsPredicate ctx (Believes a pred) = Believes a $ fixSetsPredicate ctx pred
fixSetsPredicate ctx (NotBelieves a pred) = NotBelieves a $ fixSetsPredicate ctx pred
fixSetsPredicate ctx p = p

type PropertyDefinition = (String,[String])
type Assignment = (String,(PropertyDefinition,PropertyDefinition))
               
toPredicate :: Assignment -> AtProp String
toPredicate ("set",((prop,args), (value,[]))) = Predicate prop $ args ++ [value]

buildStateGraph :: Map.Map String Int -> ([Assignment], [(String,[String])]) -> [String] -> [(String,[Assignment])] -> PointedModel
buildStateGraph ids initial actors knowledge = PM (\a -> findStates facts a) facts actors
                                            where
                                                knownProps = nub $ foldl (++) [] $ map snd knowledge
                                                knowMap = Map.fromList knowledge
                                                content = fst $ initial
                                                facts = Set.fromList $ map (\p -> optimizeAtProp ids $ toPredicate p) content
                                                opt a =  map (\p -> optimizeAtProp ids $ toPredicate p) a
                                                assignments = map (Set.fromList) $ subsequences $ opt knownProps
                                                allstates = [PM (\a -> findStates assignment a) assignment actors | assignment <- assignments]
                                                knows a = Set.fromList $ opt $ Map.findWithDefault [] a knowMap
                                                makeStates assignment a = [state | state <- allstates, Set.null $ ((fact state) `symdiff` (assignment)) `Set.intersection` (knows a) ]
                                                stateMap = Map.fromList [((assignment,a),makeStates assignment a) | assignment <- assignments, a <- actors]
                                                findStates assignment a = Map.findWithDefault (makeStates assignment a) (assignment,a) stateMap
                                                

makeState ids name allStates actors = PM (getState) facts actors
                                    where
                                       thisState = Map.findWithDefault ([],[]) name allStates
                                       (content,appearance) = thisState
                                       appearanceMap = Map.fromList appearance
                                       getState a = [makeState ids s allStates actors | s <- Map.findWithDefault [] a appearanceMap]
                                       facts = Set.fromList $ map (\p -> optimizeAtProp ids $ toPredicate p) content

toSignature (name,args,_) = (name, (args!!n):(init args))
                         where 
                            n = length args - 1

makeContext sets props = GameContext { sets = setMap, signatures = signatures, actors = Map.findWithDefault [] "Players" setMap, static_predicates = staticMap, restricted_predicates=restrictedMap }
                                    where
                                       setMap = Map.fromList sets
                                       signatures = Map.fromList $ map toSignature props
                                       hasrestrictions = filter hasRestrictions props
                                       (statics,restricted) = partition isStatic hasrestrictions
                                       staticMap = Map.fromList [(name,makeValues restrictions) | (name,_,restrictions) <- statics]
                                       restrictedMap = Map.fromList [(name,makeValues restrictions) | (name,_,restrictions) <- restricted]
                                       
                                       
hasRestrictions (_,_,[]) = False
hasRestrictions (_,_,_) = True

makeValues :: [(String,[String])] -> [[String]]
makeValues [] = []
makeValues ((arg,vals):xs) = itemLists ++ (makeValues xs)
                          where
                             items = zip (repeat arg) vals
                             itemLists = map (\(a,b) -> [a,b]) items

isStatic (name,args,restrictions) = and [length limits == 1 | (value,limits) <- restrictions]
                                       
parseActionCall :: String -> Either ParseError (String,[String])
parseActionCall text = parse parseExecuteAction "(unknown)" text