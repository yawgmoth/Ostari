module ActionCompiler where

import Baltag hiding (true, false, testtrue, testfalse, skip, sumAction, productAction, cleanComposition, cleanChoice, cleanSum, cleanProduct, cleanAnd, cleanOr)
import BaltagString
import AbstractActions
import BaseTypes
import Debug.Trace
import Control.Monad.State  
import qualified Data.Map as Map
import Data.Ord
import Data.List


type VariableNamer = State Int
nextVar :: Int -> Int
nextVar = (+1)

compilePredicate :: Predicate -> Context -> Action Int
compilePredicate pred ctx = optimize (makeIDMap ctx) p
                     where
                        (p,n) = runState (compileCondition pred ctx) 0

compile :: AbstractAction -> Context -> VarMap -> Action Int
compile action ctx vars = optimize (makeIDMap ctx) act
                     where
                        --resolvedaction = resolveVarsAbstract ctx vars action
                        --argalternatives = makeAlternativeActions resolvedaction ctx
                        (act,n) = runState (makeAlternativeActions action ctx vars) 0
                        
resolveVarsAbstract :: Context -> VarMap -> AbstractAction -> AbstractAction
resolveVarsAbstract ctx varmap (PublicArgument varname setname action) = PublicArgument varname setname $ resolveVarsAbstract ctx varmap action
resolveVarsAbstract ctx varmap (SecretArgument actors varname setname action) = SecretArgument (resolveList ctx varmap actors) varname setname $ resolveVarsAbstract ctx varmap action
resolveVarsAbstract ctx varmap (Inform actors action) = Inform (resolveList ctx varmap actors) $ resolveVarsPredicate varmap action
resolveVarsAbstract ctx varmap (Suspect actors action) = Suspect (resolveList ctx varmap actors) $ resolveVarsPredicate varmap action
resolveVarsAbstract ctx varmap (InformElse actors action) = InformElse (resolveList ctx varmap actors) $ resolveVarsPredicate varmap action
resolveVarsAbstract ctx varmap (Sequence actions) = Sequence $ map (resolveVarsAbstract ctx varmap) actions
resolveVarsAbstract ctx varmap (Set term value) = Set (resolveVarsTerm varmap term) (resolveVarsTerm varmap value)
resolveVarsAbstract ctx varmap (Initialize term value) = Initialize (resolveVarsTerm varmap term) (resolveVarsTerm varmap value)
resolveVarsAbstract ctx varmap (UnSet term) = UnSet (resolveVarsTerm varmap term)
resolveVarsAbstract ctx varmap (If condition action) = If (resolveVarsPredicate varmap condition) $ resolveVarsAbstract ctx varmap action
resolveVarsAbstract ctx varmap (Precondition condition) = Precondition $ resolveVarsPredicate varmap condition
resolveVarsAbstract ctx varmap (IfElse condition ifaction elseaction) = IfElse (resolveVarsPredicate varmap condition) (resolveVarsAbstract ctx varmap ifaction) $ resolveVarsAbstract ctx varmap elseaction
resolveVarsAbstract ctx varmap (PublicIfElse actors condition ifaction elseaction) = PublicIfElse (resolveList ctx varmap actors) (resolveVarsPredicate varmap condition) (resolveVarsAbstract ctx varmap ifaction) $ resolveVarsAbstract ctx varmap elseaction
resolveVarsAbstract ctx varmap (Public actors inner) = Public (resolveList ctx varmap actors) $ resolveVarsAbstract ctx varmap inner
resolveVarsAbstract ctx varmap (DEL action) = DEL $ resolveVarsBaltag varmap action

resolveVarsPredicate :: VarMap -> Predicate -> Predicate
resolveVarsPredicate varmap (Forall var set pred) = Forall var set $ resolveVarsPredicate varmap pred
resolveVarsPredicate varmap (Each var set pred) = Each var set $ resolveVarsPredicate varmap pred
resolveVarsPredicate varmap (Which var set pred) = Which var set $ resolveVarsPredicate varmap pred
resolveVarsPredicate varmap (Exists var set pred) = Exists var set $ resolveVarsPredicate varmap pred
resolveVarsPredicate varmap (Equal t1 t2) = Equal (resolveVarsTerm varmap t1) $ resolveVarsTerm varmap t2
resolveVarsPredicate varmap (NotEqual t1 t2) = NotEqual (resolveVarsTerm varmap t1) $ resolveVarsTerm varmap t2
resolveVarsPredicate varmap (AndP t1 t2) = AndP (resolveVarsPredicate varmap t1) $ resolveVarsPredicate varmap t2
resolveVarsPredicate varmap (OrP t1 t2) = OrP (resolveVarsPredicate varmap t1) $ resolveVarsPredicate varmap t2
resolveVarsPredicate varmap (IsSet t1) = IsSet $ resolveVarsTerm varmap t1
resolveVarsPredicate varmap (IsUnSet t1) = IsUnSet $ resolveVarsTerm varmap t1
resolveVarsPredicate varmap (Believes a p) = Believes (Map.findWithDefault a a varmap) $ resolveVarsPredicate varmap p
resolveVarsPredicate  varmap (NotBelieves a p) = NotBelieves (Map.findWithDefault a a varmap) $ resolveVarsPredicate varmap p

resolveVarsTerm :: VarMap -> Term -> Term
resolveVarsTerm varmap (Variable name) | Map.member name varmap = Constant $ Map.findWithDefault name name varmap
                                           | otherwise              = Variable name
resolveVarsTerm varmap (Property name arg) = Property name $ resolveVarsTerm varmap arg
resolveVarsTerm varmap (Property2 name arg1 arg2) = Property2 name (resolveVarsTerm varmap arg1) $ resolveVarsTerm varmap arg2
resolveVarsTerm varmap (PropertyN name args) = PropertyN name $ map (resolveVarsTerm varmap) args
resolveVarsTerm varmap (Constant value) = Constant value

resolveList :: Context -> VarMap -> [String] -> [String]
resolveList ctx vars items | (length items == 1) && (Map.member (head items) (sets ctx)) = Map.findWithDefault [] (head items) $ sets ctx
                           | otherwise = map (\x -> Map.findWithDefault x x vars) items

makeAlternativeActions :: AbstractAction -> Context -> VarMap -> VariableNamer (Action String)
makeAlternativeActions action ctx vars = do
                                  act <- compile' (resolveWith vars) ctx vars
                                  allOptions <- mapM (\assignment -> (compile' (resolveWith $ appearanceMap vars assignment) ctx (appearanceMap vars assignment))) assignments
                                  return  (if null sargs then act else MutualLearn (Composition act $ productAction $  map (appearance allOptions) otheractors) sactors)
                               where
                                 secretargs = getSecretArgs action
                                 sargs = map fst secretargs
                                 ssets = map snd secretargs
                                 sactors = resolveList ctx vars $ getKnowingActors (resolveWith vars) (actors ctx)
                                 otheractors = (actors ctx) \\ sactors
                                 assignments = sequence [getValues ctx setname | setname <- ssets]
                                 resolveWith vmap = resolveVarsAbstract ctx vmap action
                                 appearance opts a = Learn (sumAction opts) a
                                 appearanceMap vmap assignment = (Map.fromList $ zip sargs assignment) `Map.union` vmap
                                 
                                
getSecretArgs :: AbstractAction -> [(String, String)]
getSecretArgs (PublicArgument varname setname action) = getSecretArgs action
getSecretArgs (SecretArgument actors varname setname action) = (varname,setname):getSecretArgs action
getSecretArgs _ = []

getKnowingActors :: AbstractAction -> [String] -> [String]
getKnowingActors (PublicArgument varname setname action) allactors = getKnowingActors action allactors
getKnowingActors (SecretArgument actors varname setname action) allactors = actors `intersect` (getKnowingActors action allactors)
getKnowingActors _ allactors = allactors

compile' :: AbstractAction -> Context -> VarMap -> VariableNamer (Action String)
compile' (PublicArgument varname setname action) context vars = do
                                                                 act <- compile' action context vars
                                                                 return act -- $ MutualLearn act $ actors context
compile' (SecretArgument actors varname setname action) context vars = do
                                                                 act <- compile' action context vars
                                                                 return act --MutualLearn act actors
compile' (Inform actors action) context vars = compileInform action actors context
                                                
compile' (Suspect actors action) context vars = compileSuspect action actors context
  
compile' (Sequence actions) context vars = do
                                            acts <- mapM (\a -> (compile' a context vars)) actions
                                            return $ productAction acts
compile' (Set term value) context vars = do
                                            unset <- compile' (UnSet term) context vars
                                            ifunset <- compileCondition (IsUnSet term) context
                                            (varmap, items) <- resolveProperties term context
                                            (valmap, valitems) <- resolveProperties value context
                                            if (length items) <= 1 then return skip
                                            else do
                                               let allitems = if (length valitems) > 1 then items ++ valitems else items
                                               let fullmap = varmap `Map.union` valmap
                                               let pairs = makePairs allitems
                                               let (eqvar,eqfun) = head pairs
                                               let valvar = head valitems
                                               let otherChecks = tail pairs
                                               let actions = map (\(var, prop) -> resolveTest context $ makeTest var prop) otherChecks
                                               let setaction = makeFlip valvar eqfun
                                               let varorder = sortBy (comparing (\s -> -occurrences s allitems)) $ Map.keys fullmap
                                               let assignments = allValues fullmap context "" 
                                               let setactions1 = makeTests (tail pairs) fullmap varorder context (setaction,flipArgs valvar eqfun) [termName eqvar]
                                               return  $ Composition (Choice unset ifunset) $ setactions1 
compile' (Initialize term value) context vars = do
                                            (varmap, items) <- resolveProperties term context
                                            (valmap, valitems) <- resolveProperties value context
                                            if (length items) <= 1 then return skip
                                            else do
                                               let allitems = if (length valitems) > 1 then items ++ valitems else items
                                               let fullmap = varmap `Map.union` valmap
                                               let pairs = makePairs allitems
                                               let (eqvar,eqfun) = head pairs
                                               let valvar = head valitems
                                               let otherChecks = tail pairs
                                               let actions = map (\(var, prop) -> resolveTest context $ makeTest var prop) otherChecks
                                               let setaction = makeFlip valvar eqfun
                                               let varorder = sortBy (comparing (\s -> -occurrences s allitems)) $ Map.keys fullmap
                                               let assignments = allValues fullmap context "" 
                                               let setactions1 = makeTests (tail pairs) fullmap varorder context (setaction,flipArgs valvar eqfun) [termName eqvar]
                                               return setactions1 
compile' (UnSet term) context vars = do
                                            (varmap,prop) <- resolveProperties term context
                                            if (length prop) == 1 then return skip
                                            else do
                                                let pairs = makePairs prop
                                                let property = prop!!1
                                                let varorder = sortBy (comparing (\s -> -occurrences s prop)) $ Map.keys varmap
                                                let assignments = allValues varmap context ""
                                                let args = (getArgs property) ++ [termName $ head prop]
                                                let flip = Flip $ Predicate (termName term) args
                                                let acts1 = makeTests pairs varmap varorder context (flip,args) []
                                                return acts1
compile' (IfElse pred thenaction elseaction) context vars = do
                                                                thenbranch <- compile' (If pred thenaction) context vars
                                                                elsebranch <- compile' (If (negated pred) elseaction) context vars
                                                                return $ Choice thenbranch elsebranch
compile' (PublicIfElse actors pred thenaction elseaction) context vars = do
                                                                thenbranch <- compile' (If pred thenaction) context vars
                                                                elsebranch <- compile' (If (negated pred) elseaction) context vars
                                                                return $ Choice (MutualLearn thenbranch actors) (MutualLearn elsebranch actors)                                                               
compile' (Public actors inner) context vars = do
                                                 inner' <- compile' inner context vars
                                                 return $ MutualLearn inner' actors
compile' (If pred thenaction) context vars = do
                                                condition <- compileCondition pred context
                                                thenbranch <- compile' thenaction context vars
                                                return $ Composition condition thenbranch
compile' (Precondition pred) context vars = compileCondition pred context
compile' (DEL action) ctx vars = return action
compile' _ _ _ = return skip


occurrences :: String -> [Term] -> Int
occurrences query [] = 0
occurrences query (x:xs) = (occurrences' query x) + (occurrences query xs)

occurrences' :: String -> Term -> Int
occurrences' query (Variable var) | var == query = 1
                                  | otherwise  = 0
occurrences' query (Constant val) = 0
occurrences' query (Property name arg) = occurrences' query arg
occurrences' query (Property2 name arg1 arg2) = (occurrences' query arg1) + (occurrences' query arg2)
occurrences' query (PropertyN name args) = foldl1 (+) $ map (occurrences' query) args



{- 

    IsUnSet f(x): ?f(x, Null) -> product y ? not f(x,y)
    IsSet f(x): exists y ?f(x, y) -> sum y ? f(x,y)
    Set f(x) y: (sum y': (?f(x, y') flip f(x,y'))) flip f(x,y)  
    UnSet f(x): Set f(x) Null -> (sum y': (?f(x, y') flip f(x,y')))
    
-}

makeTests pairs varmap varorder context (inject,injvars) except = resolveTest context $ makeTestsStep pairs varmap varorder context (inject,filter (isPrefixOf "?var") injvars) [] except

makeTestsStep :: [(Term,Term)] -> VarMap -> [VariableName] -> Context -> (Action String,[VariableName]) -> [VariableName] -> [VariableName] -> Action String                                                  
makeTestsStep pairs varmap varorder context (inject,injvars) vars used = result 
                                               where -- split up into the parts that we can fully populate with the variables we have, and those that still have free vars
                                                    (match,others) = partition (filterByVariables vars) pairs
                                                    -- assignments for all the variables we already have
                                                    assignments = allValues1 (Map.filterWithKey (\k _ -> k `elem` vars) varmap) context used
                                                    tests = map (\(var,prop) -> makeTest var prop) match
                                                    -- if we have any matches, we should not reuse the variables we already used inside parentheses
                                                    newused = if (length match) > 0 then vars ++ used else used
                                                    -- how to construct what's inside the parentheses
                                                    doinject = (length (injvars \\ vars) == 0)
                                                    newinject = if doinject then (skip,["?invalid"]) else (inject,injvars)
                                                    injection = if doinject then [inject] else []
                                                    varorderrest = if (length varorder) > 0 then tail varorder else []
                                                    nextvar = head varorder
                                                    subtests = \a -> makeTestsStep others (varmap `Map.union` (Map.fromList a)) varorderrest context newinject (nextvar:vars) newused
                                                    makestep = \a -> productAction $ [(productAction tests)] ++ (if (length varorder) > 0 && (length others > 0) then [subtests a] else []) ++ injection
                                                    steps = if (length assignments) > 0 then [ resolveVars (Map.fromList assignment) $ makestep assignment | assignment <- assignments ]
                                                            else [skip]
                                                    nextCall = if (length varorder) > 0 then makeTestsStep others varmap varorderrest context newinject (nextvar:vars) used else 
                                                               (if (length others) > 0 then trace ("PROBLEM : " ++ (show others)) skip else cleanSum steps)
                                                    result = if (length match) == 0 then cleanProduct (nextCall:injection)
                                                             else cleanSum steps
                                                    

filterByVariables vars (res,Property _ arg) = (matchVar arg vars) && (matchVar res vars)
filterByVariables vars (res,Property2 _ arg1 arg2) = (matchVar arg1 vars) && (matchVar arg2 vars) && (matchVar res vars)
filterByVariables vars (res,PropertyN _ args) = (matchVar res vars) && (and $ map (\a -> matchVar a vars) args)
filterByVariables _ _ = False


matchVar :: Term -> [String] -> Bool
matchVar (Variable name) vars = (take 4 name) /= "?var" || name `elem` vars 
matchVar _ _ = True

resolveProperties :: Term -> Context -> VariableNamer (Map.Map VariableName SetName, [Term])
resolveProperties (Constant c) _ = return (Map.empty, [Constant c])
resolveProperties (Variable v) _ = return (Map.empty, [Variable v])
resolveProperties (Property name arg) ctx = do
                                              newvarname <- makeVar vartype
                                              (innermap,innerseq) <- resolveProperties arg ctx
                                              let rest = if (length innerseq) == 1 then [] else innerseq
                                              let innervar = head innerseq
                                              let newmap = Map.insert newvarname vartype innermap
                                              return (newmap, Variable newvarname:(Property name innervar):rest)
                                           where
                                              vartype = getReturnType ctx name

resolveProperties (Property2 name arg1 arg2) ctx = do
                                                      newvarname <- makeVar vartype
                                                      (innermap1,innerseq1) <- resolveProperties arg1 ctx
                                                      (innermap2,innerseq2) <- resolveProperties arg2 ctx
                                                      let innermap = innermap1 `Map.union` innermap2
                                                      let rest1 = if (length innerseq1) == 1 then [] else innerseq1
                                                      let rest2 = if (length innerseq2) == 1 then [] else innerseq2
                                                      let rest = rest1 ++ rest2
                                                      let innervar1 = head innerseq1
                                                      let innervar2 = head innerseq2
                                                      let newmap = Map.insert newvarname vartype innermap
                                                      return (newmap, Variable newvarname:(Property2 name innervar1 innervar2):rest)
                                                   where
                                                      vartype = getReturnType ctx name
resolveProperties (PropertyN name []) ctx = do
                                                  newvarname <- makeVar vartype
                                                  let newmap = Map.singleton newvarname vartype
                                                  return (newmap, Variable newvarname:[(PropertyN name [])])
                                               where
                                                  vartype = getReturnType ctx name

resolveProperties (PropertyN name args) ctx = do
                                                  newvarname <- makeVar vartype
                                                  props <- mapM (\arg -> resolveProperties arg ctx) args
                                                  let (innermaps,innerseqs) = unzip props
                                                  let rests = map (\innerseq -> if (length innerseq) == 1 then [] else innerseq) innerseqs
                                                  let rest = concat rests
                                                  let innervars = map head innerseqs
                                                  let innermap = foldl1 Map.union innermaps
                                                  let newmap = Map.insert newvarname vartype innermap
                                                  return (newmap, Variable newvarname:(PropertyN name innervars):rest)
                                               where
                                                  vartype = getReturnType ctx name
                                             

makeVar :: String -> VariableNamer String
makeVar vartype = do
                     index <- get
                     modify nextVar
                     return ("?var-" ++ vartype ++ "-temp-" ++ (show index))
                     
negated :: Predicate -> Predicate
negated (Forall var set pred) = Exists var set (negated pred)
negated (Exists var set pred) = Forall var set (negated pred)
negated (Each var set pred) = Each var set (negated pred)
negated (Which var set pred) = Which var set (negated pred)
negated (AndP a b) = OrP (negated a) (negated b)
negated (OrP a b) = AndP (negated a) (negated b)
negated (Equal t1 t2) = NotEqual t1 t2
negated (NotEqual t1 t2) = Equal t1 t2
negated (IsSet t) = (IsUnSet t)
negated (IsUnSet t) = (IsSet t)
negated (Believes a p) = (NotBelieves a p)
negated (NotBelieves a p) = (Believes a p)
                     
                     
compileCondition :: Predicate -> Context -> VariableNamer (Action String)
compileCondition (Forall var set pred) context  = do
                                                      acts <- mapM (\item -> compileCondition (resolveVarsPredicate (Map.singleton var item) pred) context) items
                                                      return $ cleanProduct acts
                                                      where
                                                          items = Map.findWithDefault [] set (sets context)
compileCondition (Exists var set pred) context  = do
                                                      inform <- compileCondition pred context
                                                      let acts = map (\item -> (resolveVars (Map.singleton var item) inform)) items
                                                      return $ cleanSum acts
                                                      where
                                                          items = Map.findWithDefault [] set (sets context)
compileCondition (Equal t1 t2) context  = do
                                                (map1,items1) <- resolveProperties t1 context
                                                (map2,items2) <- resolveProperties t2 context
                                                let list1 = if (length items2) == 1 then items2 else items1
                                                let list2 = if (length items2) == 1 then (head items2):(tail items1) else (head items1):(tail items2)
                                                let unused = termName $ if (length items2) == 1 then (head items1) else (head items2)
                                                if (length list2) == 1 then return skip
                                                else do
                                                    let pairs1 = makePairs list1
                                                    let pairs2 = makePairs list2
                                                    let actions1 = map (\(var,prop) -> makeTest var prop) pairs1
                                                    let actions2 = map (\(var,prop) -> makeTest var prop) pairs2
                                                    let fullmap = map1 `Map.union` map2
                                                    let assignments = allValues fullmap context unused
                                                    let allTests = [cleanProduct $ map (resolveTest context) $ map (resolveVars (Map.fromList assignment)) $ actions1 ++ actions2 | assignment <- assignments]
                                                    return $ cleanSum allTests
compileCondition (NotEqual t1 t2) context  = do 
                                                (map1,items1) <- resolveProperties t1 context
                                                (map2,items2) <- resolveProperties t2 context
                                                let list1 = if (length items2) == 1 then items2 else items1
                                                let list2 = if (length items2) == 1 then (head items2):(tail items1) else (head items1):(tail items2)
                                                let unused = termName $ if (length items2) == 1 then (head items1) else (head items2)
                                                if (length list2) == 1 then return skip
                                                else do
                                                    let pairs1 = makePairs list1
                                                    let pairs2 = makePairs list2
                                                    let (eqvar,eqfun) = head pairs2
                                                    let otherChecks = tail pairs2
                                                    let actions1 = map (\(var,prop) -> makeTest var prop) pairs1
                                                    let actions2 = map (\(var,prop) -> makeTest var prop) otherChecks
                                                    let unequalityCheck = makeNegatedTest eqvar eqfun
                                                    let fullmap = map1 `Map.union` map2
                                                    let assignments = allValues fullmap context unused
                                                    let allTests = [ cleanProduct $ map (resolveTest context) $ map (resolveVars (Map.fromList assignment)) $ actions1 ++ [unequalityCheck] ++ actions2 | assignment <- assignments]
                                                    return $ cleanSum allTests
compileCondition (IsSet term) context = do
                                           (varmap, items) <- resolveProperties term context
                                           if (length items) <= 1 then return skip
                                           else do
                                               let pairs = makePairs items
                                               let actions = map (\(var, prop) -> makeTest var prop) pairs
                                               let assignments = allValues varmap context ""
                                               let tests = [resolveVars (Map.fromList assignment) $ productAction actions | assignment <- assignments]
                                               return $ cleanSum tests
compileCondition (IsUnSet term) context = do
                                           (varmap, items) <- resolveProperties term context
                                           if (length items) <= 1 then return skip
                                           else do
                                               let pairs = makePairs items
                                               let (eqvar,eqfun) = head pairs
                                               let otherChecks = tail pairs
                                               let actions = map (\(var, prop) -> makeTest var prop) otherChecks
                                               let unequalityCheck = makeNegatedTest eqvar eqfun
                                               let assignments = allValues varmap context ""
                                               let tests = filter (isNecessary) [resolveTest context $ resolveVars (Map.fromList assignment) $ productAction (unequalityCheck:actions) | assignment <- assignments]
                                               return $ productAction tests
compileCondition (AndP p1 p2) context  = do
                                             sub1 <- compileCondition p1 context 
                                             sub2 <- compileCondition p2 context 
                                             return $ cleanComposition sub1 sub2 
compileCondition (OrP p1 p2) context  = do
                                             sub1 <- compileCondition p1 context 
                                             sub2 <- compileCondition p2 context 
                                             return $ cleanChoice sub1 sub2 
compileCondition (Believes a p) context  = do
                                             sub1 <- compileCondition p context 
                                             return $ toKnowledgeTests a sub1
compileCondition (NotBelieves a p) context  = do
                                             sub1 <- compileCondition p context 
                                             return $ toUnKnowledgeTests a sub1
                                             
toKnowledgeTests :: Actor -> Action String -> Action String
toKnowledgeTests act (Test p) = Test $ Know act p
toKnowledgeTests act (Choice a b) = Choice (toKnowledgeTests act a) $ toKnowledgeTests act b
toKnowledgeTests act (Composition a b) = Composition (toKnowledgeTests act a) $ toKnowledgeTests act b
toKnowledgeTests act (Learn a who) = Learn (toKnowledgeTests act a) who
toKnowledgeTests act (MutualLearn a who) = MutualLearn (toKnowledgeTests act a) who
toKnowledgeTests _ a = a

toUnKnowledgeTests :: Actor -> Action String -> Action String
toUnKnowledgeTests act (Test p) = Test $ Not $ Know act p
toUnKnowledgeTests act (Choice a b) = Composition (toUnKnowledgeTests act a) $ toUnKnowledgeTests act b
toUnKnowledgeTests act (Composition a b) = Choice (toUnKnowledgeTests act a) $ toUnKnowledgeTests act b
toUnKnowledgeTests act (Learn a who) = Learn (toUnKnowledgeTests act a) who
toUnKnowledgeTests act (MutualLearn a who) = MutualLearn (toUnKnowledgeTests act a) who
toUnKnowledgeTests _ a = a

isNecessary :: Action String -> Bool
isNecessary p | p == testtrue = False
              | p == testfalse = False
              | otherwise = True



              
compileInform :: Predicate -> [Actor] -> Context -> VariableNamer (Action String)
compileInform = compileLearn MutualLearn

compileSuspect :: Predicate -> [Actor] -> Context -> VariableNamer (Action String)
compileSuspect = compileLearn makeLearn

makeLearn :: Action String -> [String] -> Action String
makeLearn act actors = productAction [Learn act a | a <- actors]

compileLearn :: (Action String -> [String] -> Action String) -> Predicate -> [Actor] -> Context -> VariableNamer (Action String)
compileLearn cns (Each var set pred) actors context  = do
                                                              inform <- compileLearn' pred context
                                                              let resolve = \item -> resolveVarsPredicate (Map.singleton var item) pred
                                                              let resolved = map (resolve) items
                                                              let nresolve = \item -> resolveVarsPredicate (Map.singleton var item) $ negated pred
                                                              let nresolved = map (nresolve) items
                                                              let makeInform = \p -> compileLearn cns p actors context
                                                              acts <- mapM makeInform resolved
                                                              nacts <- mapM makeInform nresolved
                                                              let actions = map (\(a,b)-> Choice (cns a actors) (cns b actors)) $ zip acts nacts
                                                              return $ cleanProduct actions
                                                              where
                                                                  items = Map.findWithDefault [] set (sets context)
                                                                  
compileLearn cns (Which var set pred) actors context  = do
                                                              inform <- compileLearn' pred context
                                                              let resolve = \item -> resolveVarsPredicate (Map.singleton var item) pred
                                                              let resolved = map (resolve) items
                                                              let makeInform = \p -> compileLearn' p context
                                                              acts <- mapM makeInform resolved
                                                              return $ cleanSum $ map (\a -> cns a actors) acts
                                                              where
                                                                  items = Map.findWithDefault [] set (sets context)
                                                                  

                                                                  
compileLearn cns cond actors context = do
                                          action <- compileLearn' cond context
                                          return $ cns action actors
                                          

compileLearn' (Forall var set pred) context  = do
                                                              inform <- compileLearn' pred context
                                                              let resolve = \item -> resolveVarsPredicate (Map.singleton var item) pred
                                                              let resolved = map (resolve) items
                                                              let makeInform = \p -> compileLearn' p context
                                                              acts <- mapM makeInform resolved
                                                              return $ cleanProduct acts
                                                              where
                                                                  items = Map.findWithDefault [] set (sets context)

compileLearn' (Exists var set pred) context  = do
                                                              inform <- compileLearn' pred context
                                                              let resolve = \item -> resolveVarsPredicate (Map.singleton var item) pred
                                                              let resolved = map (resolve) items
                                                              let makeInform = \p -> compileLearn' p context
                                                              acts <- mapM makeInform resolved
                                                              return $ cleanSum acts
                                                              where
                                                                  items = Map.findWithDefault [] set (sets context)


compileLearn' (AndP p1 p2) context  = do
                                                     sub1 <- compileLearn' p1 context 
                                                     sub2 <- compileLearn' p2 context 
                                                     return $ Composition sub1 sub2 
compileLearn' (Believes a p) context  = do
                                                     sub1 <- compileLearn' p context 
                                                     return $ toKnowledgeTests a sub1
compileLearn' (NotBelieves a p) context  = do
                                                     sub1 <- compileLearn' p context 
                                                     return $ toUnKnowledgeTests a sub1
compileLearn' p ctx =  compileCondition p ctx


makePairs :: [a] -> [(a,a)]
makePairs [] = []
makePairs [x] = []
makePairs (x1:x2:xs) = (x1,x2):(makePairs xs)

allValues :: Map.Map VariableName SetName -> Context -> VariableName -> [[(VariableName,ConstantValue)]]
allValues vars ctx except = sequence $ [map (\val -> (varname, val)) $ getValues ctx vartype | (varname,vartype) <- (Map.assocs vars), varname /= except]

allValues1 :: Map.Map VariableName SetName -> Context -> [VariableName] -> [[(VariableName,ConstantValue)]]
allValues1 vars ctx except = sequence $ [map (\val -> (varname, val)) $ getValues ctx vartype | (varname,vartype) <- (Map.assocs vars), varname `notElem` except]
                               

makeTest :: Term -> Term -> Action String
makeTest var (Property name arg) = Test $ Atom $ Predicate name $ map termName [arg, var]
makeTest var (Property2 name arg1 arg2) = Test $ Atom $ Predicate name $ map termName [arg1, arg2, var]
makeTest var (PropertyN name args) = Test $ Atom $ Predicate name $ map termName $ args ++ [var]
makeTest var _ = skip

makeNegatedTest :: Term -> Term -> Action String
makeNegatedTest var (Property name arg) = Test $ Not $ Atom $ Predicate name $ map termName [arg, var]
makeNegatedTest var (Property2 name arg1 arg2) = Test $ Not $ Atom $ Predicate name $ map termName [arg1, arg2, var]
makeNegatedTest var (PropertyN name args) = Test $ Not $ Atom $ Predicate name $ map termName $ args ++ [var]
makeNegatedTest var _ = skip

makeFlip :: Term -> Term -> Action String
makeFlip var (Property name arg) = Flip $ Predicate name $ map termName [arg, var]
makeFlip var (Property2 name arg1 arg2) = Flip $ Predicate name $ map termName [arg1, arg2, var]
makeFlip var (PropertyN name args) = Flip $ Predicate name $ map termName $ args ++ [var]
makeFlip var _ = skip

flipArgs :: Term -> Term -> [String]
flipArgs var (Property name arg) = map termName [arg, var]
flipArgs var (Property2 name arg1 arg2) = map termName [arg1, arg2, var]
flipArgs var (PropertyN name args) = map termName $ args ++ [var]
flipArgs var _ = []


resolvePredicate :: String -> Term -> Term -> Maybe (AtProp String) -> Action String
resolvePredicate name t1 t2 (Just p) = Test $ Atom $ p
resolvePredicate _ _ _ _ = skip


resolveVars :: VarMap -> Action String -> Action String
resolveVars vars (Test prop) = Test $ resolveVarsProp vars prop
resolveVars vars (Composition a1 a2) = cleanComposition (resolveVars vars a1) (resolveVars vars a2)
resolveVars vars (Choice a1 a2) = cleanChoice (resolveVars vars a1) (resolveVars vars a2)
resolveVars vars (Learn a act) = Learn (resolveVars vars a) act
resolveVars vars (MutualLearn a acts) = MutualLearn (resolveVars vars a) acts
resolveVars vars (Flip prop) = Flip $ resolveVarsAtProp vars prop

resolveVarsProp :: VarMap -> Proposition String -> Proposition String
resolveVarsProp vars (Atom prop) = Atom $ resolveVarsAtProp vars prop
resolveVarsProp vars (Not prop) = Not $ resolveVarsProp vars prop
resolveVarsProp vars (And p1 p2) = And (resolveVarsProp vars p1) (resolveVarsProp vars p2)
resolveVarsProp vars (Apply act prop) = Apply (resolveVars vars act) (resolveVarsProp vars prop)
resolveVarsProp vars (Know act prop) = Know act $ resolveVarsProp vars prop
resolveVarsProp vars (MutualKnowledge acts prop) = MutualKnowledge acts $ resolveVarsProp vars prop

resolveVarsAtProp :: VarMap -> AtProp String -> AtProp String
resolveVarsAtProp vars (Predicate name args) = Predicate (replace vars name) $ map (replace vars) args


resolveTest :: Context -> Action String -> Action String
resolveTest ctx act = resolveStatic ctx $ resolveRestricted ctx act


resolveStatic :: Context -> Action String -> Action String
resolveStatic ctx act = resolveStatic' (static_predicates ctx) act

resolveStatic' :: Map.Map String [[String]] -> Action String -> Action String
resolveStatic' statics (Test prop) = resolveStaticTest statics prop
resolveStatic' statics (Composition a1 a2) = cleanComposition (resolveStatic' statics a1) (resolveStatic' statics a2)
resolveStatic' statics (Choice a1 a2) = cleanChoice (resolveStatic' statics a1) (resolveStatic' statics a2)
resolveStatic' statics (Learn a act) = Learn (resolveStatic' statics a) act
resolveStatic' statics (MutualLearn a acts) = MutualLearn (resolveStatic' statics a) acts
resolveStatic' statics (Flip prop) = Flip prop

resolveStaticTest :: Map.Map String [[String]] -> Proposition String -> Action String
resolveStaticTest statics (Atom (Predicate pred args)) | Map.member pred statics = if (args `elem` (Map.findWithDefault [] pred statics)) then testtrue else testfalse
                                                       | otherwise               = Test $ Atom (Predicate pred args)
resolveStaticTest statics (Not (Atom (Predicate pred args))) | Map.member pred statics = if (args `elem` (Map.findWithDefault [] pred statics)) then testfalse else testtrue
                                                             | otherwise               = Test $ Not $ Atom (Predicate pred args)
resolveStaticTest _ test = Test test




resolveRestricted :: Context -> Action String -> Action String
resolveRestricted ctx act = resolveRestricted' (restricted_predicates ctx) act

resolveRestricted' :: Map.Map String [[String]] -> Action String -> Action String
resolveRestricted' statics (Test prop) = resolveRestrictedTest statics prop
resolveRestricted' statics (Composition a1 a2) = cleanComposition (resolveRestricted' statics a1) (resolveRestricted' statics a2)
resolveRestricted' statics (Choice a1 a2) = cleanChoice (resolveRestricted' statics a1) (resolveRestricted' statics a2)
resolveRestricted' statics (Learn a act) = Learn (resolveRestricted' statics a) act
resolveRestricted' statics (MutualLearn a acts) = MutualLearn (resolveRestricted' statics a) acts
resolveRestricted' statics (Flip prop) = Flip prop

resolveRestrictedTest :: Map.Map String [[String]] -> Proposition String -> Action String
resolveRestrictedTest restricteds (Atom (Predicate pred args)) | Map.member pred restricteds = if (args `elem` (Map.findWithDefault [] pred restricteds)) then Test (Atom (Predicate pred args)) else testfalse
                                                               | otherwise               = Test $ Atom (Predicate pred args)
resolveRestrictedTest restricteds (Not (Atom (Predicate pred args))) | Map.member pred restricteds = if (args `notElem` (Map.findWithDefault [] pred restricteds)) then testtrue else Test $ Not $ Atom (Predicate pred args)
                                                                     | otherwise               = Test $ Not $ Atom (Predicate pred args)
resolveRestrictedTest _ test = Test test


replace :: VarMap -> String -> String
replace vars var = Map.findWithDefault var var vars

