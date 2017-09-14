module AbstractActionParser where

import Text.ParserCombinators.Parsec
import Text.Parsec.Expr
import AbstractActions
import Baltag hiding (choice)
import BaseTypes
import Data.List
import Control.Monad
import Control.Applicative hiding ((<|>),many,optional)

buildPrattParser table termP = parser precs where

  precs = reverse table

  prefixP = choice prefixPs <|> termP where
    prefixPs = do
      precsR@(ops:_) <- tails precs 
      Prefix opP <- ops
      return $ opP <*> parser precsR

  infixP precs lhs = choice infixPs <|> pure lhs where
    infixPs = do
      precsR@(ops:precsL) <- tails precs
      op <- ops
      p <- case op of
        Infix opP assoc -> do
          let p precs = opP <*> pure lhs <*> parser precs
          return $ case assoc of
            AssocNone  -> error "Non associative operators are not supported"
            AssocLeft  -> p precsL
            AssocRight -> p precsR
        Postfix opP ->
          return $ opP <*> pure lhs
        Prefix _ -> mzero
      return $ p >>= infixP precs

  parser precs = prefixP >>= infixP precs

identifier = do 
                result <- many1 (letter <|> digit)
                many space
                return result
                
symbol s = do
               string s
               many space
               return s
               
symbol1 s = do
               string s
               many1 space
               return s

parens p = do
              symbol "("
              result <- p
              symbol ")"
              return result
              
brackets p = do
              symbol "["
              result <- p
              symbol "]"
              return result


parseArg = try parseSecretArg <|> parsePublicArg

parseSecretArg = do
              arg <- identifier
              actors <- parens (identifier `sepBy` (symbol ","))
              symbol ":"
              argtype <- identifier
              return (arg, argtype, actors)

parsePublicArg = do
              arg <- identifier
              symbol ":"
              argtype <- identifier
              return (arg, argtype, [])

abstractActionHeader = 
                 do 
                    name <- identifier
                    args <- parens $ parseArg `sepBy` (symbol ",")
                    many space
                    innerAction <- abstractAction
                    many space
                    return $ (name,toArgs args $ innerAction)
                    
abstractAction = do
                    many space
                    act <- actualAction
                    many space
                    return act

actualAction = try parseBaltag <|> try parseInform <|> try parseSuspect <|> try parseSequence <|> try parsePublic <|> try parseIfElse <|> try parseIf <|> try parsePrecondition <|> try parseInit <|> try parseUnSet <|> parseSet

parseBaltag = do
                symbol "<"
                action <- parseDELAction
                symbol ">"
                return $ DEL action
                
parseDELAction = try parseFlip <|> try parseDELTest <|> try parseLearn <|> try parseMutualLearn <|> try parseComposition <|> try parseChoice <|> parens parseDELAction

parseFlip = do
               symbol1 "flip"
               pred <- parsePureProperty
               return $ Flip pred
               
parseDELTest = do
               symbol "?"
               prop <- parseProposition
               return $ Test prop
               
parseComposition = do
               a <- parseDELAction
               symbol "."
               b <- parseDELAction
               return $ Composition a b
               
parseChoice = do
               a <- parseDELAction
               symbol "+"
               b <- parseDELAction
               return $ Choice a b
               
parseLearn = do
               symbol "("
               act <- parseDELAction
               symbol ")^"
               actor <- many1 (letter <|> digit) 
               return $ Learn act actor
               
parseMutualLearn = do
               symbol "("
               act <- parseDELAction
               symbol ")*"
               actors <- parens $ (many1 (letter <|> digit)) `sepBy` (symbol ",")
               return $ MutualLearn act actors

parseProposition    = buildPrattParser optable parseAtom1
optable = [ [ Prefix parseNot ]  -- highest precedence first
          , [ Prefix parseApply ]
          , [ Infix parseAnd AssocLeft ]
          , [ Infix parseOr AssocLeft ]
          , [ Prefix parseKnow ]
          , [ Prefix parseMutualKnow ]
          ]

parseAtom1 = try (parens parseAtom1) <|> parseAtom
          
parseAtom = do
              prop <- parsePureProperty
              return $ Atom prop

parseNot = do
              symbol1 "not"
              return Not
              
parseKnow = do
              symbol "[]"
              actor <- many1 (letter <|> digit) 
              many1 space
              return $ Know actor
              
parseMutualKnow = do
              symbol "[]*"
              actors <- parens $ (many1 (letter <|> digit)) `sepBy` (symbol ",")
              many1 space
              return $ MutualKnowledge actors
              
parseApply = do
               action <- brackets parseDELAction
               many space
               return $ Apply action
               
parseAnd = do
               symbol1 "and"
               return $ And 
               
parseOr = do
               symbol1 "or"
               return $ Or 

parseInform = do 
                (try $ symbol "tell") <|> symbol "learn"
                actors <- parens $ identifier `sepBy` (symbol ",")
                symbol ":"
                pred <- parsePredicate
                return $ Inform actors pred
                
parseSuspect = do 
                symbol "suspect"
                actors <- parens $ identifier `sepBy` (symbol ",")
                symbol ":"
                pred <- parsePredicate
                return $ Suspect actors pred

parseSequence = do
                   symbol "{"
                   actions <- abstractAction `sepBy` (symbol ";")
                   optional $ symbol ";"                  
                   symbol "}"
                   let result = (if (length actions) == 1 then (head actions) else (Sequence actions))
                   return result
                   
parseIfElse = do
              symbol "if"
              condition <- parens parsePredicate
              many space
              ifbranch <- abstractAction
              many space
              symbol "else"
              elsebranch <- abstractAction
              return $ IfElse condition ifbranch elsebranch
                   
parseIf = do
              symbol "if"
              condition <- parens parsePredicate
              many space
              ifbranch <- abstractAction
              return $ If condition ifbranch
              
parsePrecondition = do
              symbol "precondition"
              condition <- parsePredicate
              return $ Precondition condition
              
setName = do
            result <- identifier
            return ["set: " ++ result]

makePublic actors (IfElse c t e) = PublicIfElse actors c t e
makePublic actors inner = Public actors inner
            
parsePublic = do
              symbol "public"
              actors <- (try $ parens $ identifier `sepBy` (symbol ",")) <|> setName
              inner <- try parseIfElse <|> abstractAction
              return $ makePublic actors inner
           
parsePublicIf = do
              symbol "publicif"
              actors <- setName -- 
              condition <- parens parsePredicate
              many space
              ifbranch <- abstractAction
              many space
              symbol "else"
              elsebranch <- abstractAction
              return $ PublicIfElse actors condition ifbranch elsebranch
              
parseInit = do
              symbol "init "
              property <- parseProperty
              many space
              symbol "="
              value <- parseValue
              return $ Initialize property value
              
parseSet = do
              property <- parseProperty
              many space
              symbol "="
              value <- parseValue
              return $ Set property value
              
parseUnSet = do
              property <- parseProperty
              many space
              symbol "="
              symbol "Null"
              return $ UnSet property
              

parsePredicate    = buildPrattParser predoptable parseBasePredicate
predoptable = [ [ Infix parseAndP AssocLeft ]
          , [ Infix parseOrP AssocLeft ]
          , [ Prefix parseBelieve ]
          , [ Prefix parseNotBelieve ]
          , [ Prefix parseQuantifier ]
          ]
          
parseBelieve = do
                   try (symbol1 "B") <|> try (symbol1 "[]")
                   actors <- parens identifier
                   symbol ":"
                   return $ Believes actors
                   
parseNotBelieve = do 
                   try $ symbol1 "not"
                   try (symbol "B") <|> try (symbol "[]")
                   actors <- parens identifier
                   symbol ":"
                   return $ Believes actors
                   
toQuant "Forall" = Forall
toQuant "Exists" = Exists
toQuant "Each" = Each
toQuant "Which" = Which
                    
parseQuantifier = do
                    q <- try (symbol "Each") <|> try (symbol "Forall") <|> try (symbol "Exists") <|> try (symbol "Which")
                    var <- identifier
                    try $ symbol "in"
                    set <- identifier
                    try $ symbol ":"
                    return $ (toQuant q) var set
                   
parseAndP = do
               try $ symbol1 "and"
               return $ AndP
               
parseOrP = do
               try $ symbol1 "or"
               return $ OrP
          
parseBasePredicate = try (parens parsePredicate) <|> try parseIsSet <|> try parseIsUnSet <|> try parseEqual <|> parseNotEqual <?> "Base Comparison"

parseIsSet = do
                property <- parseProperty
                many space
                symbol "!="
                symbol "Null"
                return $ IsUnSet property
                
parseIsUnSet = do
                property <- parseProperty
                many space
                symbol "=="
                symbol "Null"
                return $ IsUnSet property
                
parseEqual = do
                a <- parseProperty
                many space
                symbol "=="
                b <- parseValue
                return $ Equal a b 
                
parseNotEqual = do
                    a <- parseProperty
                    many space
                    symbol "!="
                    b <- parseValue
                    return $ NotEqual a b 
                    

                    
toProp name args | length args == 1 = Property name $ head args
                 | length args == 2 = Property2 name (head args) $ head $ tail args
                 | otherwise        = PropertyN name args
                    
parseProperty = do
                    name <- many1 (letter <|> digit)
                    args <- parens $ parseValue `sepBy` (symbol ",")
                    return $ toProp name args

                   
parseValue = try parseProperty <|> parsePureValue

parsePureValue = do
                    value <- many1 (letter <|> digit)
                    return $ Variable value
                    
                    
parsePureProperty = do
                        name <- many1 (letter <|> digit)
                        args <- parens $ (many1 (letter <|> digit)) `sepBy` (symbol ",")
                        return $ Predicate name args
                
                    

toArgs :: [(String,String,[String])] -> AbstractAction -> AbstractAction
toArgs [] action = action
toArgs ((argname,argtype,[]):args) action = PublicArgument argname argtype $ toArgs args action
toArgs ((argname,argtype,actors):args) action = SecretArgument actors argname argtype $ toArgs args action


parseAction :: String -> Either ParseError (String,AbstractAction)
parseAction text = parse abstractActionHeader "(unknown)" text

