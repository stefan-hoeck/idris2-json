module JSON.Parser

import JSON.Lexer
import Data.String
import Generics.Derive

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          JSON
--------------------------------------------------------------------------------

public export
data JSON : Type where
  JNull   : JSON
  JNumber : Double -> JSON
  JBool   : Bool   -> JSON
  JString : String -> JSON
  JArray  : List JSON -> JSON
  JObject : List (String, JSON) -> JSON

showValue : SnocList String -> JSON -> SnocList String

showPair : SnocList String -> (String,JSON) -> SnocList String

showArray : SnocList String -> List JSON -> SnocList String

showObject : SnocList String -> List (String,JSON) -> SnocList String

showValue ss JNull              = ss :< "null"
showValue ss (JNumber dbl)      = ss :< show dbl
showValue ss (JBool True)       = ss :< "true"
showValue ss (JBool False)      = ss :< "false"
showValue ss (JString str)      = ss :< encode str
showValue ss (JArray [])        = ss :< "[]"
showValue ss (JArray $ h :: t)  =
  let ss' = showValue (ss :< "[") h
   in showArray ss' t
showValue ss (JObject [])       = ss :< "{}"
showValue ss (JObject $ h :: t) =
  let ss' = showPair (ss :< "{") h
   in showObject ss' t

showPair ss (s,v) = showValue (ss :< encode s :< ":") v

showArray ss [] = ss :< "]"
showArray ss (h :: t) =
  let ss' = showValue (ss :< ",") h in showArray ss' t

showObject ss [] = ss :< "}"
showObject ss (h :: t) =
  let ss' = showPair (ss :< ",") h in showObject ss' t

showImpl : JSON -> String
showImpl v = fastConcat $ showValue Lin v <>> Nil

export %inline
Show JSON where
  show = showImpl

public export
size : JSON -> Nat
size JNull         = 1
size (JNumber dbl) = 1
size (JBool x)     = 1
size (JString str) = 1
size (JArray xs)   = assert_total $ sum $ map size xs
size (JObject xs)  = assert_total $ sum $ map (size . snd) xs

public export
depth : JSON -> Nat
depth JNull         = 1
depth (JNumber dbl) = 1
depth (JBool x)     = 1
depth (JString str) = 1
depth (JArray xs)   = 1 + assert_total (foldl (\n,j => max n $ depth j) 0 xs)
depth (JObject xs)  =
  1 + assert_total (foldl (\n,p => max n $ depth (snd p)) 0 xs)

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

public export
data ParseErr : Type where
  LErr             : Bounds -> LexErr -> ParseErr
  UnmatchedBracket : Bounds -> ParseErr
  UnmatchedBrace   : Bounds -> ParseErr
  Unexpected       : Token  -> ParseErr
  EOI              : ParseErr

%runElab derive "ParseErr" [Generic,Meta,Show,Eq]

value  :  List Token -> Either ParseErr (List Token, JSON)

array  :  Bounds -- opening bracket
       -> SnocList JSON
       -> List Token
       -> Either ParseErr (List Token, JSON)

object :  Bounds
       -> SnocList (String, JSON)
       -> List Token
       -> Either ParseErr (List Token, JSON)

value []        = Left EOI
value (t :: ts) = case t of
  TBracketO x  => array x Lin ts
  TBraceO x    => object x Lin ts
  TBool _ b    => Right (ts, JBool b)
  TNull _      => Right (ts, JNull)
  TNum _ d     => Right (ts, JNumber d)
  TStr _ s     => Right (ts, JString s)
  TErr x err   => Left (LErr x err)
  _            => Left (Unexpected t)

array b sv []                  = Left (UnmatchedBracket b)
array b sv (TBracketC _ :: xs) = Right (xs, JArray $ sv <>> Nil)
array b sv xs                  =
  let Right (TComma _ :: xs2, v) := value xs
        | Right (TBracketC _ :: xs2, v) => Right (xs2, JArray $ sv <>> [v])
        | Right (x :: xs2, v)           => Left (Unexpected x)
        | Right ([],_)                  => Left (UnmatchedBracket b)
        | Left  EOI                     => Left (UnmatchedBracket b)
        | Left  err                     => Left err
   in array b (sv :< v) (assert_smaller xs xs2)

object b sv []                           = Left (UnmatchedBrace b)
object b sv (TBraceC _ :: xs)            = Right (xs, JObject $ sv <>> Nil)
object b sv (TStr _ s :: TColon _ :: xs) =
  let Right (TComma _ :: xs2, v) := value xs
        | Right (TBraceC _ :: xs2, v) => Right (xs2, JObject $ sv <>> [(s,v)])
        | Right (x :: xs2, v)         => Left (Unexpected x)
        | Right ([],_)                => Left (UnmatchedBracket b)
        | Left  EOI                   => Left (UnmatchedBracket b)
        | Left  err                   => Left err
   in object b (sv :< (s,v)) (assert_smaller xs xs2)
object b sv (TStr _ s :: x :: xs)        = Left (Unexpected x)
object b sv (TStr _ s :: [])             = Left (UnmatchedBracket b)
object b sv (x :: xs)                    = Left (Unexpected x)

export
parseErrLine : (line : Nat) -> String -> Either ParseErr JSON
parseErrLine l s = case value (lexJSONLine l s) of
  Right ([], v)     => Right v
  Right (x :: _, v) => Left (Unexpected x)
  Left err      => Left err

export %inline
parseErr : String -> Either ParseErr JSON
parseErr = parseErrLine 1

export
parseMaybe : String -> Maybe JSON
parseMaybe s = case value (lexJSON s) of
  Right ([], v) => Just v
  _             => Nothing

--------------------------------------------------------------------------------
--          Pretty Printed Errors
--------------------------------------------------------------------------------

lexErr : LexErr -> String
lexErr MissingQuote = "missing closing quote"
lexErr InvalidLit   = "invalid literal"
lexErr InvalidEsc   = "invalid escape sequence"
lexErr InvalidChar  = "invalid character"

tokName : Token -> String
tokName (TBracketO x) = "opening bracket"
tokName (TBracketC x) = "closing bracket"
tokName (TBraceO x)   = "opening brace"
tokName (TBraceC x)   = "closing brace"
tokName (TComma x)    = "comma"
tokName (TColon x)    = "colon"
tokName (TNull x)     = "\"null\""
tokName (TBool x b)   = "boolean literal"
tokName (TNum x dbl)  = "double literal"
tokName (TStr x str)  = "string literal"
tokName (TErr x y)    = "error : \{lexErr y}"

errLines : String -> Bounds -> String -> String
errLines str bs tok = unlines $ tokenLines (lines str) bs tok

export
prettyErr : String -> ParseErr -> String
prettyErr s (LErr x y)           = errLines s x $ lexErr y
prettyErr s (UnmatchedBracket x) = errLines s x "unmatched bracket"
prettyErr s (UnmatchedBrace x)   = errLines s x "unmatched brace"
prettyErr s (Unexpected x)       = errLines s (bounds x) "unexpected \{tokName x}"
prettyErr s EOI                  = "unexpected end of input"
