module JSON.Parser

import Data.List1
import Data.String
import public Text.Parse.Manual
import Derive.Prelude

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          String Encoding
--------------------------------------------------------------------------------

hexChar : Integer -> Char
hexChar 0 = '0'
hexChar 1 = '1'
hexChar 2 = '2'
hexChar 3 = '3'
hexChar 4 = '4'
hexChar 5 = '5'
hexChar 6 = '6'
hexChar 7 = '7'
hexChar 8 = '8'
hexChar 9 = '9'
hexChar 10 = 'a'
hexChar 11 = 'b'
hexChar 12 = 'c'
hexChar 13 = 'd'
hexChar 14 = 'e'
hexChar _  = 'f'

export
encode : String -> String
encode = go (Lin :< '"') . unpack
  where go : SnocList Char -> List Char -> String
        go sc []          = pack (sc <>> ['"'])
        go sc ('"' :: t)  = go (sc :< '\\' :< '"') t
        go sc ('\n' :: t) = go (sc :< '\\' :< 'n') t
        go sc ('\f' :: t) = go (sc :< '\\' :< 'f') t
        go sc ('\b' :: t) = go (sc :< '\\' :< 'b') t
        go sc ('\r' :: t) = go (sc :< '\\' :< 'r') t
        go sc ('\t' :: t) = go (sc :< '\\' :< 't') t
        go sc ('\\' :: t) = go (sc :< '\\' :< '\\') t
        go sc ('/'  :: t) = go (sc :< '\\' :< '/') t
        go sc (c    :: t) =
          let x := the Integer $ cast c
           in if x >= 0x20
                then go (sc :< c) t
                else let d1 := hexChar $ x `div` 0x1000
                         d2 := hexChar $ (x `mod` 0x1000) `div` 0x100
                         d3 := hexChar $ (x `mod` 0x100)  `div` 0x10
                         d4 := hexChar $ x `mod` 0x10
                      in go (sc :< '\\' :< 'u' :< d1 :< d2 :< d3 :< d4) t

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

%runElab derive "JSON" [Eq]

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
showImpl v = concat $ showValue Lin v <>> Nil

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
--          Lexer
--------------------------------------------------------------------------------

public export
data JSToken : Type where
  Symbol   : Char -> JSToken
  Lit      : JSON -> JSToken

%runElab derive "JSToken" [Show,Eq]

%inline
fromChar : Char -> JSToken
fromChar = Symbol

export
Interpolation JSToken where
  interpolate (Symbol c) = show c
  interpolate (Lit x)  = "'\{show x}'"

public export
data JSErr : Type where
  ExpectedString  : JSErr
  InvalidEscape   : JSErr

%runElab derive "JSErr" [Show,Eq]

export
Interpolation JSErr where
  interpolate ExpectedString  = "Expected string literal"
  interpolate InvalidEscape   = "Invalid escape sequence"

public export %tcinline
0 ParseErr : Type
ParseErr = ParseError JSToken JSErr

strLit : SnocList Char -> JSToken
strLit = Lit . JString . cast

str : SnocList Char -> AutoTok Char JSToken
str sc ('\\' :: c  :: xs) = case c of
  '"'  => str (sc :< '"') xs
  'n'  => str (sc :< '\n') xs
  'f'  => str (sc :< '\f') xs
  'b'  => str (sc :< '\b') xs
  'r'  => str (sc :< '\r') xs
  't'  => str (sc :< '\t') xs
  '\\' => str (sc :< '\\') xs
  '/'  => str (sc :< '/') xs
  'u'  => case xs of
    w :: x :: y :: z :: t' =>
      if isHexDigit w && isHexDigit x && isHexDigit y && isHexDigit z
        then
          let c := cast $ hexDigit w * 0x1000 +
                          hexDigit x * 0x100 +
                          hexDigit y * 0x10 +
                          hexDigit z
           in str (sc :< c) t'
        else invalidEscape p t'
    _    => invalidEscape p xs
  _    => invalidEscape p xs
str sc ('"'  :: xs) = Succ (strLit sc) xs
str sc (c    :: xs) =
  if isControl c then range (InvalidControl c) p xs
  else str (sc :< c) xs
str sc []           = failEOI p

term : Tok Char JSToken
term (x :: xs) = case x of
  ',' => Succ ',' xs
  '"' => str [<] xs
  ':' => Succ ':' xs
  '[' => Succ '[' xs
  ']' => Succ ']' xs
  '{' => Succ '{' xs
  '}' => Succ '}' xs
  'n' => case xs of
    'u' :: 'l' :: 'l' :: t => Succ (Lit JNull) t
    _                      => unknown xs
  't' => case xs of
    'r' :: 'u' :: 'e' :: t => Succ (Lit $ JBool True) t
    _                      => unknown xs
  'f' => case xs of
    'a' :: 'l' :: 's' :: 'e' :: t => Succ (Lit $ JBool False) t
    _                             => unknown xs
  d   => suffix (Lit . JNumber . cast . cast {to = String}) $
         number [<] (d :: xs)

term []        = failEmpty

go :
     SnocList (Bounded JSToken)
 -> (pos   : Position)
 -> (cs    : List Char)
 -> (0 acc : SuffixAcc cs)
 -> Either (Bounded ParseErr) (List (Bounded JSToken))
go sx pos ('\n' :: xs) (SA rec) = go sx (incLine pos) xs rec
go sx pos (x :: xs)    (SA rec) =
  if isSpace x
     then go sx (incCol pos) xs rec
     else case term (x::xs) of
       Succ t xs' @{prf} =>
         let pos2 := addCol (toNat prf) pos
             bt   := bounded t pos pos2
          in go (sx :< bt) pos2 xs' rec
       Stop start errEnd r => Left $ boundedErr pos start errEnd (Reason r)
go sx _ [] _ = Right (sx <>> [])

export
lexJSON : String -> Either (Bounded ParseErr) (List (Bounded JSToken))
lexJSON s = go [<] begin (unpack s) suffixAcc

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

0 Rule : Bool -> Type -> Type
Rule b t =
     (xs : List $ Bounded JSToken)
  -> (0 acc : SuffixAcc xs)
  -> Res b JSToken xs JSErr t

array : Bounds -> SnocList JSON -> Rule True JSON

object : Bounds -> SnocList (String,JSON) -> Rule True JSON

value : Rule True JSON
value (B (Lit y) _ :: xs)        _      = Succ y xs
value (B '[' _ :: B ']' _ :: xs) _      = Succ (JArray []) xs
value (B '[' b :: xs)            (SA r) = succ $ array b [<] xs r
value (B '{' _ :: B '}' _ :: xs) _      = Succ (JObject []) xs
value (B '{' b :: xs)            (SA r) = succ $ object b [<] xs r
value (x :: xs) _                       = unexpected x
value [] _                              = eoi

array b sv xs sa@(SA r) = case value xs sa of
  Succ v (B ',' _ :: ys)  => succ $ array b (sv :< v) ys r
  Succ v (B ']' _ :: ys)  => Succ (JArray $ sv <>> [v]) ys
  res                     => failInParen b '[' res

object b sv (B (Lit $ JString l) _ :: B ':' _ :: xs) (SA r) =
  case succ $ value xs r of
    Res.Succ v (B ',' _ :: ys)  => succ $ object b (sv :< (l,v)) ys r
    Succ v (B '}' _ :: ys)      => Succ (JObject $ sv <>> [(l,v)]) ys
    res                         => failInParen b '[' res
object b sv (B (Lit $ JString _) _ :: x :: xs) _ = expected x.bounds ':'
object b sv (x :: xs)                          _ = custom x.bounds ExpectedString
object b sv []                                 _ = eoi

export
parseJSON :
     Origin
  -> String
  -> Either (FileContext, ParseErr) JSON
parseJSON o str = case lexJSON str of
  Right ts => case value ts suffixAcc of
    Fail x         => Left (fromBounded o x)
    Succ v []      => Right v
    Succ v (x::xs) => Left (fromBounded o $ Unexpected <$> x)
  Left err => Left (fromBounded o err)
