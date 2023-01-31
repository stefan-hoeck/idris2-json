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
  Unclosed        : Char -> JSErr
  Unknown         : Char -> JSErr

%runElab derive "JSErr" [Show,Eq]

export
Interpolation JSErr where
  interpolate (Unclosed c)    = "Unclosed \{show c}"
  interpolate (Unknown c)     = "Unknown token: \{show c}"
  interpolate ExpectedString  = "Expected string literal"
  interpolate InvalidEscape   = "Invalid escape sequence"

public export %tcinline
0 ParseErr : Type
ParseErr = Bounded (ParseError JSToken JSErr)

strLit : SnocList Char -> JSToken
strLit = Lit . JString . pack

str : SnocList Char -> AutoTok False Char JSToken
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
        else Succ (strLit sc) ('\\'::'u'::w::x::y::z::t')
    _    => Succ (strLit sc) ('\\'::'u'::xs)
  _    => Succ (strLit sc) ('\\'::c::xs)
str sc ('"'  :: xs) = Succ (strLit sc) xs
str sc (c    :: xs) = str (sc :< c) xs
str sc []           = Fail

term : Tok True Char JSToken
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
    _                      => Fail
  't' => case xs of
    'r' :: 'u' :: 'e' :: t => Succ (Lit $ JBool True) t
    _                      => Fail
  'f' => case xs of
    'a' :: 'l' :: 's' :: 'e' :: t => Succ (Lit $ JBool False) t
    _                             => Fail
  d   => suffix (Lit . JNumber . cast . pack) $
         number {pre = [<]} (d :: xs) @{Same}

term []        = Fail

toErr : (l,c : Nat) -> Char -> List Char -> Either ParseErr a
toErr l c '"'  cs = custom (oneChar l c) (Unclosed '"')
toErr l c '\\' ('u' :: t) =
  custom (BS l c l (c + 2 + min 4 (length t))) InvalidEscape
toErr l c '\\' (h :: t)   = custom (BS l c l (c + 2)) InvalidEscape
toErr l c x   cs = custom (oneChar l c) (Unknown x)

go :
     SnocList (Bounded JSToken)
 -> (l,c   : Nat)
 -> (cs    : List Char)
 -> (0 acc : SuffixAcc cs)
 -> Either ParseErr (List (Bounded JSToken))
go sx l c ('\n' :: xs) (SA rec) = go sx (l+1) 0 xs rec
go sx l c (x :: xs)    (SA rec) =
  if isSpace x
     then go sx l (c+1) xs rec
     else case term (x::xs) of
       Succ t xs' @{prf} =>
         let c2 := c + toNat prf
             bt := bounded t l c l c2
          in go (sx :< bt) l c2 xs' rec
       Fail => toErr l c x xs
go sx l c [] _ = Right (sx <>> [])

export
lexJSON : String -> Either ParseErr (List (Bounded JSToken))
lexJSON s = go [<] 0 0 (unpack s) suffixAcc

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
  Succ v (B ',' _ :: ys) => succ $ array b (sv :< v) ys r
  Succ v (B ']' _ :: ys) => Succ (JArray $ sv <>> [v]) ys
  Succ v (y       :: ys) => unexpected y
  Succ _ []              => custom b (Unclosed '[')
  Fail (B EOI _)         => custom b (Unclosed '[')
  Fail err               => Fail err

object b sv (B (Lit $ JString l) _ :: B ':' _ :: xs) (SA r) =
  case succ $ value xs r of
    Succ v (B ',' _ :: ys) => succ $ object b (sv :< (l,v)) ys r
    Succ v (B '}' _ :: ys) => Succ (JObject $ sv <>> [(l,v)]) ys
    Succ v (y       :: ys) => unexpected y
    Succ _ []              => custom b (Unclosed '}')
    Fail (B EOI _)         => custom b (Unclosed '}')
    Fail err               => Fail err
object b sv (B (Lit $ JString _) _ :: x :: xs) _ = expected x.bounds ':'
object b sv (x :: xs)                          _ = custom x.bounds ExpectedString
object b sv []                                 _ = eoi

export
parseJSON : Origin -> String -> Either (ReadError JSToken JSErr) JSON
parseJSON o str = case lexJSON str of
  Right ts => case value ts suffixAcc of
    Fail x         => Left (parseFailed o $ singleton x)
    Succ v []      => Right v
    Succ v (x::xs) => Left (parseFailed o $ singleton $ Unexpected <$> x)
  Left err => Left (parseFailed o $ singleton err)

-- --------------------------------------------------------------------------------
-- --          Debugging
-- --------------------------------------------------------------------------------
--
-- lineAt : List String -> Nat -> String
-- lineAt []        _     = ""
-- lineAt _         Z     = ""
-- lineAt (x :: xs) (S Z) = x
-- lineAt (_ :: xs) (S k) = lineAt xs k
--
-- export
-- tokenLines : List String -> Bounds -> String -> List String
-- tokenLines strs bs tok  =
--    [  lineAt strs bs.line
--    ,  replicate (minus bs.startCol 1) ' '
--    ++ replicate (S $ minus bs.endCol bs.startCol) '^'
--    ++ " \{tok}"
--    ]
--
-- ||| Tokenizes a JSON string and pretty prints all the tokens
-- ||| found, while displaying the line and position each token was found on.
-- export
-- debugLexJSON : String -> List String
-- debugLexJSON str =
--   let ls = lines str
--       ts = lexJSON str
--    in ts >>= \t => tokenLines ls (bounds t) (disp t)
--
-- ||| Pretty prints the tokens found in a JSON string to stdout
-- export
-- printLexJSON : String -> IO ()
-- printLexJSON = traverse_ putStrLn . debugLexJSON
