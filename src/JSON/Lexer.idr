module JSON.Lexer

import Data.Nat
import Data.String
import Generics.Derive

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          String Encoding
--------------------------------------------------------------------------------

hexChar : Int -> Char
hexChar i = if i < 10 then chr (ord '0' + i) else chr (ord 'A' + i - 10)

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
          let x := ord c
           in if x >= 0x20
                then go (sc :< c) t
                else let d1 := hexChar $ x `div` 0x1000
                         d2 := hexChar $ (x `mod` 0x1000) `div` 0x100
                         d3 := hexChar $ (x `mod` 0x100)  `div` 0x10
                         d4 := hexChar $ x `mod` 0x10
                      in go (sc :< '\\' :< 'u' :< d1 :< d2 :< d3 :< d4) t

--------------------------------------------------------------------------------
--          Error
--------------------------------------------------------------------------------

public export
data LexErr : Type where
  MissingQuote     : LexErr
  InvalidLit       : LexErr
  InvalidEsc       : LexErr
  InvalidChar      : LexErr

%runElab derive "LexErr" [Generic,Meta,Show,Eq]

--------------------------------------------------------------------------------
--          Bounds
--------------------------------------------------------------------------------

public export
record Bounds where
  constructor BS
  line     : Nat
  startCol : Nat
  endCol   : Nat

%runElab derive "Bounds" [Generic,Meta,Show,Eq]

--------------------------------------------------------------------------------
--          Token
--------------------------------------------------------------------------------

public export
data Token : Type where
  TBracketO : Bounds -> Token
  TBracketC : Bounds -> Token
  TBraceO   : Bounds -> Token
  TBraceC   : Bounds -> Token
  TComma    : Bounds -> Token
  TColon    : Bounds -> Token
  TNull     : Bounds -> Token
  TBool     : Bounds -> Bool   -> Token
  TNum      : Bounds -> Double -> Token
  TStr      : Bounds -> String -> Token
  TErr      : Bounds -> LexErr -> Token

%runElab derive "Token" [Generic,Meta,Show,Eq]

export
bounds : Token -> Bounds
bounds (TStr x str)  = x
bounds (TNull x)     = x
bounds (TBool x y)   = x
bounds (TNum x dbl)  = x
bounds (TBracketO x) = x
bounds (TBracketC x) = x
bounds (TBraceO x)   = x
bounds (TBraceC x)   = x
bounds (TComma x)    = x
bounds (TColon x)    = x
bounds (TErr x y)    = x

%inline
end : Token -> Nat
end = endCol . bounds

export
disp : Token -> String
disp (TBracketO _)   = "["
disp (TBracketC _)   = "]"
disp (TBraceO _)     = "{"
disp (TBraceC _)     = "}"
disp (TComma _)      = ","
disp (TColon _)      = ":"
disp (TNull _)       = "null"
disp (TBool _ True)  = "true"
disp (TBool _ False) = "false"
disp (TNum _ dbl)    = show dbl
disp (TStr _ str)    = encode str
disp (TErr _ x)      = show x

--------------------------------------------------------------------------------
--          String Decoding
--------------------------------------------------------------------------------

fromHex : Char -> Maybe Int
fromHex c =
  if      '0' <= c && c <= '9' then Just $ ord c - ord '0'
  else if 'a' <= c && c <= 'f' then Just $ ord c - ord 'a' + 10
  else if 'A' <= c && c <= 'F' then Just $ ord c - ord 'A' + 10
  else                              Nothing

-- convert an escaped character in a JSON string.
-- returns the remainder of the string and the number
-- of characters converted
unesc : List Char -> Either Nat (Nat, Char, List Char)
unesc [] = Left 0
unesc (h :: t) = case h of
  '"'  => Right (1, '"', t)
  'n'  => Right (1, '\n', t)
  'f'  => Right (1, '\f', t)
  'b'  => Right (1, '\b', t)
  'r'  => Right (1, '\r', t)
  't'  => Right (1, '\t', t)
  '\\' => Right (1, '\\', t)
  '/'  => Right (1, '/', t)
  'u'  => case t of
     w :: x :: y :: z :: t' =>
       let Just w' := fromHex w | Nothing => Left 2
           Just x' := fromHex x | Nothing => Left 3
           Just y' := fromHex y | Nothing => Left 4
           Just z' := fromHex z | Nothing => Left 5
           i       := w' * 0x1000 + x' * 0x100 + y' * 0x10 + z'
        in Right (5, chr i, t')
     _    => Left 1
  _    => Left 1

str : (line,start,cur : Nat)
    -> SnocList Char
    -> List Char
    -> (Token, List Char)
str l s cur sc []        = (TErr (BS l s s) MissingQuote, [])
str l s cur sc (x :: xs) = case x of
  '"'  => (TStr (BS l s cur) $ pack $ sc <>> Nil, xs)
  '\\' => case unesc xs of
    Left c          => (TErr (BS l cur (cur + c)) InvalidEsc, [])
    Right (m,c,xs') => str l s (cur+1+m) (sc :< c) (assert_smaller xs xs')
  _    =>
    if x >= ' '
       then str l s (cur + 1) (sc :< x) xs
       else (TErr (BS l cur cur) InvalidChar, [])

--------------------------------------------------------------------------------
--          Literal Decoding
--------------------------------------------------------------------------------

-- TODO Validate number case
toLit : Bounds -> SnocList Char -> Token
toLit b sc = case pack (sc <>> Nil) of
  "null"  => TNull b
  "true"  => TBool b True
  "false" => TBool b False
  num     => TNum b $ cast num

isLitChar : Char -> Bool
isLitChar '.' = True
isLitChar '+' = True
isLitChar '-' = True
isLitChar c   = isAlphaNum c

lit : (line,start,cur : Nat)
    -> SnocList Char
    -> List Char
    -> (Token, List Char)
lit l s cur sc []        = (toLit (BS l s (minus cur 1)) sc, [])
lit l s cur sc (x :: xs) =
  if isLitChar x
     then lit l s (cur+1) (sc :< x) xs
     else (toLit (BS l s (minus cur 1)) sc, x :: xs)

--------------------------------------------------------------------------------
--          Lexer
--------------------------------------------------------------------------------

lex : (line,col : Nat) -> SnocList Token -> List Char -> List Token
lex _ _   sc [] = sc <>> Nil
lex l cur sc (c :: cs) = case c of
  ':'  => lex l (cur+1) (sc :< TColon (BS l cur cur)) cs
  ','  => lex l (cur+1) (sc :< TComma (BS l cur cur)) cs
  '"' =>
    let (t, xs2) := str l cur (cur+1) Lin cs
     in lex l (end t + 1) (sc :< t) (assert_smaller cs xs2)

  '['  => lex l (cur+1) (sc :< TBracketO (BS l cur cur)) cs
  ']'  => lex l (cur+1) (sc :< TBracketC (BS l cur cur)) cs
  '{'  => lex l (cur+1) (sc :< TBraceO (BS l cur cur)) cs
  '}'  => lex l (cur+1) (sc :< TBraceC (BS l cur cur)) cs
  '\n' => lex (l+1) 1 sc cs
  _   =>
    if isSpace c then lex l (cur+1) sc cs
    else if isLitChar c then
      let (t, xs2) := lit l cur cur Lin (c :: cs)
       in lex l (end t + 1) (sc :< t) (assert_smaller cs xs2)
    else sc <>> [TErr (BS l cur cur) InvalidChar]

export %inline
lexJSONLine : (line : Nat) -> String -> List Token
lexJSONLine l = lex l 1 Lin . unpack

export %inline
lexJSON : String -> List Token
lexJSON = lexJSONLine 1

--------------------------------------------------------------------------------
--          Debugging
--------------------------------------------------------------------------------

lineAt : List String -> Nat -> String
lineAt []        _     = ""
lineAt _         Z     = ""
lineAt (x :: xs) (S Z) = x
lineAt (_ :: xs) (S k) = lineAt xs k

export
tokenLines : List String -> Bounds -> String -> List String
tokenLines strs bs tok  =
   [  lineAt strs bs.line
   ,  replicate (minus bs.startCol 1) ' '
   ++ replicate (S $ minus bs.endCol bs.startCol) '^'
   ++ " \{tok}"
   ]

||| Tokenizes a JSON string and pretty prints all the tokens
||| found, while displaying the line and position each token was found on.
export
debugLexJSON : String -> List String
debugLexJSON str =
  let ls = lines str
      ts = lexJSON str
   in ts >>= \t => tokenLines ls (bounds t) (disp t)

||| Pretty prints the tokens found in a JSON string to stdout
export
printLexJSON : String -> IO ()
printLexJSON = traverse_ putStrLn . debugLexJSON
