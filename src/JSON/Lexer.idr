module JSON.Lexer

%default total

public export
data Token : Type where
  TBracketO : Token
  TBracketC : Token
  TBraceO   : Token
  TBraceC   : Token
  TComma    : Token
  TColon    : Token
  TLit      : String -> Token
  TStr      : String -> Token
  TOther    : Char -> Token

fromHex : Char -> Maybe Int
fromHex c =
  if      '0' <= c && c <= '9' then Just $ ord c - ord '0'
  else if 'a' <= c && c <= 'f' then Just $ ord c - ord 'a' + 10
  else if 'A' <= c && c <= 'F' then Just $ ord c - ord 'A' + 10
  else                              Nothing

unesc : List Char -> Maybe (Char, List Char)
unesc [] = Nothing
unesc (h :: t) = case h of
  '"'  => Just ('"', t)
  'n'  => Just ('\n', t)
  'f'  => Just ('\f', t)
  'b'  => Just ('\b', t)
  'r'  => Just ('\r', t)
  't'  => Just ('\t', t)
  '\\' => Just ('\\', t)
  '/'  => Just ('/', t)
  'u'  => case t of
     w :: x :: y :: z :: t' =>
       let Just w' := fromHex w | Nothing => Nothing
           Just x' := fromHex x | Nothing => Nothing
           Just y' := fromHex y | Nothing => Nothing
           Just z' := fromHex z | Nothing => Nothing
           i       := w' * 0x1000 + x' * 0x100 + y' * 0x10 + z'
        in Just (chr i, t')
     _    => Nothing
  _    => Nothing

lexString : SnocList Char -> List Char -> (Token, List Char)
lexString sc []           = (TStr $ pack $ sc <>> Nil, [])
lexString sc ('"'  :: xs) = (TStr $ pack $ sc <>> Nil, xs)
lexString sc ('\\' :: xs) = case unesc xs of
  Just (c,xs') => lexString (sc :< c) (assert_smaller xs xs')
  Nothing      => (TOther '\\', xs)
lexString sc (c :: xs)    = lexString (sc :< c) xs

takeLit : SnocList Char -> List Char -> (List Char, List Char)
takeLit sc []        = (sc <>> Nil, [])
takeLit sc (x :: xs) =
  if isAlphaNum x || elem x ['.', '-', '+']
     then takeLit (sc :< x) xs
     else (sc <>> [], x :: xs)

lex : SnocList Token -> List Char -> List Token
lex sc [] = sc <>> Nil
lex sc (c :: cs) = case c of
  '"' =>
    let (t,xs2) = lexString Lin cs
     in lex (sc :< t) (assert_smaller cs xs2)
  '[' => lex (sc :< TBracketO) cs
  ']' => lex (sc :< TBracketC) cs
  '{' => lex (sc :< TBraceO) cs
  '}' => lex (sc :< TBraceC) cs
  ',' => lex (sc :< TComma) cs
  ':' => lex (sc :< TColon) cs
  _   =>
    if isSpace c || isControl c
       then lex sc cs
       else let (t, xs2) = takeLit Lin cs
             in lex (sc :< (TLit $ pack $ c :: t)) (assert_smaller cs xs2)

export %inline
lexJSON : String -> List Token
lexJSON = lex Lin . unpack
