module JSON.Parser

import JSON.Lexer

%default total

public export
data JSON : Type where
  JNull   : JSON
  JNumber : Double -> JSON
  JBool   : Bool   -> JSON
  JString : String -> JSON
  JArray  : List JSON -> JSON
  JObject : List (String, JSON) -> JSON

hexChar : Int -> Char
hexChar i = if i < 10 then chr (ord '0' + i) else chr (ord 'A' + i - 10)

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

value  : List Token -> Maybe (List Token, JSON)

array  : SnocList JSON -> List Token -> Maybe (List Token, JSON)

object : SnocList (String, JSON) -> List Token -> Maybe (List Token, JSON)

value (TBracketO :: xs)    = array Lin xs
value (TBraceO :: xs)      = object Lin xs
value (TLit "true" :: xs)  = Just (xs, JBool True)
value (TLit "false" :: xs) = Just (xs, JBool False)
value (TLit "null" :: xs)  = Just (xs, JNull)
value (TLit cs :: xs)      = Just (xs, JNumber $ cast cs)
value (TStr s :: xs)       = Just (xs, JString s)
value _                    = Nothing

array sv (TBracketC :: xs) = Just (xs, JArray $ sv <>> Nil)
array sv xs               =
  let Just (TComma :: xs2, v) := value xs
        | Just (TBracketC :: xs2, v) => Just (xs2, JArray $ sv <>> [v])
        | _                          => Nothing
   in array (sv :< v) (assert_smaller xs xs2)

object sp (TBraceC :: xs)            = Just (xs, JObject $ sp <>> Nil)
object sp (TStr s  :: TColon :: xs)  =
  let Just (TComma :: xs2, v) := value xs
        | Just (TBraceC :: xs2, v) => Just (xs2, JObject $ sp <>> [(s,v)])
        | _                        => Nothing
   in object (sp :< (s, v)) (assert_smaller xs xs2)
object _ _                           = Nothing

export
parse : String -> Maybe JSON
parse s = case value (lexJSON s) of
  Just ([], v) =>  Just v
  _            => Nothing
