||| Interface and utilities for marshalling Idris2 values from JSON
||| via an intermediate `Value` representation.
|||
||| For regular algebraic data types, implementations can automatically
||| be derived using elaborator reflection (see module `Derive.FromJSON`)
|||
||| Operators and functionality strongly influenced by Haskell's aeson
||| library
module JSON.FromJSON

import Data.Either
import Data.List.Quantifiers as LQ
import Data.SortedMap
import Data.Vect.Quantifiers as VQ
import Derive.Prelude
import JSON.ToJSON
import JSON.Option
import JSON.Encoder

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Types
--------------------------------------------------------------------------------

public export
data JSONPathElement = Key String | Index Bits32

%runElab derive "JSONPathElement" [Show,Eq]

public export
JSONPath : Type
JSONPath = List JSONPathElement

public export
JSONErr : Type
JSONErr = (JSONPath,String)

public export
Result : Type -> Type
Result = Either JSONErr

public export
Parser : Type -> Type -> Type
Parser v a = v -> Either JSONErr a

public export
orElse : Either a b -> Lazy (Either a b) -> Either a b
orElse r@(Right _) _ = r
orElse _           v = v

public export
(<|>) : Parser v a -> Parser v a -> Parser v a
f <|> g = \vv => f vv `orElse` g vv

public export
data DecodingErr : Type where
  JErr      : JSONErr -> DecodingErr
  JParseErr : ParseError JSErr-> DecodingErr

%runElab derive "DecodingErr" [Show,Eq]

public export
DecodingResult : Type -> Type
DecodingResult = Either DecodingErr

--------------------------------------------------------------------------------
--          Error Formatting
--------------------------------------------------------------------------------

||| Format a <http://goessner.net/articles/JsonPath/ JSONPath> as a 'String'
||| which represents the path relative to some root object.
export
formatRelativePath : JSONPath -> String
formatRelativePath path = format "" path

  where
    isIdentifierKey : List Char -> Bool
    isIdentifierKey []      = False
    isIdentifierKey (x::xs) = isAlpha x && all isAlphaNum xs

    escapeChar : Char -> String
    escapeChar '\'' = "\\'"
    escapeChar '\\' = "\\\\"
    escapeChar c    = singleton c

    escapeKey : List Char -> String
    escapeKey = fastConcat . map escapeChar

    formatKey : String -> String
    formatKey key =
      let chars := fastUnpack key
       in if isIdentifierKey chars then fastPack $ '.' :: chars
          else "['" ++ escapeKey chars ++ "']"

    format : String -> JSONPath -> String
    format pfx []                = pfx
    format pfx (Index idx :: parts) = format (pfx ++ "[" ++ show idx ++ "]") parts
    format pfx (Key key :: parts)   = format (pfx ++ formatKey key) parts

||| Format a <http://goessner.net/articles/JsonPath/ JSONPath> as a 'String',
||| representing the root object as @$@.
export
formatPath : JSONPath -> String
formatPath path = "$" ++ formatRelativePath path

||| Annotate an error message with a
||| <http://goessner.net/articles/JsonPath/ JSONPath> error location.
export
formatError : JSONPath -> String -> String
formatError path msg = "Error in " ++ formatPath path ++ ": " ++ msg

export
Interpolation DecodingErr where
  interpolate (JErr (p,s))  = formatError p s
  interpolate (JParseErr x) = interpolate x

||| Pretty prints a decoding error. In case of a parsing error,
||| this might be printed on several lines.
|||
||| DEPRECATED: Use `interpolate` instead
export %deprecate
prettyErr : (input : String) -> DecodingErr -> String
prettyErr _ = interpolate

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface FromJSON a  where
  constructor MkFromJSON
  fromJSON : forall v,obj . Value v obj => Parser v a

export %inline
decodeVia :
     (0 v : Type)
  -> {auto _ : Value v obj}
  -> {auto _ : FromJSON a}
  -> String
  -> DecodingResult a
decodeVia v s =
  let Right json := parse {v} Virtual s | Left err => Left (JParseErr err)
      Right res  := fromJSON json       | Left p   => Left (JErr p)
   in Right res

export %inline
decodeEitherVia :
     (0 v : Type)
  -> {auto _ : Value v obj}
  -> {auto _ : FromJSON a}
  -> String
  -> Either String a
decodeEitherVia v s = mapFst (prettyErr s) $ decodeVia v s

export %inline
decodeMaybeVia : (0 v : Type) -> Value v obj => FromJSON a => String -> Maybe a
decodeMaybeVia v = either (const Nothing) Just . decodeVia v

export %inline
decode : FromJSON a => String -> DecodingResult a
decode = decodeVia JSON

export %inline
decodeEither : FromJSON a => String -> Either String a
decodeEither = decodeEitherVia JSON

export %inline
decodeMaybe : FromJSON a => String -> Maybe a
decodeMaybe = decodeMaybeVia JSON

--------------------------------------------------------------------------------
--          Parsing Utilities
--------------------------------------------------------------------------------

export %inline
fail : String -> Result a
fail s = Left (Nil,s)

typeMismatch : Value v obj => String -> Parser v a
typeMismatch expected actual =
  fail $ "expected \{expected}, but encountered \{typeOf actual}"

unexpected : Value v obj => Parser v a
unexpected actual = fail $ "unexpected \{typeOf actual}"

export %inline
modifyFailure : (String -> String) -> Result a -> Result a
modifyFailure f = mapFst (map f)

||| If the inner 'Parser' failed, prepend the given string to the failure
||| message.
export %inline
prependFailure : String -> Result a -> Result a
prependFailure = modifyFailure . (++)

export %inline
prependContext : String -> Result a -> Result a
prependContext name = prependFailure "parsing \{name} failed, "

export %inline
prependPath : Result a -> JSONPathElement -> Result a
prependPath r elem = mapFst (\(path,s) => (elem :: path,s)) r

export infixr 9 <?>, .:, .:?, .:!

||| Deprecated: Use `prependPath` instead.
export %inline %deprecate
(<?>) : Result a -> JSONPathElement -> Result a
(<?>) = prependPath

withValue :
     {auto _ : Value v obj}
  -> (type : String)
  -> (v -> Maybe t)
  -> (name : Lazy String)
  -> Parser t a
  -> Parser v a
withValue s get n f val =
  case get val of
    Just v  => f v
    Nothing => prependContext n $ typeMismatch s val

export %inline
withObject : Value v obj => Lazy String -> Parser obj a -> Parser v a
withObject = withValue "Object" getObject

export %inline
withBoolean : Value v obj => Lazy String -> Parser Bool a -> Parser v a
withBoolean = withValue "Boolean" getBoolean

export %inline
withString : Value v obj => Lazy String -> Parser String a -> Parser v a
withString = withValue "String" getString

export %inline
eqString : Value v obj => Lazy String -> String -> Parser v ()
eqString n s = withString n $ \s' =>
  if s == s' then Right () else fail "expected '\{s}' but got '\{s'}'"

export %inline
withDouble : Value v obj => Lazy String -> Parser Double a -> Parser v a
withDouble = withValue "Double" getDouble

export %inline
withInteger : Value v obj => Lazy String -> Parser Integer a -> Parser v a
withInteger = withValue "Integer" getInteger

export
boundedIntegral :
     {auto _ : Num a}
  -> {auto _ : Value v obj}
  -> Lazy String
  -> (lower : Integer)
  -> (upper : Integer)
  -> Parser v a
boundedIntegral s lo up =
  withInteger s $ \n =>
    if n >= lo && n <= up
      then pure $ fromInteger n
      else fail "integer out of bounds: \{show n}"

export %inline
withArray : Value v obj => Lazy String -> Parser (List v) a -> Parser v a
withArray = withValue "Array" getArray

export %inline
withArrayN :
     {auto _ : Value v obj}
  -> (n : Nat)
  -> Lazy String
  -> Parser (Vect n v) a
  -> Parser v a
withArrayN n = withValue "Array of length \{show n}" (getArrayN n)

||| See `field`
export
explicitParseField :
     {auto _ : Object obj v}
  -> {auto _ : Value v obj}
  -> Parser v a
  -> obj
  -> Parser String a
explicitParseField p o key =
  case lookup key o of
    Nothing => fail "key \{show key} not found"
    Just v  => p v `prependPath` Key key

||| See `fieldMaybe`
export
explicitParseFieldMaybe :
     {auto _ : Object obj v}
  -> {auto _ : Value v obj}
  -> Parser v a
  -> obj
  -> Parser String (Maybe a)
explicitParseFieldMaybe p o key =
  case lookup key o of
    Nothing => Right Nothing
    Just v  =>
      if isNull v then Right Nothing else map Just $ p v `prependPath` Key key

||| See `optField`
export
explicitParseFieldMaybe' :
     {auto _ : Object obj v}
  -> {auto _ : Encoder v}
  -> {auto _ : Value v obj}
  -> Parser v a
  -> obj
  -> Parser String a
explicitParseFieldMaybe' p o key =
  case lookup key o of
    Nothing   => p null `prependPath` Key key
    Just v    => p v `prependPath` Key key

||| Retrieve the value associated with the given key of an `IObject`.
||| The result is `empty` if the key is not present or the value cannot
||| be converted to the desired type.
|||
||| This accessor is appropriate if the key and value /must/ be present
||| in an object for it to be valid.  If the key and value are
||| optional, use `optField` instead.
export %inline
field : Object obj v => Value v obj => FromJSON a => obj -> Parser String a
field = explicitParseField fromJSON

||| Deprecated: Use `field` instead
export %deprecate %inline
(.:) : Object obj v => Value v obj => FromJSON a => obj -> Parser String a
(.:) = field

||| Retrieve the value associated with the given key of an `IObject`. The
||| result is `Nothing` if the key is not present or if its value is `Null`,
||| or `empty` if the value cannot be converted to the desired type.
|||
||| This accessor is most useful if the key and value can be absent
||| from an object without affecting its validity.  If the key and
||| value are mandatory, use `field` instead.
export %inline
fieldMaybe :
     {auto _ : Object obj v}
  -> {auto _ : FromJSON a}
  -> {auto _ : Value v obj}
  -> obj
  -> Parser String (Maybe a)
fieldMaybe = explicitParseFieldMaybe fromJSON

||| Retrieve the value associated with the given key of an `Object`
||| using the given default value in case the key is missing.
export %inline
fieldWithDeflt :
     {auto _ : Object obj v}
  -> {auto _ : FromJSON a}
  -> {auto _ : Value v obj}
  -> obj
  -> Lazy a
  -> Parser String a
fieldWithDeflt o v s = fromMaybe v <$> fieldMaybe o s

||| Deprecated: Use `fieldMaybe` instead
export %deprecate %inline
(.:?) :
     {auto _ : Object obj v}
  -> {auto _ : FromJSON a}
  -> {auto _ : Value v obj}
  -> obj
  -> Parser String (Maybe a)
(.:?) = fieldMaybe

||| Retrieve the value associated with the given key of an `IObject`
||| passing on `Null` in case the given key is missing.
|||
||| This differs from `fieldMaybe` in that it can be used with any converter
||| accepting `Null` as an input.
export %inline
optField :
     {auto _ : Object obj v}
  -> {auto _ : Encoder v}
  -> {auto _ : FromJSON a}
  -> {auto _ : Value v obj}
  -> obj
  -> Parser String a
optField = explicitParseFieldMaybe' fromJSON

||| Deprecated: Use `optField` instead
export %deprecate %inline
(.:!) :
     {auto _ : Object obj v}
  -> {auto _ : Encoder v}
  -> {auto _ : FromJSON a}
  -> {auto _ : Value v obj}
  -> obj
  -> Parser String a
(.:!) = optField

||| Function variant of `.:`.
|||
||| Deprecated: Use `field` instead
export %deprecate %inline
parseField :
     {auto _ : Object obj v}
  -> {auto _ : FromJSON a}
  -> {auto _ : Value v obj}
  -> obj
  -> Parser String a
parseField = field

||| Function variant of `.:?`.
|||
||| Deprecated: Use `fieldMaybe` instead
export %deprecate %inline
parseFieldMaybe :
     {auto _ : Object obj v}
  -> {auto _ : FromJSON a}
  -> {auto _ : Value v obj}
  -> obj
  -> Parser String (Maybe a)
parseFieldMaybe = fieldMaybe

||| Function variant of `.:!`.
|||
||| Deprecated: Use `optField` instead
export %deprecate
parseFieldMaybe' :
     {auto _ : Object obj v}
  -> {auto _ : FromJSON a}
  -> {auto _ : Encoder v}
  -> {auto _ : Value v obj}
  -> obj
  -> Parser String a
parseFieldMaybe' = optField

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

export
FromJSON Void where
  fromJSON v = fail "Cannot parse Void"

export
FromJSON () where
  fromJSON = withArray "()" $
    \case Nil    => pure ()
          _ :: _ => fail "parsing () failed, expected empty list"

export
FromJSON Bool where
  fromJSON = withBoolean "Bool" pure

export
FromJSON Double where
  fromJSON = withDouble "Double" pure

export
FromJSON Bits8 where
  fromJSON = boundedIntegral "Bits8" 0 0xff

export
FromJSON Bits16 where
  fromJSON = boundedIntegral "Bits16" 0 0xffff

export
FromJSON Bits32 where
  fromJSON = boundedIntegral "Bits32" 0 0xffffffff

export
FromJSON Bits64 where
  fromJSON = boundedIntegral "Bits64" 0 0xffffffffffffffff

export
FromJSON Int where
  fromJSON = boundedIntegral "Int" (-0x8000000000000000) 0x7fffffffffffffff

export
FromJSON Int8 where
  fromJSON = boundedIntegral "Int8" (-0x80) 0x7f

export
FromJSON Int16 where
  fromJSON = boundedIntegral "Int16" (-0x8000) 0x7fff

export
FromJSON Int32 where
  fromJSON = boundedIntegral "Int32" (-0x80000000) 0x7fffffff

export
FromJSON Int64 where
  fromJSON = boundedIntegral "Int64" (-0x8000000000000000) 0x7fffffffffffffff

export
FromJSON Nat where
  fromJSON = withInteger "Nat" $ \n =>
    if n >= 0 then pure $ fromInteger n
    else fail #"not a natural number: \#{show n}"#

export
FromJSON Integer where
  fromJSON = withInteger "Integer" pure

export
FromJSON String where
  fromJSON = withString "String" pure

export
FromJSON Char where
  fromJSON = withString "Char" $ \str =>
    case strM str of
      (StrCons c "") => pure c
      _ => fail "expected a string of length 1"

export
FromJSON a => FromJSON (Maybe a) where
  fromJSON v = if isNull v then pure Nothing else Just <$> fromJSON v

export
FromJSON a => FromJSON (List a) where
  fromJSON = withArray "List" $ traverse fromJSON

export
FromJSON a => FromJSON (SnocList a) where
  fromJSON = map ([<] <><) . fromJSON

export
FromJSON a => FromJSON (List1 a) where
  fromJSON = withArray "List1" $
    \case Nil    => fail "expected non-empty list"
          h :: t => traverse fromJSON (h ::: t)

export
{n : Nat} -> FromJSON a => FromJSON (Vect n a) where
  fromJSON = withArray "Vect \{show n}" $ \vs =>
    case toVect n vs of
      Just vect => traverse fromJSON vect
      Nothing   => fail "expected list of length \{show n}"

export
FromJSON a => FromJSON b => FromJSON (Either a b) where
  fromJSON = withObject "Either" $ \o =>
    map Left (field o "Left") `orElse`
    map Right (field o "Right")

export
FromJSON a => FromJSON b => FromJSON (a, b) where
  fromJSON = withArray "Pair" $
    \case [x,y] => [| MkPair (fromJSON x) (fromJSON y) |]
          _     => fail "expected a pair of values"

readLQ :
     {auto _ : Value v obj}
  -> {auto ps : LQ.All.All (FromJSON . f) ts}
  -> Parser (List v) (LQ.All.All f ts)
readLQ @{_} @{[]} [] = Right []
readLQ @{_} @{_::_} (x :: xs) = [| fromJSON x :: readLQ xs |]
readLQ @{_} @{_::_} [] = fail "list of values too short"
readLQ @{_} @{[]} _    = fail "list of values too long"

readVQ :
     {auto _ : Value v obj}
  -> {auto ps : VQ.All.All (FromJSON . f) ts}
  -> Parser (List v) (VQ.All.All f ts)
readVQ @{_} @{[]} [] = Right []
readVQ @{_} @{_::_} (x :: xs) = [| fromJSON x :: readVQ xs |]
readVQ @{_} @{_::_} [] = fail "list of values too short"
readVQ @{_} @{[]} _    = fail "list of values too long"

export
LQ.All.All (FromJSON . f) ts => FromJSON (LQ.All.All f ts) where
  fromJSON = withArray "HList" $ readLQ

export
VQ.All.All (FromJSON . f) ts => FromJSON (VQ.All.All f ts) where
  fromJSON = withArray "HVect" $ readVQ

export
FromJSON a => FromJSON (SortedMap String a) where
  fromJSON object =
    case pairs <$> getObject object of
         Just props => maybe (fail "expected an object with string keys and values") Right $
                         foldr (\(key, val), sortedMap => pure $ insert key !(eitherToMaybe $ fromJSON val) !sortedMap)
                               (Just SortedMap.empty)
                               props
         Nothing => fail "expected an object"

||| Tries to decode a value encoded as a single field object of the given name.
|||
||| This corresponds to the `ObjectWithSingleField` option
||| for encoding sum types.
export
fromSingleField :
     {auto _ : Object obj v}
  -> {auto _ : Value v obj}
  -> (tpe : Lazy String)
  -> Parser (String,v) a
  -> Parser v a
fromSingleField n f = withObject n $ \o => case pairs o of
  [p] => f p
  _   => fail "expected single field object"

||| Tries to decode a value encoded as a two-element array with the given
||| constructor name.
|||
||| This corresponds to the `TwoElemArray` option
||| for encoding sum types.
export
fromTwoElemArray :
     {auto _ : Object obj v}
  -> {auto _ : Value v obj}
  -> (tpe : Lazy String)
  -> Parser (String,v) a
  -> Parser v a
fromTwoElemArray n f =
  withArrayN 2 n $ \[x,y] => withString n (\s => f (s,y)) x

||| Tries to decode a value encoded as a tagged object with the given
||| tag and content field, plus tag value.
|||
||| This corresponds to the `TaggedObject` option
||| for encoding sum types.
export
fromTaggedObject :
     {auto _ : Object obj v}
  -> {auto _ : Value v obj}
  -> (tpe : Lazy String)
  -> (tagField, contentField : String)
  -> Parser (String,v) a
  -> Parser v a
fromTaggedObject n tf cf f = withObject n $ \o => do
  s <- field o tf
  v <- explicitParseField pure o cf
  f (s,v)
