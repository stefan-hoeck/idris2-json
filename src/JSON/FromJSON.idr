||| Interface and utilities for marshalling Idris2 values from JSON
||| via an intermediate `Value` representation.
|||
||| For regular algebraic data types, implementations can automatically
||| be derived using elaborator reflection.
|||
||| Operators and functionality strongly influenced by Haskell's aeson
||| library
module JSON.FromJSON

import JSON.ToJSON
import JSON.Option
import JSON.Value
import Language.JSON

import Generics.Derive

%language ElabReflection

--------------------------------------------------------------------------------
--          Types
--------------------------------------------------------------------------------

public export
data JSONPathElement = Key String | Index Bits32

%runElab derive "JSONPathElement" [Generic,Meta,Show,Eq]

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
      let chars = fastUnpack key
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

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface FromJSON a  where
  constructor MkFromJSON
  fromJSON : forall v,obj . Value v obj => Parser v a

export %inline
decodeVia : (0 v : Type) -> Value v obj => FromJSON a => String -> Result a
decodeVia v s = mapFst (Nil,) (parse {v} s) >>= fromJSON

export %inline
decodeEitherVia : (0 v : Type)
                -> Value v obj
                => FromJSON a
                => String
                -> Either String a
decodeEitherVia v = mapFst (uncurry formatError) . decodeVia v

export %inline
decodeMaybeVia : (0 v : Type) -> Value v obj => FromJSON a => String -> Maybe a
decodeMaybeVia v = either (const Nothing) Just . decodeVia v

export %inline
decode : FromJSON a => String -> Result a
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
  fail $ #"expected \#{expected}, but encountered \#{typeOf actual}"#

unexpected : Value v obj => Parser v a
unexpected actual = fail $ #"unexpected \#{typeOf actual}"#

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
prependContext name = prependFailure #"parsing \#{name} failed, "#

infixr 3 <?>, .:, .:?, .:!

export %inline
(<?>) : Result a -> JSONPathElement -> Result a
r <?> elem = mapFst (\(path,s) => (elem :: path,s)) r

withValue :  Value v obj
          => (type : String)
          -> (v -> Maybe t)
          -> (name : Lazy String)
          -> Parser t a
          -> Parser v a
withValue s get n f val = case get val of
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
withNumber : Value v obj => Lazy String -> Parser Double a -> Parser v a
withNumber = withValue "Number" getNumber

export
withInteger : Value v obj => Lazy String -> Parser Integer a -> Parser v a
withInteger s f =
  withNumber s $ \d =>
    let n = the Integer (cast d)
    in if d == fromInteger n
          then f n
          else fail #"not an integer: \#{show d}"#

export
withLargeInteger : Value v obj => Lazy String -> Parser Integer a -> Parser v a
withLargeInteger s f v =
  withInteger s f v `orElse` withString s parseStr v
  where parseStr : Parser String a
        parseStr str = case parseInteger {a = Integer} str of
                            Nothing => fail #"not an integer: \#{show str}"#
                            Just n  => f n

export
boundedIntegral :  Num a
                => Value v obj
                => Lazy String
                -> (lower : Integer)
                -> (upper : Integer)
                -> Parser v a
boundedIntegral s lo up =
  withInteger s $ \n => if n >= lo && n <= up
                         then pure $ fromInteger n
                         else fail #"integer out of bounds: \#{show n}"#

export
boundedLargeIntegral :  Num a
                     => Value v obj
                     => Lazy String
                     -> (lower : Integer)
                     -> (upper : Integer)
                     -> Parser v a
boundedLargeIntegral s lo up =
  withLargeInteger s $ \n => if n >= lo && n <= up
                              then pure $ fromInteger n
                              else fail #"integer out of bounds: \#{show n}"#

export %inline
withArray : Value v obj => Lazy String -> Parser (List v) a -> Parser v a
withArray = withValue "Array" getArray

||| See `.:`
export
explicitParseField : Object obj v => Value v obj =>
                     Parser v a -> obj -> Parser String a
explicitParseField p o key =
  case lookup key o of
       Nothing => fail #"key \#{show key} not found"#
       Just v  => p v <?> Key key

||| See `.:?`
export
explicitParseFieldMaybe : Object obj v => Value v obj =>
                          Parser v a -> obj -> Parser String (Maybe a)
explicitParseFieldMaybe p o key =
  case lookup key o of
       Nothing => Right Nothing
       Just v  => if isNull v then Right Nothing else Just <$> p v <?> Key key

||| See `.:!`
export
explicitParseFieldMaybe' : Object obj v => Value v obj =>
                           Parser v a -> obj -> Parser String (Maybe a)
explicitParseFieldMaybe' p o key =
  case lookup key o of
       Nothing   => Right Nothing
       Just v    => Just <$> p v <?> Key key

||| Retrieve the value associated with the given key of an `IObject`.
||| The result is `empty` if the key is not present or the value cannot
||| be converted to the desired type.
||| 
||| This accessor is appropriate if the key and value /must/ be present
||| in an object for it to be valid.  If the key and value are
||| optional, use `.:?` instead.
export
(.:) : Object obj v => Value v obj => FromJSON a => obj -> Parser String a
(.:) = explicitParseField fromJSON

||| Retrieve the value associated with the given key of an `IObject`. The
||| result is `Nothing` if the key is not present or if its value is `Null`,
||| or `empty` if the value cannot be converted to the desired type.
||| 
||| This accessor is most useful if the key and value can be absent
||| from an object without affecting its validity.  If the key and
||| value are mandatory, use `.:` instead.
export
(.:?) : Object obj v => Value v obj => FromJSON a =>
        obj -> Parser String (Maybe a)
(.:?) = explicitParseFieldMaybe fromJSON

||| Retrieve the value associated with the given key of an `IObject`
||| The result is `Nothing` if the key is not present or 'empty' if the
||| value cannot be converted to the desired type.
||| 
||| This differs from `.:?` by attempting to parse `Null` the same as any
||| other JSON value, instead of interpreting it as `Nothing`.
export
(.:!) : Object obj v => Value v obj => FromJSON a =>
        obj -> Parser String (Maybe a)
(.:!) = explicitParseFieldMaybe' fromJSON

||| Function variant of `.:`.
export
parseField : Object obj v => Value v obj => FromJSON a =>
             obj -> Parser String a
parseField = (.:)

||| Function variant of `.:?`.
export
parseFieldMaybe : Object obj v => Value v obj => FromJSON a =>
                  obj -> Parser String (Maybe a)
parseFieldMaybe = (.:?)

||| Function variant of `.:!`.
export
parseFieldMaybe' : Object obj v => Value v obj => FromJSON a =>
                   obj -> Parser String (Maybe a)
parseFieldMaybe' = (.:!)

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
  fromJSON = withNumber "Double" pure

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
  fromJSON = boundedLargeIntegral "Bits64" 0 0xffffffffffffffff

export
FromJSON Int where
  fromJSON = boundedLargeIntegral "Int" (-0x8000000000000000) 0x7fffffffffffffff

export
FromJSON Int8 where
  fromJSON = boundedLargeIntegral "Int8" (-0x80) 0x7f

export
FromJSON Int16 where
  fromJSON = boundedLargeIntegral "Int16" (-0x8000) 0x7fff

export
FromJSON Int32 where
  fromJSON = boundedLargeIntegral "Int32" (-0x80000000) 0x7fffffff

export
FromJSON Int64 where
  fromJSON = boundedLargeIntegral "Int64" (-0x8000000000000000) 0x7fffffffffffffff

export
FromJSON Nat where
  fromJSON = withLargeInteger "Nat" $ \n =>
    if n >= 0 then pure $ fromInteger n
    else fail #"not a natural number: \#{show n}"#

export
FromJSON Integer where
  fromJSON = withLargeInteger "Integer" pure

export
FromJSON String where
  fromJSON = withString "String" pure

export
FromJSON Char where
  fromJSON = withString "Char" $
    \str => case strM str of
                 (StrCons c "") => pure c
                 _ => fail "expected a string of length 1"

export
FromJSON a => FromJSON (Maybe a) where
  fromJSON v = if isNull v then pure Nothing else Just <$> fromJSON v

export
FromJSON a => FromJSON (List a) where
  fromJSON = withArray "List" $ traverse fromJSON

export
FromJSON a => FromJSON (List1 a) where
  fromJSON = withArray "List1" $
    \case Nil    => fail #"expected non-empty list"#
          h :: t => traverse fromJSON (h ::: t)

export
{n : Nat} -> FromJSON a => FromJSON (Vect n a) where
  fromJSON = withArray #"Vect \#{show n}"# $
    \vs => case toVect n vs of
                Just vect => traverse fromJSON vect
                Nothing   => fail #"expected list of length \#{show n}"#

export
(FromJSON a, FromJSON b) => FromJSON (Either a b) where
  fromJSON = withObject "Either" $ \o =>
               map Left (o .: "Left") `orElse` map Right (o .: "Right")

--------------------------------------------------------------------------------
--          SOP Implementations
--------------------------------------------------------------------------------

np : Value v obj => (all : NP (FromJSON . f) ks) => Parser (List v) (NP f ks)
np vs = case fromListNP all vs of
          Just npVS => hctraverse (FromJSON . f) fromJSON npVS
          Nothing   => fail #"expected array of \#{show $ hsize all} values"#

export
NP (FromJSON . f) ks => FromJSON (NP f ks) where
  fromJSON = withArray "NP" np

export
(FromJSON a, FromJSON b) => FromJSON (a,b) where
  fromJSON = map (\[x,y] => (x,y)) . fromJSON {a = NP I [a,b] }

firstSuccess :  NP (K (Parser v a)) ts -> Parser v a
firstSuccess []        _ = fail #"Can't parse nullary sum"#
firstSuccess (f :: []) o = f o
firstSuccess (f :: fs) o = f o `orElse` firstSuccess fs o

ns : Value v obj =>
     (all : NP (FromJSON . f) ks) => Parser v (NS f ks)
ns = withObject "NS"
   $ firstSuccess 
   $ hcliftA2 (FromJSON . f) parse (injectionsNP all) (indices all)
  where parse : FromJSON (f a) =>
                (f a -> NS f ks) -> Bits32 -> obj -> Result (NS f ks)
        parse f ix o = map f (o .: show ix)

export
NP (FromJSON . f) ks => FromJSON (NS f ks) where
  fromJSON = ns

||| Decodes a newtype-like sum of products
||| (exactly one single value constructor) by wrapping
||| the decoded value in `MkSOP . Z`.
export
sopNewtype : Value v obj => FromJSON (f k) => Parser v (SOP f [[k]])
sopNewtype = map (\x => MkSOP $ Z [x]) . fromJSON

consAsEnum :  Value v obj
           => String
           -> NP_ (List k) (ConInfo_ k) kss
           -> (0 prf : EnumType kss)
           -> Parser v (NS_ (List k) (NP_ k f) kss)
consAsEnum tn np prf =
  withString tn $ \s => firstSuccess (hliftA2 run np (nullaryInjections np prf)) s
  where run :  ConInfo_ k ks
            -> NS_ (List k) (NP f) kss
            -> Parser String (NS_ (List k) (NP f) kss)
        run i res s = if i.conName == s then Right res
                                        else fail #"expected \#{i.conName}"#

||| Decodes an enum-like sum of products
||| (only nullary constructors) by trying to extract one of the
||| constructors' name
export
sopEnum :  Value v obj
        => TypeInfo' k kss
        -> {auto 0 prf : EnumType kss}
        -> Parser v (SOP f kss)
sopEnum (MkTypeInfo _ tn cs) v = MkSOP <$> consAsEnum tn cs prf v

-- Decodes an applied, record-like constructor as list of key-value pairs.
conFields : Value v obj => NP (FromJSON . f) ks =>
            String -> NP (K String) ks -> Parser v (NP f ks)
conFields cn names = withObject cn $ \o =>
                       hctraverse (FromJSON . f) (parseField o) names

untagged : Value v obj => NP (FromJSON . f) ks =>
           ConInfo ks -> Parser v (NP f ks)
untagged info = maybe fromJSON (conFields info.conName) (argNames info)

||| Decodes a single-constructor sum of products. The
||| constructor's name is ignored.
export
sopRecord : Value v obj => NP (FromJSON . f) ks =>
            TypeInfo [ks] -> Parser v (SOP f [ks])
sopRecord (MkTypeInfo _ n [i]) v = map (MkSOP . Z) (untagged i v)

-- Decodes an applied constructor as a tagged object, if it is record-like,
-- that is, all fields do have a field name. Otherwise, it is
-- encoded as a two-field object, one field for the constructor's name
-- the other for the encoded heterogeneous array.
tagged :  Value v obj
       => NP (FromJSON . f) ks
       => (tagField : String)
       -> (contentField : String)
       -> ConInfo ks
       -> Parser v (NP f ks)
tagged tf cf ci v =
  do nm <- withObject ci.conName (.: tf) v
     if nm == ci.conName
        then case argNames ci of
                  Nothing => withObject ci.conName (.: cf) v
                  Just ns => conFields ci.conName ns v
        else fail #"expected \#{ci.conName}"#

-- Decodes a constructer as a single-field object. The constructor's name
-- is used as the field name.
asObject : Value v obj => NP (FromJSON . f) ks =>
           (typeName : String) -> ConInfo ks -> Parser v (NP f ks)
asObject tn i@(MkConInfo _ n _) =
  withObject tn $ \o => explicitParseField (untagged i) o n

-- Decodes a single constructor as a two element array: The first element
-- being the constructor's name, the second its encoded values.
asTwoElemArray : Value v obj => NP (FromJSON . f) ks =>
                 (typeName : String) -> ConInfo ks -> Parser v (NP f ks)
asTwoElemArray tn i@(MkConInfo _ cn _) =
  withArray tn $ \vs => case vs of
                             [n,c] => do n2 <- fromJSON n
                                         if n2 == cn
                                            then untagged i c
                                            else fail #"expected \#{cn} but got \#{n2}"#
                             _     => fail #"expected 2-element array"#

||| Decodes a sum of products as specified by the passed
||| `SumEncoding` (see its documentation for details) using
||| the given `TypeInfo` to decode constructor and argument names.
|||
||| See also `sopRecord` for decoding values with a single constructor,
||| `sopEnum` for decoding enum types (only nullary constructors),
||| and `sopNewtype` for decoding newtype wrappers.
export
sop : Value v obj
    => (all : POP (FromJSON . f) kss)
    => SumEncoding
    -> TypeInfo' k kss
    -> Parser v (SOP_ k f kss)
sop {all = MkPOP nps} enc (MkTypeInfo _ tn cs) =
  case enc of
       UntaggedValue         => impl untagged
       ObjectWithSingleField => impl (asObject tn)
       TwoElemArray          => impl (asTwoElemArray tn)
       (TaggedObject tf cf)  => impl (tagged tf cf)

  where injSOP : NP_ (List k) (InjectionSOP f kss) kss
        injSOP = hmap (MkSOP .) $ injectionsNP nps

        impl : (forall ks . NP (FromJSON . f) ks =>
                            ConInfo ks -> Parser v (NP f ks))
             -> Parser v (SOP f kss)
        impl g = firstSuccess $ hcliftA2 (NP $ FromJSON . f) apply injSOP cs
          where apply :  NP_ k (FromJSON . f) ts
                      => (NP_ k f ts -> SOP_ k f kss)
                      -> ConInfo_ k ts
                      -> Parser v (SOP_ k f kss)
                apply f c = map f . g c

--------------------------------------------------------------------------------
--          Generic Decoders
--------------------------------------------------------------------------------

||| Generic version of `sopNewtype`.
export
genNewtypeFromJSON : Value v obj => Generic a [[k]] => FromJSON k => Parser v a
genNewtypeFromJSON = map to . sopNewtype

||| Generic version of `sopEnum`.
export
genEnumFromJSON :  Value v obj => Meta a kss => {auto 0 prf : EnumType kss}
                -> Parser v a
genEnumFromJSON = map to . sopEnum (metaFor a)

||| Like `genEnumFromJSON`, but uses the given function to adjust
||| constructor names before being used as tags.
export
genEnumFromJSON' :  Value v obj => Meta a kss => {auto 0 prf : EnumType kss}
                 -> (String -> String) -> Parser v a
genEnumFromJSON' f = let meta = adjustConnames f (metaFor a)
                      in map to . sopEnum meta {prf}

||| Generic version of `sopRecord`.
export
genRecordFromJSON : Value v obj => Meta a [ks] => NP FromJSON ks => Parser v a
genRecordFromJSON = map to . sopRecord (metaFor a)

||| Like `genRecordFromJSON`, but uses the given function to adjust
||| field names before being used as tags.
export
genRecordFromJSON' : Value v obj => Meta a [ks] => NP FromJSON ks =>
                     (String -> String) -> Parser v a
genRecordFromJSON' f = let meta = adjustFieldNames f (metaFor a)
                        in map to . sopRecord meta

export
genFromJSON : Value v obj => Meta a code => POP FromJSON code =>
              SumEncoding -> Parser v a
genFromJSON enc = map to . sop enc (metaFor a)

export
genFromJSON' :  Value v obj
             => Meta a code
             => POP FromJSON code
             => (adjFieldLabel : String -> String)
             -> (adjConstructorTag : String -> String)
             -> SumEncoding
             -> Parser v a
genFromJSON' ff fc enc = let meta = adjustInfo ff fc (metaFor a) 
                          in map to . sop enc meta

--------------------------------------------------------------------------------
--          Elab Deriving
--------------------------------------------------------------------------------

namespace Derive
  export
  customFromJSON : TTImp -> DeriveUtil -> InterfaceImpl
  customFromJSON tti g = MkInterfaceImpl "FromJSON" Export []
                           `(MkFromJSON ~(tti))
                           (implementationType `(FromJSON) g)

  ||| Derives a `FromJSON` implementation for the given data type
  export
  FromJSON : DeriveUtil -> InterfaceImpl
  FromJSON = customFromJSON `(genFromJSON defaultTaggedObject)

  ||| Derives a `FromJSON` implementation for the given single-constructor
  ||| data type
  export
  RecordFromJSON : DeriveUtil -> InterfaceImpl
  RecordFromJSON = customFromJSON `(genRecordFromJSON)

  ||| Derives a `FromJSON` implementation for the given enum type
  export
  EnumFromJSON : DeriveUtil -> InterfaceImpl
  EnumFromJSON = customFromJSON `(\v => genEnumFromJSON v)

  ||| Derives a `FromJSON` implementation for the given newtype
  export
  NewtypeFromJSON : DeriveUtil -> InterfaceImpl
  NewtypeFromJSON = customFromJSON `(genNewtypeFromJSON)
