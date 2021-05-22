||| Interface and utilities for encoding Idris2 values to JSON
||| via an entermediate `Value` representation.
|||
||| For regular algebraic data types, implementations can automatically
||| be derived using elaborator reflection.
|||
||| Operators and functionality strongly influenced by Haskell's aeson
||| library
module JSON.ToJSON

import Data.List1
import Data.Vect
import JSON.Option
import JSON.Value
import Language.JSON
import Generics.Derive

%language ElabReflection

public export
interface ToJSON a where
  constructor MkToJSON
  toJSON : forall v . Encoder v => a -> v

infixr 8 .=

export
(.=) : ToJSON a => Encoder v => String -> a -> (String,v)
s .= val = (s, toJSON val)

export
encodeVia : (0 v : Type) -> Encoder v => ToJSON a => a -> String
encodeVia v val = stringify $ toJSON {v} val

export
encode : ToJSON a => a -> String
encode = encodeVia JSON

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

export
ToJSON Void where
  toJSON x impossible

export
ToJSON String where toJSON = string

export
ToJSON Char where toJSON = string . singleton

export
ToJSON Double where toJSON = number

export
ToJSON Bits8 where toJSON = smallInteger . cast

export
ToJSON Bits16 where toJSON = smallInteger . cast

export
ToJSON Bits32 where toJSON = smallInteger . cast

export
ToJSON Bits64 where toJSON = largeInteger . cast

export
ToJSON Int where toJSON = largeInteger . cast

export
ToJSON Integer where toJSON = largeInteger

export
ToJSON Nat where toJSON = largeInteger . natToInteger

export
ToJSON Bool where toJSON = boolean

export
ToJSON a => ToJSON (Maybe a) where
  toJSON Nothing  = null
  toJSON (Just a) = toJSON a

export
ToJSON a => ToJSON (List a) where
  toJSON = array . map toJSON

export
ToJSON a => ToJSON (List1 a) where
  toJSON = toJSON . forget

export
ToJSON a => ToJSON (Vect n a) where
  toJSON = toJSON . toList

export
ToJSON () where
  toJSON () = array Nil

export
(ToJSON a, ToJSON b) => ToJSON (Either a b) where
  toJSON (Left a)  = object ["Left"  .= a]
  toJSON (Right b) = object ["Right" .= b]

--------------------------------------------------------------------------------
--          SOP Implementations
--------------------------------------------------------------------------------

np : Encoder v => NP (ToJSON . f) ks => NP f ks -> v
np = array . collapseNP . hcmap (ToJSON . f) toJSON

export
NP (ToJSON . f) ks => ToJSON (NP f ks) where
  toJSON = np

export
(ToJSON a, ToJSON b) => ToJSON (a,b) where
  toJSON (a,b) = toJSON $ the (NP I _) [a,b]

export
indices : NP f ks ->  NP (K Bits32) ks
indices np = iterateNP np (+1) (the Bits32 0)

ns : Encoder v => (all : NP (ToJSON . f) ks) => NS f ks -> v
ns = collapseNS . hcliftA2 (ToJSON . f) enc (indices all)
  where enc : ToJSON (f a) => Bits32 -> f a -> v
        enc ix v = object [show ix .= v]

export
NP (ToJSON . f) ks => ToJSON (NS f ks) where
  toJSON = ns

||| Encodes a newtype-like sum of products
||| (exactly one single value constructor) by just unwrapping
||| the stored value
export
sopNewtype : Encoder v => ToJSON (f k) => SOP f [[k]] -> v
sopNewtype (MkSOP $ Z [x]) = toJSON x
sopNewtype (MkSOP $ S _) impossible

consAsEnum :  Encoder v
           => NP_ (List k) (ConInfo_ k) kss
           -> NS_ (List k) (NP_ k f) kss
           -> (0 prf : EnumType kss)
           -> v
consAsEnum (c :: _) (Z []) _ = string c.conName
consAsEnum (_ :: cs) (S y) v = consAsEnum cs y (enumTail v)
consAsEnum (_ :: _) (Z (_ :: _)) _ impossible
consAsEnum [] (Z x) _ impossible
consAsEnum [] (S x) _ impossible

||| Encodes an enum-like sum of products
||| (only nullary constructors) by just storing a constructor's name.
export
sopEnum :  Encoder v
        => TypeInfo' k kss
        -> {auto 0 prf : EnumType kss}
        -> SOP f kss
        -> v
sopEnum (MkTypeInfo _ _ cs) (MkSOP ns) = consAsEnum cs ns prf

-- Encodes an applied, record-like constructor as list of key-value pairs.
conFields : Encoder v => NP (ToJSON . f) ks =>
            NP (K String) ks -> NP f ks -> List (String,v)
conFields ns = collapseNP . hcliftA2 (ToJSON . f) (.=) ns

-- Encodes an applied constructor as an object, if it is record-like,
-- that is, all fields are paired with a field name. Otherwise, it is
-- encoded as a heterogeneous array.
untagged : Encoder v => NP (ToJSON . f) ks => ConInfo ks -> NP f ks -> v
untagged i as =
  maybe (toJSON as) (object . (`conFields` as)) (argNames i)

||| Encodes a single-constructor sum of products. The
||| constructor's name is ignored.
export
sopRecord : Encoder v => NP (ToJSON . f) ks => TypeInfo [ks] -> SOP f [ks] -> v
sopRecord (MkTypeInfo _ _ (v :: [])) (MkSOP (Z x)) = untagged v x
sopRecord (MkTypeInfo _ _ (v :: [])) (MkSOP (S x)) impossible

-- Encodes an applied constructor as a tagged object, if it is record-like,
-- that is, all fields do have a field name. Otherwise, it is
-- encoded as a two-field object, one field for the constructor's name
-- the other for the encoded heterogeneous array.
tagged :  Encoder v
       => NP (ToJSON . f) ks
       => (tagField : String)
       -> (contentField : String)
       -> ConInfo ks
       -> NP f ks
       -> v
tagged tf cf i as =
  maybe (object [ tf .= i.conName, cf .= as])
        (\np => object $ (tf .= i.conName) :: conFields np as)
        (argNames i)

-- Encodes a constructer as a single-field object. The constructor's name
-- is used as the field name.
asObject : Encoder v => NP (ToJSON . f) ks => ConInfo ks -> NP f ks -> v
asObject i@(MkConInfo _ n _) np = object [(n, untagged i np)]

-- Encodes a single constructor, as a two element array: The first element
-- being the constructor's name, the second its encoded values.
asTwoElemArray : Encoder v => NP (ToJSON . f) ks => ConInfo ks -> NP f ks -> v
asTwoElemArray i@(MkConInfo _ n _) np = array [string n, untagged i np]

||| Encodes a sum of products as specified by the passed
||| `SumEncoding` (see its documentation for details) using
||| the given `TypeInfo` to encode constructor and argument names.
|||
||| See also `sopRecord` for encoding values with a single constructor,
||| `sopEnum` for encoding enum types (only nullary constructors),
||| and `sopNewtype` for encoding newtype wrappers.
export
sop : Encoder v
    => (all : POP (ToJSON . f) kss)
    => SumEncoding
    -> TypeInfo kss
    -> SOP f kss
    -> v
sop {all = MkPOP _} enc (MkTypeInfo _ _ cons) (MkSOP ns) =
  case enc of
       UntaggedValue         => impl untagged
       ObjectWithSingleField => impl asObject
       TwoElemArray          => impl asTwoElemArray
       (TaggedObject tf cf)  => impl $ tagged tf cf

  where impl : (forall ks . NP (ToJSON . f) ks => ConInfo ks -> NP f ks -> v)
             -> v
        impl g = collapseNS $ hcliftA2 (NP $ ToJSON . f) g cons ns

--------------------------------------------------------------------------------
--          Generic Encoders
--------------------------------------------------------------------------------

||| Generic version of `sopNewtype`.
export
genNewtypeToJSON : Encoder v => Generic a [[k]] => ToJSON k => a -> v
genNewtypeToJSON = sopNewtype . from

||| Generic version of `sopEnum`.
export
genEnumToJSON :  Encoder v => Meta a kss => {auto 0 prf : EnumType kss}
              -> a -> v
genEnumToJSON = sopEnum (metaFor a) . from

||| Like `genEnumToJSON`, but uses the given function to adjust
||| constructor names before being used as tags.
export
genEnumToJSON' :  Encoder v => Meta a kss => {auto 0 prf : EnumType kss}
               -> (String -> String) -> a -> v
genEnumToJSON' f = let meta = adjustConnames f (metaFor a)
                    in sopEnum meta {prf} . from

||| Generic version of `sopRecord`.
export
genRecordToJSON : Encoder v => Meta a [ks] => NP ToJSON ks => a -> v
genRecordToJSON = sopRecord (metaFor a) . from

||| Like `genRecordToJSON`, but uses the given function to adjust
||| field names before being used as tags.
export
genRecordToJSON' : Encoder v => Meta a [ks] => NP ToJSON ks =>
                   (String -> String) -> a -> v
genRecordToJSON' f = let meta = adjustFieldNames f (metaFor a)
                      in sopRecord meta . from

export
genToJSON : Encoder v => Meta a code => POP ToJSON code =>
            SumEncoding -> a -> v
genToJSON enc = sop enc (metaFor a) . from

export
genToJSON' :  Encoder v
           => Meta a code
           => POP ToJSON code
           => (adjFieldLabel : String -> String)
           -> (adjConstructorTag : String -> String)
           -> SumEncoding
           -> a
           -> v
genToJSON' ff fc enc = let meta = adjustInfo ff fc (metaFor a) 
                        in sop enc meta . from

--------------------------------------------------------------------------------
--          Elab Deriving
--------------------------------------------------------------------------------

namespace Derive
  export
  customToJSON : TTImp -> DeriveUtil -> InterfaceImpl
  customToJSON tti g = MkInterfaceImpl "ToJSON" Export []
                          `(MkToJSON ~(tti))
                          (implementationType `(ToJSON) g)

  ||| Derives a `ToJSON` implementation for the given data type
  export
  ToJSON : DeriveUtil -> InterfaceImpl
  ToJSON = customToJSON `(genToJSON defaultTaggedObject)

  ||| Derives a `ToJSON` implementation for the given single-constructor
  ||| data type
  export
  RecordToJSON : DeriveUtil -> InterfaceImpl
  RecordToJSON = customToJSON `(genRecordToJSON)

  ||| Derives a `ToJSON` implementation for the given enum type
  export
  EnumToJSON : DeriveUtil -> InterfaceImpl
  EnumToJSON = customToJSON `(genEnumToJSON)

  ||| Derives a `ToJSON` implementation for the given newtype
  export
  NewtypeToJSON : DeriveUtil -> InterfaceImpl
  NewtypeToJSON = customToJSON `(genNewtypeToJSON)
