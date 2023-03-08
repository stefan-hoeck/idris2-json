||| Interface and utilities for encoding Idris2 values to JSON
||| via an entermediate `Value` representation.
|||
||| For regular algebraic data types, implementations can automatically
||| be derived using elaborator reflection (see module `Derive.ToJSON`)
|||
||| Operators and functionality strongly influenced by Haskell's aeson
||| library
module JSON.Simple.ToJSON

import Data.List1
import Data.String
import Data.Vect
import JSON.Simple.Option
import JSON.Value

public export
interface ToJSON a where
  constructor MkToJSON
  toJSON : a -> JSON

export %inline
jpair : ToJSON a => String -> a -> (String,JSON)
jpair s val = (s, toJSON val)

export %inline
encode : ToJSON a => a -> String
encode = show . toJSON

||| Encodes a value as a single-field object. The field has the given
||| name.
|||
||| This corresponds to the `ObjectWithSingleField` option
||| for encoding sum types.
export %inline
singleField : String -> JSON -> JSON
singleField s x = JObject [(s,x)]

||| Encodes a value plus a string as a two-element array.
|||
||| This corresponds to the `TwoElemArray` option
||| for encoding sum types.
export %inline
twoElemArray : String -> JSON -> JSON
twoElemArray s x = JArray [JString s, x]

||| Encodes a value plus a string as a tagged object.
|||
||| This corresponds to the `TaggedObject` option
||| for encoding sum types.
export
taggedObject : (tagField, contentField, tag : String) -> JSON -> JSON
taggedObject tf cf tag x = JObject [(tf, JString tag), (cf, x)]

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

||| In Javascript, numbers are represented as IEEE 64bit
||| floating point numbers. Integers can be represented exactly
||| in the range [-(2^53-1), 2^53-1]. This library's default
||| behavior is, that large integers will be encoded as
||| `string` and smaller values use `number`
public export
maxSafeInteger : Integer
maxSafeInteger = 9007199254740991

||| Encode a small integer (less than or equal to `maxSafeInteger`)
||| as a number.
export %inline
smallInteger : Integer -> JSON
smallInteger = JNumber . fromInteger

||| Encode an `Integer` (possibly larger than `maxSafeInteger`)
||| as a number or a string.
|||
||| The corresponding decoder for potentially large numbers
||| will also try both types: Number and string.
export %inline
largeInteger : Integer -> JSON
largeInteger n =
  if abs n <= maxSafeInteger then smallInteger n else JString $ show n

export
ToJSON Void where
  toJSON x impossible

export %inline
ToJSON String where toJSON = JString

export %inline
ToJSON Char where toJSON = JString . singleton

export %inline
ToJSON Double where toJSON = JNumber

export %inline
ToJSON Bits8 where toJSON = smallInteger . cast

export %inline
ToJSON Bits16 where toJSON = smallInteger . cast

export %inline
ToJSON Bits32 where toJSON = smallInteger . cast

export %inline
ToJSON Bits64 where toJSON = largeInteger . cast

export %inline
ToJSON Int8 where toJSON = smallInteger . cast

export %inline
ToJSON Int16 where toJSON = smallInteger . cast

export %inline
ToJSON Int32 where toJSON = smallInteger . cast

export %inline
ToJSON Int64 where toJSON = largeInteger . cast

export %inline
ToJSON Int where toJSON = largeInteger . cast

export %inline
ToJSON Integer where toJSON = largeInteger

export %inline
ToJSON Nat where toJSON = largeInteger . natToInteger

export %inline
ToJSON Bool where toJSON = JBool

export
ToJSON a => ToJSON (Maybe a) where
  toJSON Nothing  = JNull
  toJSON (Just a) = toJSON a

export
ToJSON a => ToJSON (List a) where
  toJSON = JArray . map toJSON

export
ToJSON a => ToJSON (List1 a) where
  toJSON = toJSON . forget

export
ToJSON a => ToJSON (Vect n a) where
  toJSON = toJSON . toList

export
ToJSON () where
  toJSON () = JArray Nil

export
ToJSON a => ToJSON b => ToJSON (Either a b) where
  toJSON (Left a)  = JObject [jpair "Left"  a]
  toJSON (Right b) = JObject [jpair "Right" b]

export
ToJSON a => ToJSON b => ToJSON (a, b) where
  toJSON (x,y) = JArray [toJSON x, toJSON y]
