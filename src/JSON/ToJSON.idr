||| Interface and utilities for encoding Idris2 values to JSON
||| via an entermediate `Value` representation.
|||
||| For regular algebraic data types, implementations can automatically
||| be derived using elaborator reflection (see module `Derive.ToJSON`)
|||
||| Operators and functionality strongly influenced by Haskell's aeson
||| library
module JSON.ToJSON

import Data.List1
import Data.String
import Data.Vect
import JSON.Option
import JSON.Parser
import JSON.Value

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

||| Encodes a value as a single-field object. The field has the given
||| name.
|||
||| This corresponds to the `ObjectWithSingleField` option
||| for encoding sum types.
export
singleField : Encoder v => String -> v -> v
singleField s x = object [(s,x)]

||| Encodes a value plus a string as a two-element array.
|||
||| This corresponds to the `TwoElemArray` option
||| for encoding sum types.
export
twoElemArray : Encoder v => String -> v -> v
twoElemArray s x = array [string s, x]

||| Encodes a value plus a string as a tagged object.
|||
||| This corresponds to the `TaggedObject` option
||| for encoding sum types.
export
taggedObject :
     Encoder v
  => (tagField, contentField, tag : String)
  -> v
  -> v
taggedObject tf cf tag x = object [(tf, string tag), (cf, x)]

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
ToJSON Int8 where toJSON = smallInteger . cast

export
ToJSON Int16 where toJSON = smallInteger . cast

export
ToJSON Int32 where toJSON = smallInteger . cast

export
ToJSON Int64 where toJSON = largeInteger . cast

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
ToJSON a => ToJSON b => ToJSON (Either a b) where
  toJSON (Left a)  = object ["Left"  .= a]
  toJSON (Right b) = object ["Right" .= b]

export
ToJSON a => ToJSON b => ToJSON (a, b) where
  toJSON (x,y) = array [toJSON x, toJSON y]
