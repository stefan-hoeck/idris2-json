||| Interface and utilities for encoding Idris2 values to JSON
||| via an entermediate `Value` representation.
|||
||| For regular algebraic data types, implementations can automatically
||| be derived using elaborator reflection (see module `Derive.ToJSON`)
|||
||| Operators and functionality strongly influenced by Haskell's aeson
||| library
module JSON.Simple.ToJSON

import Data.List.Quantifiers as LQ
import Data.List1
import Data.SortedMap
import Data.String
import Data.Vect
import Data.Vect.Quantifiers as VQ
import JSON.Parser
import JSON.Simple.Option

||| Interface for encoding an Idris value as a JSON value.
public export
interface ToJSON a where
  constructor MkToJSON
  toJSON : a -> JSON

||| Interface for encoding an Idris value as a key in a JSON object
public export
interface ToJSONKey a where
  constructor MkToJSONKey
  toKey : a -> String

export %inline
jpair : ToJSONKey k => ToJSON a => k -> a -> (String,JSON)
jpair s val = (toKey s, toJSON val)

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

export
ToJSON JSON where toJSON = id

export
ToJSON Void where
  toJSON x impossible

export %inline
ToJSON String where toJSON = JString

export %inline
ToJSONKey String where toKey = id

export %inline
ToJSON Char where toJSON = JString . singleton

export %inline
ToJSONKey Char where toKey = singleton

export %inline
ToJSON Double where toJSON = JDouble

export %inline
ToJSON Bits8 where toJSON = JInteger . cast

export %inline
ToJSON Bits16 where toJSON = JInteger . cast

export %inline
ToJSON Bits32 where toJSON = JInteger . cast

export %inline
ToJSON Bits64 where toJSON = JInteger . cast

export %inline
ToJSON Int8 where toJSON = JInteger . cast

export %inline
ToJSON Int16 where toJSON = JInteger . cast

export %inline
ToJSON Int32 where toJSON = JInteger . cast

export %inline
ToJSON Int64 where toJSON = JInteger . cast

export %inline
ToJSON Int where toJSON = JInteger . cast

export %inline
ToJSON Integer where toJSON = JInteger

export %inline
ToJSON Nat where toJSON = JInteger . cast

export %inline
ToJSON Bool where toJSON = JBool

export %inline
ToJSONKey Double where toKey = cast

export %inline
ToJSONKey Bits8 where toKey = cast

export %inline
ToJSONKey Bits16 where toKey = cast

export %inline
ToJSONKey Bits32 where toKey = cast

export %inline
ToJSONKey Bits64 where toKey = cast

export %inline
ToJSONKey Int8 where toKey = cast

export %inline
ToJSONKey Int16 where toKey = cast

export %inline
ToJSONKey Int32 where toKey = cast

export %inline
ToJSONKey Int64 where toKey = cast

export %inline
ToJSONKey Int where toKey = cast

export %inline
ToJSONKey Integer where toKey = cast

export %inline
ToJSONKey Nat where toKey = cast

export %inline
ToJSONKey Bool where toKey = show

export
ToJSON a => ToJSON (Maybe a) where
  toJSON Nothing  = JNull
  toJSON (Just a) = toJSON a

export
ToJSON a => ToJSON (List a) where
  toJSON = JArray . map toJSON

export
ToJSON a => ToJSON (SnocList a) where
  toJSON = toJSON . (<>> [])

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

export
(ps : LQ.All.All (ToJSON . f) ts) => ToJSON (All f ts) where
  toJSON = JArray . forget . zipPropertyWith (\_,v => toJSON v) ps

export
ToJSONKey k => ToJSON v => ToJSON (SortedMap k v) where
  toJSON = JObject . map (uncurry jpair) . SortedMap.toList

export
zipAllWith :
     (f : {0 x : a} -> p x -> q x -> r x)
  -> VQ.All.All p xs
  -> All q xs
  -> All r xs
zipAllWith f [] [] = []
zipAllWith f (px :: pxs) (qx :: qxs) = f px qx :: zipAllWith f pxs qxs

export
(ps : VQ.All.All (ToJSON . f) ts) => ToJSON (VQ.All.All f ts) where
  toJSON = JArray . toList . forget . zipAllWith (\_,v => toJSON v) ps
