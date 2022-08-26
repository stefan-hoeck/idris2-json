||| The interfaces in this module abstract over how we
||| encode and decode values from and to JSON.
|||
||| This allows us to use different (probably backend dependant)
||| intermediary data representations to be used by the actual
||| marshallers `ToJSON` and `FromJSON`.
module JSON.Value

import Data.List
import JSON.Parser

||| In Javascript, numbers are represented as IEEE 64bit
||| floating point numbers. Integers can be represented exactly
||| in the range [-(2^53-1), 2^53-1]. This library's default
||| behavior is, that large integers will be encoded as
||| `string` and smaller values use `number`
public export
maxSafeInteger : Integer
maxSafeInteger = 9007199254740991

--------------------------------------------------------------------------------
--          Encoding
--------------------------------------------------------------------------------

||| Abstraction over JSON value encoding.
public export
interface Encoder v where
  ||| Converts the intermediary data representation
  ||| to a JSON string.
  stringify : v -> String

  ||| Encodes a `String` value.
  string : String -> v

  ||| Encodes a `Double` as a JSON `Number`.
  number : Double -> v

  ||| Encodes a `Bool` as a JSON `Boolean`.
  boolean : Bool -> v

  ||| Encodes a `List` of values as a JSON `Array`.
  array : List v -> v

  ||| Encodes a `List` key-value pairs as a JSON `Object`
  object : List (String,v) -> v

  null : v

||| Encode a small integer (less than or equal to `maxSafeInteger`)
||| as a number.
export %inline
smallInteger : Encoder v => Integer -> v
smallInteger = number . fromInteger

||| Encode an `Integer` (possibly larger than `masSafeInteger`)
||| as a number or a string.
|||
||| The corresponding decoder for potentially large numbers
||| will also try both types: Number and string.
export %inline
largeInteger : Encoder v => Integer -> v
largeInteger n = if abs n <= maxSafeInteger
                    then smallInteger n
                    else string $ show n

--------------------------------------------------------------------------------
--          Decoding
--------------------------------------------------------------------------------

||| Abstraction over JSON Object representation for decoding.
||| It is important that `obj` is the type that guides interface
||| resolution here, otherwise operators like `.:` cannot conveniently
||| be used, since Idris needs additional guidance to resolve interfaces.
public export
interface Object obj v | obj where
  lookup : String -> obj -> Maybe v

||| Abstraction over JSON value representation for decoding.
public export
interface Object obj v => Value v obj | v where
  ||| Returns the actual value. This should be one of
  ||| "String", "Null", "Object", "Number", "Boolean", or "Array".
  ||| However, other types are possible as well, as this is
  ||| only used for error messages when something goes wrong.
  typeOf : v -> String

  ||| Tries to convert a string to an intermediare value.
  parse : String -> Either String v

  ||| Tries to convert a value to an `Object`.
  getObject : v -> Maybe obj

  ||| Tries to convert a value to an `Array` of values.
  getArray : v -> Maybe (List v)

  ||| Tries to convert a value to a `Boolean`.
  getBoolean : v -> Maybe Bool

  ||| Tries to convert a value to a `Number`.
  getNumber : v -> Maybe Double

  ||| Tries to convert a value to a `String`.
  getString : v -> Maybe String

  ||| `True`, if the value in question is `null`.
  isNull : v -> Bool

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

export %inline
Encoder JSON where
  stringify = show
  string    = JString
  number    = JNumber
  boolean   = JBool
  null      = JNull
  array     = JArray
  object    = JObject

export %inline
Object (List (String,JSON)) JSON where
  lookup = Data.List.lookup

export %inline
Value JSON (List (String,JSON)) where
  parse     = maybe (Left "Couldn't parse JSON.") Right . parse

  typeOf JNull        = "Null"
  typeOf (JBool _)    = "Boolean"
  typeOf (JNumber _)  = "Number"
  typeOf (JString _)  = "String"
  typeOf (JArray _)   = "Array"
  typeOf (JObject _)  = "Object"

  getObject (JObject ps) = Just ps
  getObject _            = Nothing

  getNumber (JNumber v) = Just v
  getNumber _           = Nothing

  getBoolean (JBool v)  = Just v
  getBoolean _            = Nothing

  getArray (JArray v) = Just v
  getArray _          = Nothing

  getString (JString v) = Just v
  getString _           = Nothing

  isNull JNull = True
  isNull _     = False
