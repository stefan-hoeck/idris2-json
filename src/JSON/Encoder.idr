||| The interfaces in this module abstract over how we
||| encode and decode values from and to JSON.
|||
||| This allows us to use different (probably backend dependant)
||| intermediary data representations to be used by the actual
||| marshallers `ToJSON` and `FromJSON`.
module JSON.Encoder

import Data.List
import Data.Vect
import public JSON.Parser

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

  ||| Encodes a `Double` as a JSON `Double`.
  double : Double -> v

  ||| Encodes a `Double` as a JSON `Integer`.
  integer : Integer -> v

  ||| Encodes a `Bool` as a JSON `Boolean`.
  boolean : Bool -> v

  ||| Encodes a `List` of values as a JSON `Array`.
  array : List v -> v

  ||| Encodes a `List` key-value pairs as a JSON `Object`
  object : List (String,v) -> v

  null : v

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
  pairs  : obj -> List (String,v)

||| Abstraction over JSON value representation for decoding.
public export
interface Object obj v => Value v obj | v where
  ||| Returns the actual value. This should be one of
  ||| "String", "Null", "Object", "Number", "Boolean", or "Array".
  ||| However, other types are possible as well, as this is
  ||| only used for error messages when something goes wrong.
  typeOf : v -> String

  ||| Tries to convert a string to an intermediare value.
<<<<<<< HEAD
  parse : Origin -> String -> Either (ParseError JSErr) v
=======
  parse : Origin -> String -> ParseRes Void JTok v
>>>>>>> 0f4fa4c ([ refactor, wip ] use ilex-json for parsing)

  ||| Tries to convert a value to an `Object`.
  getObject : v -> Maybe obj

  ||| Tries to convert a value to an `Array` of values.
  getArray : v -> Maybe (List v)

  ||| Tries to convert a value to a `Boolean`.
  getBoolean : v -> Maybe Bool

  ||| Tries to convert a value to a `Double`.
  getDouble : v -> Maybe Double

  ||| Tries to convert a value to an `Integer`.
  getInteger : v -> Maybe Integer

  ||| Tries to convert a value to a `String`.
  getString : v -> Maybe String

  ||| `True`, if the value in question is `null`.
  isNull : v -> Bool

public export
getArrayN : Value v obj => (n : Nat) -> v -> Maybe (Vect n v)
getArrayN n x = getArray x >>= toVect n

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

export %inline
Encoder JSON where
  stringify = show
  string    = JString
  double    = JDouble
  integer   = JInteger
  boolean   = JBool
  null      = JNull
  array     = JArray
  object    = JObject

export %inline
Object (List (String,JSON)) JSON where
  lookup = Data.List.lookup
  pairs = id

export %inline
Value JSON (List (String,JSON)) where
  parse     = parseJSON

  typeOf JNull        = "Null"
  typeOf (JBool _)    = "Boolean"
  typeOf (JDouble _)  = "Double"
  typeOf (JInteger _)  = "Integer"
  typeOf (JString _)  = "String"
  typeOf (JArray _)   = "Array"
  typeOf (JObject _)  = "Object"

  getObject (JObject ps) = Just ps
  getObject _            = Nothing

  getDouble (JDouble v)  = Just v
  getDouble (JInteger v) = Just (cast v)
  getDouble _            = Nothing

  getInteger (JInteger v) = Just v
  getInteger _           = Nothing

  getBoolean (JBool v)  = Just v
  getBoolean _            = Nothing

  getArray (JArray v) = Just v
  getArray _          = Nothing

  getString (JString v) = Just v
  getString _           = Nothing

  isNull JNull = True
  isNull _     = False
