module JSON.Value

import Data.List
import Language.JSON

||| Abstraction over JSON Object representations.
||| It is important that `obj` is the type that guides interface
||| resolution here, otherwise operators like `.:` cannot conveniently
||| be used, since Idris needs additional guidance to resolve interfaces.
public export
interface Object obj v | obj where
  lookup : String -> obj -> Maybe v

||| Abstraction over JSON value representations.
public export
interface Object obj v => Value v obj | v where

  ------------------------------------------------------------------------------
  -- Encoding

  stringify : v -> String

  string : String -> v

  number : Double -> v

  boolean : Bool -> v

  array : List v -> v

  object : List (String,v) -> v

  null : v

  ------------------------------------------------------------------------------
  -- decoding

  typeOf : v -> String

  parse : String -> Either String v

  getObject : v -> Maybe obj

  getArray : v -> Maybe (List v)

  getBoolean : v -> Maybe Bool

  getNumber : v -> Maybe Double

  getString : v -> Maybe String

  isNull : v -> Bool

||| In Javascript, numbers are represented as IEEE 64bit
||| floating point numbers. Integers can be represented exactly
||| in the range [-(2^53-1), 2^53-1]. This library's default
||| behavior is, that large integers will be encoded as
||| `string` and smaller values use `number`
public export
maxSafeInteger : Integer
maxSafeInteger = 9007199254740991

||| Encode a small integer (less than or equal to `maxSafeInteger`)
||| as a number
export %inline
smallInteger : Value v obj => Integer -> v
smallInteger = number . fromInteger

export
largeInteger : Value v obj => Integer -> v
largeInteger n = if abs n <= maxSafeInteger
                    then smallInteger n
                    else string $ show n

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

export %inline
Object (List (String,JSON)) JSON where
  lookup = Data.List.lookup

export %inline
Value JSON (List (String,JSON)) where
  stringify = show
  string    = JString
  number    = JNumber
  boolean   = JBoolean
  null      = JNull
  array     = JArray
  object    = JObject

  parse     = maybe (Left "Couldn't parse JSON.") Right . parse

  typeOf JNull        = "Null"
  typeOf (JBoolean _) = "Boolean"
  typeOf (JNumber _)  = "Number"
  typeOf (JString _)  = "String"
  typeOf (JArray _)   = "Array"
  typeOf (JObject _)  = "Object"
  
  getObject (JObject ps) = Just ps
  getObject _            = Nothing
  
  getNumber (JNumber v) = Just v
  getNumber _           = Nothing
  
  getBoolean (JBoolean v) = Just v
  getBoolean _            = Nothing
  
  getArray (JArray v) = Just v
  getArray _          = Nothing
  
  getString (JString v) = Just v
  getString _           = Nothing
  
  isNull JNull = True
  isNull _     = False
