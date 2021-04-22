module JSON.Value

import Language.JSON.Data

||| Abstraction over JSON value representations.
public export
interface Value v where
  stringify : v -> String

  string : String -> v

  number : Double -> v

  boolean : Bool -> v

  array : List v -> v

  object : List (String,v) -> v

  null : v

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
smallInteger : Value v => Integer -> v
smallInteger = number . fromInteger

export
largeInteger : Value v => Integer -> v
largeInteger n = if abs n <= maxSafeInteger
                    then smallInteger n
                    else string $ show n

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

export
Value Language.JSON.Data.JSON where
  stringify = show
  string    = JString
  number    = JNumber
  boolean   = JBoolean
  null      = JNull
  array     = JArray
  object    = JObject
