module Test.Main

import Language.JSON
import JSON
import Hedgehog

import Generics.Derive

%language ElabReflection

--------------------------------------------------------------------------------
--          Fast Eq for Nat
--------------------------------------------------------------------------------

-- The default Eq for Nat runs in O(n), which leads to stack overflows
-- for large Nats
[FastNatEq] Eq Nat where
  (==) = (==) `on` natToInteger
  
-- The default Ord for Nat runs in O(n), which leads to stack overflows
-- for large Nats
[FastNatOrd] Ord Nat using FastNatEq where
  compare = compare `on` natToInteger

--------------------------------------------------------------------------------
--          Elab Deriving
--------------------------------------------------------------------------------

-- example newtype
record Newtype where
  constructor MkNewtype
  field : String

%runElab derive "Newtype" [Generic,Meta,Show,Eq,NewtypeToJSON,NewtypeFromJSON]

-- sum type with default encoding behavior: this will
-- be encoded as a mapping from constructor argument names
-- to values including a special field called "tag" with the
-- encoded constructor name.
data Sum : (a : Type) -> Type where
  Con1 : (name : String) -> (age : Bits32) -> (female : Bool) -> Sum a
  Con2 : (treasure : List a) -> (weight : Bits64) -> Sum a
  Con3 : (foo : Maybe a) -> (bar : Either Bool a) -> Sum a

%runElab derive "Sum" [Generic,Meta,Show,Eq,ToJSON,FromJSON]

-- this sum type will be encoded in the same manner as `Sum`
-- but without the additional "tag" field: This should
-- only be used if not two constructors have the same
-- type and field names.
data Sum2 : (a : Type) -> Type where
  Con21 : (name : String) -> (age : Bits32) -> (female : Bool) -> Sum2 a
  Con22 : (treasure : List a) -> (weight : Bits64) -> Sum2 a
  Con23 : (foo : Maybe a) -> (bar : Either Bool a) -> Sum2 a

%runElab derive "Sum2" [Generic,Meta,Show,Eq]

ToJSON a => ToJSON (Sum2 a) where
  toJSON = genToJSON UntaggedValue

FromJSON a => FromJSON (Sum2 a) where
  fromJSON = genFromJSON UntaggedValue

-- this sum type will be encoded as `Sum` but instead of adding
-- a "tag" for the constructor name, it will be wrapped up
-- as a single field object, the field being named as the
-- constructor used.
data Sum3 : (a : Type) -> Type where
  Con31 : (name : String) -> (age : Bits32) -> (female : Bool) -> Sum3 a
  Con32 : (treasure : List a) -> (weight : Bits64) -> Sum3 a
  Con33 : (foo : Maybe a) -> (bar : Either Bool a) -> Sum3 a

%runElab derive "Sum3" [Generic,Meta,Show,Eq]

ToJSON a => ToJSON (Sum3 a) where
  toJSON = genToJSON ObjectWithSingleField

FromJSON a => FromJSON (Sum3 a) where
  fromJSON = genFromJSON ObjectWithSingleField

-- this sum will be encoded as an array of two elements:
-- the first corresponding to the constructor name, the second
-- to the encoded value.
data Sum4 : (a : Type) -> Type where
  Con41 : (name : String) -> (age : Bits32) -> (female : Bool) -> Sum4 a
  Con42 : (treasure : List a) -> (weight : Bits64) -> Sum4 a
  Con43 : (foo : Maybe a) -> (bar : Either Bool a) -> Sum4 a

%runElab derive "Sum4" [Generic,Meta,Show,Eq]

ToJSON a => ToJSON (Sum4 a) where
  toJSON = genToJSON TwoElemArray

FromJSON a => FromJSON (Sum4 a) where
  fromJSON = genFromJSON TwoElemArray

-- this sum will be encoded as a tagged object with custom
-- names for the tag and content field
data Sum5 : (a : Type) -> Type where
  Con51 : (name : String) -> (age : Bits32) -> (female : Bool) -> Sum5 a
  Con52 : (treasure : List a) -> (weight : Bits64) -> Sum5 a
  Con53 : (foo : Maybe a) -> (bar : Either Bool a) -> Sum5 a

%runElab derive "Sum5" [Generic,Meta,Show,Eq]

ToJSON a => ToJSON (Sum5 a) where
  toJSON = genToJSON (TaggedObject "v" "c")

FromJSON a => FromJSON (Sum5 a) where
  fromJSON = genFromJSON (TaggedObject "v" "c")

-- since records have only one constructor, they can be encoded
-- without having to care about the different techniques to
-- distinguish between constructors
record ARecord where
  constructor MkRecord
  anInt   : Integer
  perhaps : Maybe (Sum Int)
  foo     : Either String Bool

%runElab derive "ARecord" [Generic,Meta,Show,Eq,RecordToJSON,RecordFromJSON]

-- enum types (all nullary constructors) can be encoded just
-- as a string representing the constructor's name
data Weekday = Monday
             | Tuesday
             | Wednesday
             | Thursday
             | Friday
             | Saturday
             | Sunday

%runElab derive "Weekday" [Generic,Meta,Show,Eq,EnumToJSON,EnumFromJSON]

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

bits8All : Gen Bits8
bits8All = bits8 $ linear 0 255

bits16All : Gen Bits16
bits16All = bits16 $ exponential 0 65535

bits32All : Gen Bits32
bits32All = bits32 $ exponential 0 4294967295

bits64All : Gen Bits64
bits64All = bits64 $ exponential 0 18446744073709551615

unicode16 : Gen Char
unicode16 = charc '\0' '\65535'

doubleE100 : Gen Double
doubleE100 = double $ exponentialFrom 0 (-1.0e100) 1.0e100

intAll : Gen Int
intAll = int $ exponential (-9223372036854775808) 9223372036854775807

integer128 : Gen Integer
integer128 = integer $ exponentialFrom 0 (-0x100000000000000000000000000000000) 0x100000000000000000000000000000000

nat128 : Gen Nat
nat128 = nat $ exponential @{FastNatOrd} 0 0x100000000000000000000000000000000

list20 : Gen a -> Gen (List a)
list20 = list (linear 0 20)

list1_20 : Gen a -> Gen (List1 a)
list1_20 = list1 (linear 1 20)

string20 : Gen Char -> Gen String
string20 = string $ linear 0 20

string20Ascii : Gen String
string20Ascii = string20 ascii

string20Unicode16 : Gen String
string20Unicode16 = string20 unicode16

vect13 : Gen a -> Gen (Vect 13 a)
vect13 = vect 13

newtype : Gen String
newtype = string20 unicode16

sumSop : Gen (SOP I [ [String,Bits32,Bool]
                    , [List Int, Bits64]
                    , [Maybe Int, Either Bool Int]
                    ])
sumSop = sop $ MkPOP [ [ string20 alphaNum, bits32All, bool ]
                       , [ list20 intAll, bits64All ]
                       , [ maybe intAll, either bool intAll ]
                       ]

sum : Gen (Sum Int)
sum = map to sumSop

rec : Gen ARecord
rec = map to $ sop $
      MkPOP [[integer128, maybe sum, either string20Unicode16 bool]]

weekday : Gen Weekday
weekday = element [Monday,Tuesday,Wednesday,Thursday,Friday,Saturday,Sunday]

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

roundTrip : Eq a => FromJSON a => ToJSON a => Show a => Gen a -> Property
roundTrip g = property $ do v <- forAll g
                            let enc = encode v
                            footnote enc
                            Right v === decode enc

prop_unit : Property
prop_unit = roundTrip $ pure ()

prop_bits8 : Property
prop_bits8 = roundTrip bits8All

prop_bits16 : Property
prop_bits16 = roundTrip bits16All

prop_bits32 : Property
prop_bits32 = roundTrip bits32All

prop_bits64 : Property
prop_bits64 = roundTrip bits64All

prop_bool : Property
prop_bool = roundTrip bool

prop_char : Property
prop_char = roundTrip unicode16

prop_double : Property
prop_double = roundTrip doubleE100

prop_either : Property
prop_either = roundTrip $ either bits8All ascii

prop_int : Property
prop_int = roundTrip intAll

prop_integer : Property
prop_integer = roundTrip integer128

prop_list : Property
prop_list = roundTrip $ list20 bits8All

prop_list1 : Property
prop_list1 = roundTrip $ list1_20 unicode16

prop_maybe : Property
prop_maybe = roundTrip $ maybe (either bool bits32All)

prop_nat : Property
prop_nat = roundTrip @{FastNatEq} nat128

prop_np : Property
prop_np = roundTrip $ np [ integer128, bool, unicode16, maybe string20Ascii ]

prop_ns : Property
prop_ns = roundTrip $ ns [ integer128, bool, unicode16, maybe string20Ascii ]

prop_pair : Property
prop_pair = roundTrip [| (,) (list1_20 bool) (maybe ascii) |]

prop_rec : Property
prop_rec = roundTrip rec

prop_newtype : Property
prop_newtype = roundTrip newtype

prop_string : Property
prop_string = roundTrip $ string20 unicode16

prop_sum : Property
prop_sum = roundTrip {a = Sum Int} (map to sumSop)

prop_sum2 : Property
prop_sum2 = roundTrip {a = Sum2 Int} (map to sumSop)

prop_sum3 : Property
prop_sum3 = roundTrip {a = Sum3 Int} (map to sumSop)

prop_sum4 : Property
prop_sum4 = roundTrip {a = Sum4 Int} (map to sumSop)

prop_sum5 : Property
prop_sum5 = roundTrip {a = Sum5 Int} (map to sumSop)

prop_vect : Property
prop_vect = roundTrip $ vect13 intAll

prop_weekday : Property
prop_weekday = roundTrip weekday

main : IO ()
main = ignore . checkGroup . withTests 10000 $ MkGroup "JSON" [
            ("prop_bits8", prop_bits8)
          , ("prop_bits16", prop_bits16)
          , ("prop_bits32", prop_bits32)
          , ("prop_bits64", prop_bits64)
          , ("prop_bool", prop_bool)
          , ("prop_char", prop_char)
          , ("prop_double", prop_double)
          , ("prop_either", prop_either)
          , ("prop_int", prop_int)
          , ("prop_integer", prop_integer)
          , ("prop_list", prop_list)
          , ("prop_list1", prop_list1)
          , ("prop_maybe", prop_maybe)
          , ("prop_nat", prop_nat)
          , ("prop_newtype", prop_newtype)
          , ("prop_np", prop_np)
          , ("prop_ns", prop_ns)
          , ("prop_pair", prop_pair)
          , ("prop_rec", prop_rec)
          , ("prop_string", prop_string)
          , ("prop_sum", prop_sum)
          , ("prop_sum2", prop_sum2)
          , ("prop_sum3", prop_sum3)
          , ("prop_sum4", prop_sum4)
          , ("prop_sum5", prop_sum5)
          , ("prop_unit", prop_unit)
          , ("prop_vect", prop_vect)
          , ("prop_weekday", prop_weekday)
          ]
