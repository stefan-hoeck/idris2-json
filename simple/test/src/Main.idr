module Main

import Data.List.Quantifiers as LQ
import Data.SortedMap
import Data.Vect.Quantifiers as VQ
import Hedgehog
import JSON.Simple.Derive

%language ElabReflection

--------------------------------------------------------------------------------
--          Elab Deriving
--------------------------------------------------------------------------------

-- example newtype
record Newtype where
  constructor MkNewtype
  field : String

%runElab derive "Newtype" [Show,Eq,ToJSON,FromJSON]

-- example enum
data Elem = H | He | B | C | N | O | F | Ne

%runElab derive "Elem" [Show, Eq, Ord, ToJSON, FromJSON]

-- sum type with default encoding behavior: this will
-- be encoded as a mapping from constructor argument names
-- to values including a special field called "tag" with the
-- encoded constructor name.
data Sum : (a : Type) -> Type where
  Con1 : (name : String) -> (age : Bits32) -> (female : Bool) -> Sum a
  Con2 : (treasure : List a) -> (weight : Bits64) -> Sum a
  Con3 : (foo : Maybe a) -> (bar : Either Bool a) -> Sum a
  Con4 : (map : SortedMap Nat Bool) -> Sum a
  Con5 : Either Bool String -> Sum a

%runElab derive "Sum" [Show,Eq,ToJSON,FromJSON]

-- this sum type will be encoded in the same manner as `Sum`
-- but without the additional "tag" field: This should
-- only be used if not two constructors have the same
-- type and field names.
data Sum2 : (a : Type) -> Type where
  Con21 : (name : String) -> (age : Bits32) -> (female : Bool) -> Sum2 a
  Con22 : (treasure : List a) -> (weight : Bits64) -> Sum2 a
  Con23 : (foo : Maybe a) -> (bar : Either Bool a) -> Sum2 a
  Con24 : (map : SortedMap Nat Bool) -> Sum2 a
  Con25 : Either Bool String -> Sum2 a

opts2 : Options
opts2 = MkOptions UntaggedValue True False True id id

%runElab derive "Sum2" [Show,Eq,customToJSON Export opts2, customFromJSON Export opts2]

-- this sum type will be encoded as `Sum` but instead of adding
-- a "tag" for the constructor name, it will be wrapped up
-- as a single field object, the field being named as the
-- constructor used.
data Sum3 : (a : Type) -> Type where
  Con31 : (name : String) -> (age : Bits32) -> (female : Bool) -> Sum3 a
  Con32 : (treasure : List a) -> (weight : Bits64) -> Sum3 a
  Con33 : Maybe a -> Either Bool a -> Sum3 a
  Con34 : (map : SortedMap Nat Bool) -> Sum3 a
  Con35 : Either Bool String -> Sum3 a

opts3 : Options
opts3 = MkOptions ObjectWithSingleField True False True id id

%runElab derive "Sum3" [Show,Eq,customToJSON Export opts3, customFromJSON Export opts3]

-- this sum will be encoded as an array of two elements:
-- the first corresponding to the constructor name, the second
-- to the encoded value.
data Sum4 : (a : Type) -> Type where
  Con41 : (name : String) -> (age : Bits32) -> (female : Bool) -> Sum4 a
  Con42 : (treasure : List a) -> (weight : Bits64) -> Sum4 a
  Con43 : Maybe a -> Either Bool a -> Sum4 a
  Con44 : (map : SortedMap Nat Bool) -> Sum4 a
  Con45 : Either Bool String -> Sum4 a

opts4 : Options
opts4 = MkOptions TwoElemArray True False True id id

%runElab derive "Sum4" [Show,Eq,customToJSON Export opts4, customFromJSON Export opts4]

-- this sum will be encoded as a tagged object with custom
-- names for the tag and content field
data Sum5 : (a : Type) -> Type where
  Con51 : (name : String) -> (age : Bits32) -> (female : Bool) -> Sum5 a
  Con52 : (treasure : List a) -> (weight : Bits64) -> Sum5 a
  Con53 : Maybe a -> Either Bool a -> Sum5 a
  Con54 : SortedMap Nat Bool -> Sum5 a
  Con55 : Either Bool String -> Sum5 a

opts5 : Options
opts5 = MkOptions (TaggedObject "v" "c") True False True id id

%runElab derive "Sum5" [Show,Eq,customToJSON Export opts5, customFromJSON Export opts5]

-- since records have only one constructor, they can be encoded
-- without having to care about the different techniques to
-- distinguish between constructors
record ARecord where
  constructor MkRec
  anInt   : Integer
  perhaps : Maybe (Sum Nat)
  foo     : Either String Bool

%runElab derive "ARecord" [Show,Eq,ToJSON,FromJSON]

-- unless we decide to not unwrap record types
record AnotherRecord where
  constructor MkARec
  anInt   : Integer
  perhaps : Maybe (Sum Nat)
  foo     : Either String Bool

opts6 : Options
opts6 = MkOptions (TaggedObject "v" "c") True False False id id

%runElab derive "AnotherRecord" [Show,Eq,customToJSON Export opts6, customFromJSON Export opts6]

-- enum types (all nullary constructors) can be encoded just
-- as a string representing the constructor's name
data Weekday =
    Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday

%runElab derive "Weekday" [Show,Eq,ToJSON,FromJSON]

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

toSum2 : Sum a -> Sum2 a
toSum2 (Con1 n a f) = Con21 n a f
toSum2 (Con2 t w)   = Con22 t w
toSum2 (Con3 f b)   = Con23 f b
toSum2 (Con4 m)     = Con24 m
toSum2 (Con5 m)     = Con25 m

toSum3 : Sum a -> Sum3 a
toSum3 (Con1 n a f) = Con31 n a f
toSum3 (Con2 t w)   = Con32 t w
toSum3 (Con3 f b)   = Con33 f b
toSum3 (Con4 m)     = Con34 m
toSum3 (Con5 m)     = Con35 m

toSum4 : Sum a -> Sum4 a
toSum4 (Con1 n a f) = Con41 n a f
toSum4 (Con2 t w)   = Con42 t w
toSum4 (Con3 f b)   = Con43 f b
toSum4 (Con4 m)     = Con44 m
toSum4 (Con5 m)     = Con45 m

toSum5 : Sum a -> Sum5 a
toSum5 (Con1 n a f) = Con51 n a f
toSum5 (Con2 t w)   = Con52 t w
toSum5 (Con3 f b)   = Con53 f b
toSum5 (Con4 m)     = Con54 m
toSum5 (Con5 m)     = Con55 m

bits8All : Gen Bits8
bits8All = bits8 $ linear 0 255

bits16All : Gen Bits16
bits16All = bits16 $ exponential 0 65535

bits32All : Gen Bits32
bits32All = bits32 $ exponential 0 4294967295

bits64All : Gen Bits64
bits64All = bits64 $ exponential 0 18446744073709551615

unicode16 : Gen Char
unicode16 = noSpecial <$> charc '\0' '\65535'
  where
    noControl : Char -> Char
    noControl c = if isControl c then ' ' else c

    noHighSurrogate : Char -> Char
    noHighSurrogate c =
      let idx = ord c
      in if idx >= 0xD800 && idx <= 0xDBFF then ' ' else c

    noLowSurrogate : Char -> Char
    noLowSurrogate c =
      let idx = ord c
      in if idx >= 0xDC00 && idx <= 0xDFFF then ' ' else c

    noSpecial : Char -> Char
    noSpecial = noControl . noHighSurrogate . noLowSurrogate

doubleE100 : Gen Double
doubleE100 = double $ exponentialFrom 0 (-1.0e100) 1.0e100

intAll : Gen Int
intAll = int $ exponential (-9223372036854775808) 9223372036854775807

integer128 : Gen Integer
integer128 = integer $ exponentialFrom 0 (-0x100000000000000000000000000000000) 0x100000000000000000000000000000000

nat128 : Gen Nat
nat128 = nat $ exponential 0 0x100000000000000000000000000000000

list20 : Gen a -> Gen (List a)
list20 = list (linear 0 20)

list1_20 : Gen a -> Gen (List1 a)
list1_20 = list1 (linear 1 20)

string20 : Gen Char -> Gen String
string20 = string $ linear 0 20

string20Ascii : Gen String
string20Ascii = string20 printableAscii

string20Unicode16 : Gen String
string20Unicode16 = string20 unicode16

vect13 : Gen a -> Gen (Vect 13 a)
vect13 = vect 13

newtype : Gen Newtype
newtype = MkNewtype <$> string20 unicode16

sum : Gen a -> Gen (Sum a)
sum g = choice
  [ [| Con1 string20Ascii bits32All bool |]
  , [| Con2 (list20 g) bits64All |]
  , [| Con3 (maybe g) (either bool g) |]
  , map Con4 smap
  , map Con5 (either bool string20Ascii)
  ]
  where
    pair : Gen (Nat,Bool)
    pair = [| MkPair (nat $ linear 0 50) bool |]

    smap : Gen (SortedMap Nat Bool)
    smap = SortedMap.fromList <$> list (linear 0 20) pair

rec : Gen ARecord
rec = [| MkRec integer128 (maybe $ sum nat128) (either string20Unicode16 bool) |]

anotherRec : Gen AnotherRecord
anotherRec = [| MkARec integer128 (maybe $ sum nat128) (either string20Unicode16 bool) |]

weekday : Gen Weekday
weekday = element [Monday,Tuesday,Wednesday,Thursday,Friday,Saturday,Sunday]

elem : Gen Elem
elem = element [H,He,B,C,N,O,F,Ne]

[AllLEq] LQ.All.All (Eq . p) ts => Eq (LQ.All.All p ts) where
  (==) [] [] = True
  (==) @{_ :: _} (h1::t1) (h2::t2) = h1 == h2 && t1 == t2

[AllVEq] VQ.All.All (Eq . p) ts => Eq (VQ.All.All p ts) where
  (==) [] [] = True
  (==) @{_ :: _} (h1::t1) (h2::t2) = h1 == h2 && t1 == t2

all : Gen (HList [Elem, ARecord])
all = [| (\x,y => [x,y]) elem rec |]

allv : Gen (HVect [Elem, ARecord])
allv = [| (\x,y => [x,y]) elem rec |]

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------
--
roundTrip : Eq a => FromJSON a => ToJSON a => Show a => Gen a -> Property
roundTrip g = property $ do
  v <- forAll g
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
prop_either = roundTrip $ either bits8All printableAscii

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
prop_nat = roundTrip nat128

prop_pair : Property
prop_pair = roundTrip [| (,) (list1_20 bool) (maybe printableAscii) |]

prop_rec : Property
prop_rec = roundTrip rec

prop_anotherRec : Property
prop_anotherRec = roundTrip anotherRec

prop_anotherRecEnc : Property
prop_anotherRecEnc = property1 $
  encode (MkARec 12 Nothing (Right False)) ===
  #"{"v":"MkARec","c":{"anInt":12,"perhaps":null,"foo":{"Right":false}}}"#

prop_newtype : Property
prop_newtype = roundTrip newtype

prop_string : Property
prop_string = roundTrip $ string20 unicode16

prop_sum : Property
prop_sum = roundTrip (sum bits8All)

prop_sum2 : Property
prop_sum2 = roundTrip (map toSum2 $ sum bits16All)

prop_sum3 : Property
prop_sum3 = roundTrip (map toSum3 $ sum bits16All)

prop_sum4 : Property
prop_sum4 = roundTrip (map toSum4 $ sum bits16All)

prop_sum5 : Property
prop_sum5 = roundTrip (map toSum4 $ sum bits16All)

prop_vect : Property
prop_vect = roundTrip $ vect13 intAll

prop_weekday : Property
prop_weekday = roundTrip weekday

prop_all : Property
prop_all = roundTrip @{AllLEq} all

prop_allv : Property
prop_allv = roundTrip @{AllVEq} allv

main : IO ()
main = test . pure $
  MkGroup
    "JSON"
    [ ("prop_bits8", prop_bits8)
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
    , ("prop_pair", prop_pair)
    , ("prop_rec", prop_rec)
    , ("prop_anotherRec", prop_anotherRec)
    , ("prop_anotherRecEnc", prop_anotherRecEnc)
    , ("prop_string", prop_string)
    , ("prop_sum", prop_sum)
    , ("prop_sum2", prop_sum2)
    , ("prop_sum3", prop_sum3)
    , ("prop_sum4", prop_sum4)
    , ("prop_sum5", prop_sum5)
    , ("prop_unit", prop_unit)
    , ("prop_vect", prop_vect)
    , ("prop_weekday", prop_weekday)
    , ("prop_all", prop_all)
    , ("prop_allv", prop_allv)
    ]
