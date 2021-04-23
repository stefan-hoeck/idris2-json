module JSON.Option

import Generics.Derive

%language ElabReflection

||| Specifies how to encode constructors of a sum datatype.
public export
data SumEncoding : Type where
  ||| Constructor names won't be encoded. Instead only the contents of the
  ||| constructor will be encoded as if the type had a single constructor. JSON
  ||| encodings have to be disjoint for decoding to work properly.
  |||
  ||| When decoding, constructors are tried in the order of definition. If some
  ||| encodings overlap, the first one defined will succeed.
  |||
  ||| Note: Nullary constructors are encoded as strings (using
  ||| constructorTagModifier).  Having a nullary constructor
  ||| alongside a single field constructor that encodes to a
  ||| string leads to ambiguity.
  |||
  ||| Note: Only the last error is kept when decoding, so in the case of
  ||| malformed JSON, only an error for the last constructor will be reported.
  UntaggedValue         : SumEncoding

  ||| A constructor will be encoded to an object with a single field named
  ||| after the constructor tag (modified by the constructorTagModifier) which
  ||| maps to the encoded contents of the constructor.
  ObjectWithSingleField : SumEncoding

  ||| A constructor will be encoded to a 2-element array where the first
  ||| element is the tag of the constructor (modified by the constructorTagModifier)
  ||| and the second element the encoded contents of the constructor.
  TwoElemArray          : SumEncoding

  ||| A constructor will be encoded to an object with a field `tagFieldName`
  ||| which specifies the constructor tag (modified by the
  ||| constructorTagModifier). If the constructor is a record the
  ||| encoded record fields will be unpacked into this object. So
  ||| make sure that your record doesn't have a field with the
  ||| same label as the tagFieldName.  Otherwise the tag gets
  ||| overwritten by the encoded value of that field! If the constructor
  ||| is not a record the encoded constructor contents will be
  ||| stored under the contentsFieldName field.
  TaggedObject          :  (tagFieldName : String)
                        -> (contentsFieldName : String)
                        -> SumEncoding

%runElab derive "SumEncoding" [Generic,Meta,Show,Eq]

||| Corresponds to `TaggedObject "tag" "contents"`
public export
defaultTaggedObject : SumEncoding
defaultTaggedObject = TaggedObject "tag" "contents"

public export
adjustConnames : (String -> String) -> TypeInfo' k kss -> TypeInfo' k kss
adjustConnames f = record { constructors $= mapNP adjCon }
  where adjCon : ConInfo_ k ks -> ConInfo_ k ks
        adjCon (MkConInfo ns n fs) = MkConInfo ns (f n) fs

public export
adjustInfo :  (adjFields : String -> String)
           -> (adjCons : String -> String)
           -> TypeInfo' k kss
           -> TypeInfo' k kss
adjustInfo af ac = record { constructors $= mapNP adjCon }
  where adjArg : ArgName -> ArgName
        adjArg (NamedArg ix n) = NamedArg ix $ af n
        adjArg arg = arg

        adjCon : ConInfo_ k ks -> ConInfo_ k ks
        adjCon (MkConInfo ns n fs) = MkConInfo ns (ac n) (mapNP adjArg fs)

public export
adjustFieldNames : (String -> String) -> TypeInfo' k kss -> TypeInfo' k kss
adjustFieldNames f = adjustInfo f id

||| Witness that a list of list of types (representing the
||| constructors and fields of an ADT) represents an enum type, i.e.
||| that all constructors are nullary.
public export
data EnumType : (kss : List $ List k) -> Type where
  EZ : EnumType Nil
  ES : EnumType kss -> EnumType ([] :: kss)

public export
0 enumTail : EnumType (ks :: kss) -> EnumType kss
enumTail (ES x) = x

public export
nullaryInjections :  NP_ (List k) (ConInfo_ k) kss
                  -> (0 et : EnumType kss)
                  -> NP_ (List k) (K (NS_ (List k) (NP f) kss)) kss
nullaryInjections []         _  = []
nullaryInjections (MkConInfo _ _ [] :: vs) es =
  Z [] :: mapNP (\ns => S ns) (nullaryInjections vs (enumTail es))
