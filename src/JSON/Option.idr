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

||| Options that specify how to encode/decode your datatype to/from JSON.
public export
record Options where
  constructor MkOptions
  ||| Function applied to field labels. Handy for removing common record
  ||| prefixes for example.
  fieldLabelModifier     : String -> String

  ||| Function applied to constructor tags which could be handy for
  ||| lower-casing them for example.
  constructorTagModifier : String -> String

  ||| If True the constructors of a datatype, with all nullary constructors,
  ||| will be encoded to just a string with the constructor tag. If False the
  ||| encoding will always follow the sumEncoding.
  allNullaryToStringTag  : Bool

  ||| Specifies how to encode constructors of a sum datatype.
  sumEncoding            : SumEncoding

  ||| Hide the field name when a record constructor has only one field, like a
  ||| newtype.
  unwrapUnaryRecords     : Bool

  ||| Encode types with a single constructor as sums, so that
  ||| allNullaryToStringTag and sumEncoding apply.
  tagSingleConstructors  : Bool

||| Corresponds to
|||
||| ```idris
||| defaultOptions = MkOptions
|||                    { fieldLabelModifier      = id
|||                    , constructorTagModifier  = id
|||                    , allNullaryToStringTag   = True
|||                    , sumEncoding             = defaultTaggedObject
|||                    , unwrapUnaryRecords      = False
|||                    , tagSingleConstructors   = False
|||                    }
||| ```
public export
defaultOptions : Options
defaultOptions = MkOptions
                   { fieldLabelModifier      = id
                   , constructorTagModifier  = id
                   , allNullaryToStringTag   = True
                   , sumEncoding             = defaultTaggedObject
                   , unwrapUnaryRecords      = False
                   , tagSingleConstructors   = False
                   }
