module JSON.Option

import Derive.Prelude

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

%runElab derive "SumEncoding" [Show,Eq]

||| Corresponds to `TaggedObject "tag" "contents"`
public export
defaultTaggedObject : SumEncoding
defaultTaggedObject = TaggedObject "tag" "contents"

public export
record Options where
  constructor MkOptions
  sum                        : SumEncoding
  replaceMissingKeysWithNull : Bool
  constructorTagModifier     : String -> String
  fieldNameModifier          : String -> String

public export
defaultOptions : Options
defaultOptions = MkOptions defaultTaggedObject False id id

public export
fieldName : Named a => Options -> a -> String
fieldName o v = o.fieldNameModifier v.nameStr

public export
fieldNamePrim : Named a => Options -> a -> TTImp
fieldNamePrim o v = primVal (Str $ fieldName o v)

public export
constructorTag : Named a => Options -> a -> String
constructorTag o v = o.constructorTagModifier v.nameStr

public export
constructorTagPrim : Named a => Options -> a -> TTImp
constructorTagPrim o v = primVal (Str $ constructorTag o v)

--------------------------------------------------------------------------------
--          Constructors
--------------------------------------------------------------------------------

public export
data ArgInfo : Type where
  Const  : ArgInfo
  Fields : SnocList (BoundArg 2 RegularNamed) -> ArgInfo
  Values : SnocList (BoundArg 2 Regular) -> ArgInfo

public export
record DCon where
  constructor DC
  name    : Name
  bound   : TTImp
  applied : TTImp
  tag     : TTImp
  args    : ArgInfo

argInfo : SnocList (BoundArg 2 Regular) -> ArgInfo
argInfo [<]  = Const
argInfo sx   = maybe (Values sx) Fields $ traverse toNamed sx

public export
isConst : DCon -> Bool
isConst (DC _ _ _ _ Const) = True
isConst _                  = False

public export
toRegular : BoundArg n RegularNamed -> BoundArg n Regular
toRegular (BA arg vars prf) = BA arg vars %search

export
dcon : Options -> Con n vs -> DCon
dcon o c =
  let xs  := freshNames "x" c.arty
      ys  := freshNames "y" c.arty
      bc  := bindCon c xs
      ac  := `(Right ~(applyCon c xs))
      sx  := boundArgs regular c.args [xs,ys]
      tag := constructorTagPrim o c
  in DC c.name bc ac tag $ argInfo sx
