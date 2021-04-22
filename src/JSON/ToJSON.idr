||| Interface and utilities for encoding Idris2 values to JSON
||| via an entermediate `Value` representation.
|||
||| For regular algebraic data types, implementations can automatically
||| be derived using elaborator reflection.
|||
||| Operators and functionality strongly influenced by Haskell's aeson
||| library
module JSON.ToJSON

import Data.List1
import Data.Vect
import JSON.Value
import Generics.Derive

%language ElabReflection

public export
interface ToJSON a where
  toJSON : forall v,obj . Value v obj => a -> v

infixr 8 .=

export
(.=) : ToJSON a => Value v obj => String -> a -> (String,v)
s .= val = (s, toJSON val)

export
encodeVia : (0 v : Type) -> Value v obj => ToJSON a => a -> String
encodeVia v val = stringify $ toJSON {v} val

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

export
ToJSON Void where
  toJSON x impossible

export
ToJSON String where toJSON = string

export
ToJSON Char where toJSON = string . singleton

export
ToJSON Double where toJSON = number

export
ToJSON Bits8 where toJSON = smallInteger . cast

export
ToJSON Bits16 where toJSON = smallInteger . cast

export
ToJSON Bits32 where toJSON = smallInteger . cast

export
ToJSON Bits64 where toJSON = largeInteger . cast

export
ToJSON Int where toJSON = largeInteger . cast

export
ToJSON Integer where toJSON = largeInteger

export
ToJSON Nat where toJSON = largeInteger . natToInteger

export
ToJSON Bool where toJSON = boolean

export
ToJSON a => ToJSON (Maybe a) where
  toJSON Nothing  = null
  toJSON (Just a) = toJSON a

export
ToJSON a => ToJSON (List a) where
  toJSON = array . map toJSON

export
ToJSON a => ToJSON (List1 a) where
  toJSON = toJSON . forget

export
ToJSON a => ToJSON (Vect n a) where
  toJSON = toJSON . toList

export
ToJSON () where
  toJSON () = array Nil

export
(ToJSON a, ToJSON b) => ToJSON (Either a b) where
  toJSON (Left a)  = object ["Left"  .= a]
  toJSON (Right b) = object ["Right" .= b]

--------------------------------------------------------------------------------
--          SOP Implementations
--------------------------------------------------------------------------------

np : Value v obj => NP (ToJSON . f) ks => NP f ks -> v
np = array . collapseNP . hcmap (ToJSON . f) toJSON

export
NP (ToJSON . f) ks => ToJSON (NP f ks) where
  toJSON = np

export
(ToJSON a, ToJSON b) => ToJSON (a,b) where
  toJSON (a,b) = toJSON $ the (NP I _) [a,b]

-- TODO: This should go as a utility or interface to idris2-sop
export
unfoldNP : NP f ks -> (a -> a) -> a -> NP (K a) ks
unfoldNP []     _ _ = []
unfoldNP (_::t) f x = x :: unfoldNP t f (f x)

export
indices : NP f ks ->  NP (K Bits32) ks
indices np = unfoldNP np (+1) (the Bits32 0)

ns : Value v obj => (all : NP (ToJSON . f) ks) => NS f ks -> v
ns = collapseNS . hcliftA2 (ToJSON . f) enc (indices all)
  where enc : ToJSON (f a) => Bits32 -> f a -> v
        enc ix v = object [show ix .= v]

export
NP (ToJSON . f) ks => ToJSON (NS f ks) where
  toJSON = ns

--------------------------------------------------------------------------------
--          Elab Deriving
--------------------------------------------------------------------------------

-- Converts a single applied constructor, without pairing it
-- with its name.
toJSONC1 : Value v obj => NP (ToJSON . f) ks => ConInfo ks -> NP f ks -> v
toJSONC1 info args = maybe (toJSON args) encRecord (argNames info)

  where encRecord : NP (K String) ks -> v
        encRecord ns = object (collapseNP $ hcliftA2 (ToJSON . f) (.=) ns args)

toJSONSOP1 : Value v obj => NP (ToJSON . f) ks => TypeInfo [ks] -> SOP f [ks] -> v
toJSONSOP1 (MkTypeInfo _ _ (v :: [])) (MkSOP (Z x)) = toJSONC1 v x
toJSONSOP1 (MkTypeInfo _ _ (v :: [])) (MkSOP (S x)) impossible

-- Converts a single applied constructor, pairing it with its name
toJSONC : Value v obj => NP (ToJSON . f) ks => ConInfo ks -> NP f ks -> v
toJSONC i@(MkConInfo _ n _) np = object [(n, toJSONC1 i np)]

toJSONSOP :  Value v obj
          => (all : POP (ToJSON . f) kss)
          => TypeInfo kss -> SOP f kss -> v
toJSONSOP {all = MkPOP _} (MkTypeInfo _ _ cons) =
  collapseNS . hcliftA2 (NP $ ToJSON . f) toJSONC cons . unSOP

export
genToJSON1 : Value v obj => Meta a [ks] => NP ToJSON ks => a -> v
genToJSON1 = toJSONSOP1 (metaFor a) . from

export
genToJSON : Value v obj => Meta a code => POP ToJSON code => a -> v
genToJSON = toJSONSOP (metaFor a) . from

public export
mkToJSON :  {0 a : Type}
         -> (toJSON : forall v,obj . Value v obj => a -> v) -> ToJSON a
mkToJSON = %runElab check (var $ singleCon "ToJSON")

namespace Derive

  ||| Derives a `ToJSON` implementation for the given data type
  export
  ToJSON : DeriveUtil -> InterfaceImpl
  ToJSON g = MkInterfaceImpl "ToJSON" Export []
                    `(mkToJSON genToJSON)
                    (implementationType `(ToJSON) g)

  ||| Derives a `ToJSON` implementation for the given single-constructor
  ||| data type
  export
  ToJSON1 : DeriveUtil -> InterfaceImpl
  ToJSON1 g = MkInterfaceImpl "ToJSON" Export []
                    `(mkToJSON genToJSON1)
                    (implementationType `(ToJSON) g)
