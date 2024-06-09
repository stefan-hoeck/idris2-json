# Idris2-json: Tutorial

This library offers functionality for writing marshallers
from and to JSON in Idris2. While it is kept in the spirit
of [Haskell's aeson](https://hackage.haskell.org/package/aeson),
there is one key difference: We abstract over the `Value`
representation, allowing greater flexibility in how data
is encoded and decoded. While we will use the `JSON` type
from `Language.JSON` in this tutorial, users on one of the
JavaScript backends might opt for going via some (immutable)
wrapper around JavaScript `object`s, thus having access
to the highly optimized parser and stringifier of the backend
(this is what [idris2-dom](https://github.com/stefan-hoeck/idris2-dom)
does). This tutorial is a literate Idris2 file, hence:

```idris
module Docs.Tutorial

import JSON.Derive
import Data.String

%language ElabReflection
```

## Before we begin

This tutorial will make heavy use of the generic
interfaces from [idris2-sop](https://github.com/stefan-hoeck/idris2-sop).
If these concepts are new to you, you can read about
them in several [tutorial blog posts](https://github.com/stefan-hoeck/idris2-sop/blob/main/docs/src/Docs/Index.md).
Also, if you'd like to learn more about the elaborator scripts
we use, there are again several
[tutorials from the elab-util project](https://github.com/stefan-hoeck/idris2-elab-util/blob/main/src/Doc/Index.md).

Now, after this shameless self-advertising, let us begin with
the JSON stuff.

## Writing `ToJSON` Encoders

This library comes with encoders for many data types from
the core libraries already implemented. As an example, we
will define a simple `Hero` data type (I keep coming back
to these) from a role playing game:

```idris
data Race = Human | Halfling | Dwarf | Elf | HalfOrc

%runElab derive "Race" [Show,Eq]

ToJSON Race where toJSON = string . show

data Class = Fighter | Thief | Wizard | Cleric

%runElab derive "Class" [Show,Eq]

ToJSON Class where toJSON = string . show

record Hero where
  constructor MkHero
  name   : String
  age    : Nat
  race   : Race
  class  : Class
  allies : List Hero

%runElab derive "Hero" [Show,Eq]

ToJSON Hero where
  toJSON h =
    object
      [ jpair "name"   h.name
      , jpair "age"    h.age
      , jpair "race"   h.race
      , jpair "class"  h.class
      , jpair "allies" h.allies
      ]
```

So, that was very easy. For encoding, we use the functions
from the `JSON.Value.Encoder` interface together with
`jpair`, for encoding key-value pairs.
Most of the time, this is so straight forward that we can derive
these instances automatically:


```idris
data MonsterClass = Imp | Goblin | Orc | Dragon

%runElab derive "MonsterClass" [Show,Eq,ToJSON]

record Villain where
  constructor MkVillain
  name    : String
  hp      : Nat
  class   : MonsterClass
  cronies : List Villain

%runElab derive "Villain" [Show,Eq,ToJSON]

gorgar : Villain
gorgar = MkVillain "Gorgar" 2000 Dragon [MkVillain "Igor" 10 Imp []]
```

Feel free to load this tutorial in a REPL session and give
the encoders a try: `rlwrap idris2 --find-ipkg src/Doc/Tutorial.md`:

```repl
:exec putStrLn $ encode gorgar
```

## Customizing Encoders

Automatically derived encoders and decoders can be customized
via the `JSON.Option` data type. For instance, we can encode
an enum type by just taking the first three letters of its
names:

### Newtypes
Function `genNewtyeToJSON` encodes a newtype (one constructor, one field)
by just extracting the wrapped value and encoding that. Implementations
can also be derived using elab reflection by using `NewtypeToJSON`.

### Enums
For enumerations (all nullary constructors), there are functions
`genEnumToJSON` and `genEnumToJSON'`, the latter taking an additional
function argument for adjusting constructor names before encoding
them. `genEnumToJSON` can also be derived automatically via
`EnumToJSON` as shown for `MonsterClass` above.

Examples:

```idris

take : Nat -> String -> String
take n = pack . take n . unpack

toLower : Options
toLower = {constructorTagModifier := toLower} defaultOptions

take3 : Options
take3 = {constructorTagModifier := take 3 . toUpper} defaultOptions

data Gender = Female | Male | NonBinary

%runElab derive "Gender" [Show,Eq,Ord,customToJSON toLower]

data Weekday =
    Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday

%runElab derive "Weekday" [Show,Eq,Ord,customToJSON take3]
```

Likewise, we can adjust the generated field names for data constructors
where all arguments have user-defined names.

Examples:

```idris

take4 : Options
take4 = {fieldNameModifier := take 4} defaultOptions

data Treasure : Type where
  MkTreasure :  (description : String)
             -> (weight : Nat)
             -> (value  : Nat)
             -> Treasure

%runElab derive "Treasure" [Show,Eq,Ord,customToJSON take4]

record Spell where
  constructor MkSpell
  name       : String
  difficulty : Nat
  cost       : Nat

%runElab derive "Spell" [Show,Eq,Ord,customToJSON take4]
```

### Arbitrary Sums
Sum types offer the greatest flexibility about how they
can be encoded. There is a `SumEncoding` data type in `JSON.Option`,
the doc strings of which explain in detail the different options we
have. Use `customToJSON` together with one of these options to encode
an arbitrary sum type.

Example:

```idris
weaponOptions : Options
weaponOptions = {sum := TwoElemArray} toLower

data Weapon : Type where
  Sword : (name : String) -> (weight : Nat) -> (value : Nat) -> Weapon
  Club : (weight : Nat) -> Weapon
  Rock : (material : String) -> (weight : Nat) -> Weapon

%runElab derive "Weapon" [Show,Eq,Ord,customToJSON weaponOptions]
```

### Writing your own Derivable Encoders

If a certain pattern of customized encoders keeps coming up,
it is very easy to write your own autoderivable version
using `customToJSON:

Example:

```idris
MyToJSON : List Name -> ParamTypeInfo -> Res (List TopLevel)
MyToJSON =
  customToJSON (MkOptions (TaggedObject "t" "c") False True toLower (take 3))

data NPC : Type where
  Commoner : (name : String) -> (profession : String) -> NPC
  Noblewoman : (name : String) -> (status : String) -> NPC
  Demigod : (name : String) -> (attributes : List String) -> NPC

%runElab derive "NPC" [Show,Eq,Ord,MyToJSON]
```
