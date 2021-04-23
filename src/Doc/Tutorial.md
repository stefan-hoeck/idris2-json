## Idris2-json: Tutorial

This library offers functionality for writing marshallers
from and to JSON in Idris2. While it is kept in the spirit
of [Haskell's aeson](https://hackage.haskell.org/package/aeson),
there is one key difference: We abstract over the `Value`
representation, allowing greater flexibility in how data
is encoded and decoded. While we will use the `JSON` type
from `Language.JSON` in this tutorial, users on one of the
Javascript backends might opt for going via some (immutable)
wrapper around Javascript `object`s, thus having access
to the highly optimized parser and stringifier of the backend
(this is what [idris2-dom](https://github.com/stefan-hoeck/idris2-dom)
does). This tutorial is a literate Idris2 file, hence:

```idris
module Doc.Tutorial

import JSON
import Generics.Derive

%language ElabReflection
```

### Writing `ToJSON` Encoders

This library comes with encoders for many data types from
the core libraries already implemented. As an example, we
will define a simple `Hero` data type (I keep coming back
to these) from a role playing game:

```idris
data Race = Human | Halfling | Dwarf | Elf | HalfOrc

%runElab derive "Race" [Generic,Meta,Show,Eq]

ToJSON Race where toJSON = string . show

data Class = Fighter | Thief | Wizard | Cleric

%runElab derive "Class" [Generic,Meta,Show,Eq]

ToJSON Class where toJSON = string . show

record Hero where
  constructor MkHero
  name   : String
  age    : Nat
  race   : Race
  class  : Class
  allies : List Hero

%runElab derive "Hero" [Generic,Meta,Show,Eq]

ToJSON Hero where
  toJSON h = object [ "name"   .= h.name
                    , "age"    .= h.age
                    , "race"   .= h.race
                    , "class"  .= h.class
                    , "allies" .= h.allies
                    ]
```

So, that was very easy. For encoding, we use the functions
from the `JSON.Value.Encoder` interface together with operator
`.=` (same as in aeson), for encoding key-value pairs.
Most of the time, this is so straight forward that we can derive
these instance automatically:


```idris
data MonsterClass = Imp | Goblin | Orc | Dragon

%runElab derive "MonsterClass" [Generic,Meta,Show,Eq,EnumToJSON]

record Villain where
  constructor MkVillain
  name    : String
  hp      : Nat
  class   : MonsterClass
  cronies : List Villain

%runElab derive "Villain" [Generic,Meta,Show,Eq,RecordToJSON]

gorgar : Villain
gorgar = MkVillain "Gorgar" 2000 Dragon [MkVillain "Igor" 10 Imp []]
```

The `RecordToJSON` encoder can be used for data types with only
on constructor. In this case, the constructor name will not
be part of the encoding. Likewise, for enum types (all nullary
constructors), we can opt for encoding just the constructor's name
(`EnumToJSON`).

Feel free to load this tutorial in a REPL session, and give
the encoders a try: `rlwrap idris2 --find-ipkg src/Doc/Tutorial.md`:

```
:exec putStrLn $ encode gorgar
```

### Customizing Encoders

There are quite a few options for customizing, how automatically derived
encoders should behave. Not all of these are available via elaborator
reflection, but it is quite easy to write your own elab decriptors
for your customized versions (see below).

#### Newtypes
Function `genNewtyeToJSON` encodes a newtype (one constructor, one field)
by just extracting the stored value and encoding that. Implementations
can also be derived using elab reflection by using `NewtypeToJSON`.

#### Enums
For enumerations (all nullary constructors), there are functions
`genEnumToJSON` and `genEnumToJSON'`, the latter taking an additional
function argument for adjusting constructor names before encoding
them. `genEnumToJSON` can also be derived automatically via
`EnumToJSON` as shown for `MonsterClass` above.

Examples:

```idris
data Gender = Female | Male | NonBinary

%runElab derive "Gender" [Generic,Meta,Eq,Ord]

ToJSON Gender where toJSON = genEnumToJSON

data Weekday = Monday
             | Tuesday
             | Wednesday
             | Thursday
             | Friday
             | Saturday
             | Sunday

%runElab derive "Weekday" [Generic,Meta,Eq,Ord]

ToJSON Weekday where
  toJSON = genEnumToJSON' (take 3 . toLower)
```

#### Records
With `records` we mean single-constructor data types here. If all
arguments have a name, `genRecordToJSON` will encode these as
a mapping from field name to encoded value, otherwise, they will
be encoded like an n-ary sum (resulting in a heterogeneous array).
If you need to adjust field names prior to encoding them,
use `genRecordToJSON'` instead.
As shown for the `Villain` data type, `ToJSON` implementations
for records can be derived by using `RecordToJSON`.

Examples:

```idris
data Treasure : Type where
  MkTreasure :  (description : String)
             -> (weight : Nat)
             -> (value  : Nat)
             -> Treasure

%runElab derive "Treasure" [Generic,Meta,Eq,Ord]

ToJSON Treasure where
  toJSON = genRecordToJSON

record Spell where
  constructor MkSpell
  name       : String
  difficulty : Nat
  cost       : Nat

%runElab derive "Spell" [Generic,Meta,Eq,Ord]

ToJSON Spell where
  toJSON = genRecordToJSON' reverse
```

#### Arbitrary Sums
Sum types offer the greatest flexibility about how they
can be encoded. There is a `SumEncoding` data type in `JSON.Option`,
the doc strings of which explain in detail the different options we
have. Use `genToJSON` together with one of these options to encode
an arbitrary sum type. If constructor or field names need to
be adjusted before encoding them, use `genToEnum'` instead.

Note: So far, the only option to derive encoders for arbitrary
sum type through elaborator reflection is `ToJSON`, which
passes the `defaultTaggedField` option to `genToJSON` internally.

```idris
data Weapon : Type where
  Sword : (name : String) -> (weight : Nat) -> (value : Nat) -> Weapon
  Club : (weight : Nat) -> Weapon
  Rock : (material : String) -> (weight : Nat) -> Weapon

%runElab derive "Weapon" [Generic,Meta,Eq,Ord]

ToJSON Weapon where
  toJSON = genToJSON' id toLower TwoElemArray
```
