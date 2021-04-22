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

%runElab derive "MonsterClass" [Generic,Meta,Show,Eq,ToJSON]

record Villain where
  constructor MkVillain
  name    : String
  hp      : Nat
  class   : MonsterClass
  cronies : List Villain

%runElab derive "Villain" [Generic,Meta,Show,Eq,ToJSON1]

gorgar : Villain
gorgar = MkVillain "Gorgar" 2000 Dragon [MkVillain "Igor" 10 Imp []]
```

The `ToJSON1` encoder can be used for data types with only
on constructor. In this case, the constructor name will not
be part of the encoding. There are still some options missing about how
to handle different data types (see todo list in the README).
For instance, the automatically derived implementation for `MonsterClass`
will add an empty object field for every constructor name. It would
probably make more sense to encode the constructors directly as
`String`s, as was manually done for `Race` and `Class` above.

Feel free to load this tutorial in a REPL session, and give
the encoders a try: `rlwrap idris2 --find-ipkg src/Doc/Tutorial.md`:

```
:exec putStrLn $ encode gorgar
```
