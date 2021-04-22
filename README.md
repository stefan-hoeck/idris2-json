# idris2-json

Automatically derivable JSON marshallers in the spirit of
[Haskell's aeson](https://hackage.haskell.org/package/aeson).

### Usage Example

Getting started with encoding and decoding is very easy:

```idris
import JSON
import Generics.Derive

%language ElabReflection

data MonsterClass = Imp | Goblin | Orc | Dragon

%runElab derive "MonsterClass" [Generic,Meta,Show,Eq,ToJSON,FromJSON]

record Villain where
  constructor MkVillain
  name    : String
  hp      : Nat
  class   : MonsterClass
  cronies : List Villain

%runElab derive "Villain" [Generic,Meta,Show,Eq,ToJSON1,FromJSON1]
```

More examples can be found in the [tutorial](src/Doc/Tutorial.idr).

### Missing Stuff

In aeson it is possible to adjust via an `Option` data type,
how generically derived implementations of `ToJSON` and `FromJSON`
behave. Me wants this too! Here's what's still missing:

  - [ ] Configure generic encoders and decoders
    - [ ] Option for adjusting field names
    - [ ] Option for adjusting constructor names
    - [ ] Option for converting all-nullary sum types
          directly to strings (instead of tagged objects)
    - [ ] Option for automatically providing `null` when
          decoding a missing object field
    - [x] Do not add constructor tag for single-constructor types
    - [ ] Encode newtypes directly (without tags for constructor
          or field names.
    - [ ] Options, how sum types should be encoded
      - [ ] As a tagged object, with a field for the constructor to
            be used and a field for the actual values
      - [ ] As an untagged value (constructors will be tried in
            order when decoding until the first succeeds)
      - [x] As an object with a single field named after the
            constructor
      - [ ] As a two element array

### Dependencies

Besides `base` and `contrib`, the following dependencies are needed to
support the automatic deriving of interface implementations:

  * [elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
  * [sop](https://github.com/stefan-hoeck/idris2-sop)

In addition, the test suit requires the following:

  * [pretty-show](https://github.com/stefan-hoeck/idris2-pretty-show)
  * [hedgehog](https://github.com/stefan-hoeck/idris2-hedgehog)

### Idris2 Version

Note, that Idris2 had a bug in `Language.JSON` when encoding and decoding
unicode characters. This was fixed in commit 181b26b25008359e4746adc5ff583836a9fa287e.
