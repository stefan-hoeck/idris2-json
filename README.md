# idris2-json

Automatically derivable JSON marshallers in the spirit of
[Haskell's aeson](https://hackage.haskell.org/package/aeson).

Please note, that while tests suggest that the encoders and decoders
perform reasonably well, this library has not been optimized in
terms of performance.

### Usage Example

Getting started with encoding and decoding is very easy:

```idris
import JSON
import Generics.Derive

%language ElabReflection

data MonsterClass = Imp | Goblin | Orc | Dragon

%runElab derive "MonsterClass" [Generic,Meta,Show,Eq,EnumToJSON,EnumFromJSON]

record Villain where
  constructor MkVillain
  name    : String
  hp      : Nat
  class   : MonsterClass
  cronies : List Villain

%runElab derive "Villain" [Generic,Meta,Show,Eq,RecordToJSON,RecordFromJSON]

gorgar : Villain
gorgar = MkVillain "Gorgar" 2000 Dragon [MkVillain "Igor" 10 Imp []]
```

You can give this a try after installing `idris2-json`:

```
rlwrap idris2 -p elab-util -p sop -p json -p contrib README.md

Main> :exec putStrLn $ encode gorgar
Main> :exec printLn $ (decode {a = Villain} (encode gorgar))
```

More examples can be found in the [tutorial](src/Doc/Tutorial.md).

### Missing Stuff

In aeson it is possible to adjust via an `Option` data type,
how generically derived implementations of `ToJSON` and `FromJSON`
behave. Me wants this too! Here's what's still missing:

  - [ ] Configure generic encoders and decoders
    - [x] Option for adjusting field names
    - [x] Option for adjusting constructor names
    - [x] Option for converting all-nullary sum types
          directly to strings (instead of tagged objects)
    - [ ] Option for automatically providing `null` when
          decoding a missing object field
    - [x] Do not add constructor tag for single-constructor types
    - [x] Encode newtypes directly (without tags for constructor
          or field names.
    - [x] Options, how sum types should be encoded
      - [x] As a tagged object, with a field for the constructor to
            be used and a field for the actual values
      - [x] As an untagged value (constructors will be tried in
            order when decoding until the first succeeds)
      - [x] As an object with a single field named after the
            constructor
      - [x] As a two element array

### Dependencies

Besides `base` and `contrib`, the following dependencies are needed to
support the automatic deriving of interface implementations:

  * [elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
  * [experimental](https://github.com/stefan-hoeck/idris2-experimental)
  * [sop](https://github.com/stefan-hoeck/idris2-sop)

In addition, the test suit requires the following:

  * [pretty-show](https://github.com/stefan-hoeck/idris2-pretty-show)
  * [hedgehog](https://github.com/stefan-hoeck/idris2-hedgehog)

### Idris2 Version

The latest release requires Idris2, version 0.4.0.
The actual commit has been built against Idris 2, version 0.4.0-ea1ad1688.
