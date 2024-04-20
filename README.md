# idris2-json

Automatically derivable JSON marshallers in the spirit of
[Haskell's aeson](https://hackage.haskell.org/package/aeson).

Please note, that while tests suggest that the encoders and decoders
perform reasonably well, this library has not been optimized in
terms of performance.

## Usage Example

Getting started with encoding and decoding is very easy:

```idris
module README

import JSON.Derive

%language ElabReflection

data MonsterClass = Imp | Goblin | Orc | Dragon

%runElab derive "MonsterClass" [Show,Eq,ToJSON,FromJSON]

record Villain where
  constructor MkVillain
  name    : String
  hp      : Nat
  class   : MonsterClass
  cronies : List Villain

%runElab derive "Villain" [Show,Eq,ToJSON,FromJSON]

gorgar : Villain
gorgar = MkVillain "Gorgar" 2000 Dragon [MkVillain "Igor" 10 Imp []]
```

You can give this a try at the REPL:

```shell
pack repl docs/src/README.md

README> :exec putStrLn $ encode gorgar
README> :exec printLn $ (decode {a = Villain} (encode gorgar))
```

More examples can be found in the [tutorial](docs/src/Docs/Tutorial.md).

## Dependencies

Besides `base`, the following dependencies are needed to
support the automatic deriving of interface implementations:

* [elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
* [parser-json](https://github.com/stefan-hoeck/idris2-parser)

In addition, the test suit requires the following:

* [pretty-show](https://github.com/stefan-hoeck/idris2-pretty-show)
* [hedgehog](https://github.com/stefan-hoeck/idris2-hedgehog)

It is nowadays recommended to use a package manager such as
[pack](https://github.com/stefan-hoeck/idris2-pack) for installing
and managing your Idris2 dependencies.

## The json-simple sub-project

Personally, I don't think the versatility of using different JSON
representations and thus having to go via `Encoder`, `Value`, or `Object`
interfaces is worth the hassle. I therefore added a second library,
which uses just the JSON representation from the
[parser-json](https://github.com/stefan-hoeck/idris2-parser) package.
