# idris2-json

Automatically derivable JSON marshallers in the spirit of Haskell's aeson.

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
