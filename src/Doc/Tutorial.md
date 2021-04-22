## Idris2-json: Tutorial

This library offers functionality for writing marshallers
from and to JSON in Idris2. While it is kept in the spirit
of [Haskell's aeson](https://hackage.haskell.org/package/aeson),
there are is one key difference: We abstract over the `Value`
representation, allowing greater flexibility in how data
is encoded and decoded. While we will use the `JSON` type
from `Language.JSON` in this tutorial, users on one of the
Javascript backends might opt for going via some (immutable)
wrapper around Javascript `object`s, thus having access
to the highly optimized parser and stringifier of the backend
(this is what [idris2-dom](https://github.com/stefan-hoeck/idris2-dom)
does. This is a literate Idris2 file, hence:

```idris
module Doc.Tutorial

import JSON
import Generics.Derive

%language ElabReflection
```

### Writing `ToJSON` Encoders
