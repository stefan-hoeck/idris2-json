module Derive.FromJSON

import JSON.Option
import JSON.FromJSON
import public Derive.Show

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| General type of a `fromJSON` function with the given list
||| of implicit and auto-implicit arguments, plus the given argument type
||| to be displayed.
|||
||| TODO: Use fresh names for `v` and `obj`.
export
generalFromJsonType : (implicits : List Arg) -> (arg : TTImp) -> TTImp
generalFromJsonType is arg =
  piAll `({0 v : _} -> {0 obj : _} -> Value v obj => Parser v ~(arg)) is

||| Top-level function declaration implementing the `fromJSON` function for
||| the given data type.
export
fromJsonClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
fromJsonClaim fun p =
  let tpe := generalFromJsonType (allImplicits p "FromJSON") p.applied
   in public' fun tpe

||| Top-level declaration of the `FromJSON` implementation for the given data type.
export
fromJsonImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
fromJsonImplClaim impl p = implClaim impl (implType "FromJSON" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

val : String
val = "val"

bval : TTImp
bval = bindVar val

vval : TTImp
vval = varStr val

obj : String
obj = "obj"

bobj : TTImp
bobj = bindVar obj

vobj : TTImp
vobj = varStr obj

matchArray : SnocList (BoundArg 2 p) -> TTImp -> TTImp
matchArray [<]                  s = s
matchArray (sx :< BA _ [_,y] _) s =
  matchArray sx `(~(bindVar y) :: ~(s))

constClause : DCon -> Clause
constClause c = c.tag .= c.applied

matchEither : (pat,res : TTImp) -> String -> TTImp
matchEither pat res x =
  `(case ~(pat) of
     Right ~(bindVar x) => ~(res)
     Left e             => Left e)

||| Top-level definition of the `FromJSON` implementation for the given data type.
export
fromJsonImplDef : (fun,impl : Name) -> Decl
fromJsonImplDef f i = def i [var i .= var "MkFromJSON" .$ var f]

parameters (nms : List Name) (o : Options) (tpeName : TTImp) (err : TTImp)

  dec : Name -> TTImp
  dec n =
    let fnm := fieldNamePrim o n
     in case o.replaceMissingKeysWithNull of
          True  => `(~(vobj) .:! ~(fnm))
          False => `(~(vobj) .: ~(fnm))

  decFields : SnocList (BoundArg 2 RegularNamed) -> (res : TTImp) -> TTImp
  decFields [<] res = `(withObject ~(tpeName) $ \ ~(bobj) => ~(res))
  decFields (sx :< (BA a [x,y] _)) res =
    let pat := assertIfRec nms a.type (dec $ argName a)
     in decFields sx (matchEither pat res x)

  decValues : SnocList (BoundArg 2 Regular) -> (res : TTImp) -> TTImp
  decValues sx res =
    let nargs := `(fromInteger ~(primVal $ BI $ cast (length sx)))
        mtch  := matchArray sx `(Nil)
     in `(withArrayN ~(nargs) ~(tpeName) $ \ ~(mtch) => ~(go sx res))
    where go : SnocList (BoundArg 2 Regular) -> TTImp -> TTImp
          go [<]                    res = res
          go (sx :< (BA a [x,y] _)) res =
            let pat := assertIfRec nms a.type `(fromJSON ~(varStr y))
             in go sx (matchEither pat res x)

  consts : List DCon -> TTImp
  consts ds =
    let catch := `(s) .= `(fail $ ~(err) ++ show s)
        cse   :=  lambdaArg {a = Name} "x"
              .=> iCase `(x) implicitFalse (map constClause ds ++ [catch])
     in `(withString ~(tpeName) ~(cse))

  withArgs : DCon -> List DCon -> TTImp
  withArgs d ds = case o.sum of
    UntaggedValue         => untagged
    ObjectWithSingleField => `(fromSingleField ~(tpeName) ~(pairCases))
    TwoElemArray          => `(fromTwoElemArray ~(tpeName) ~(pairCases))
    (TaggedObject tg cs)  =>
      let tf := primVal $ Str tg
          cf := primVal $ Str cs
       in `(fromTaggedObject ~(tpeName) ~(tf) ~(cf) ~(pairCases))

    where rhs : DCon -> TTImp
          rhs c = case c.args of
            Const     => decFields [<] c.applied
            Fields sx => decFields sx  c.applied
            Values sx => decValues sx  c.applied

          clause : DCon -> Clause
          clause c = `(MkPair ~(c.tag) ~(bval)) .= `(~(rhs c) ~(vval))

          pairCases : TTImp
          pairCases =
            let clauses := map clause (d :: ds)
                catch   := `(MkPair s _) .= `(fail $ ~(err) ++ show s)
             in lambdaArg {a = Name} "x" .=>
                iCase `(x) implicitFalse (clauses ++ [catch])

          untagged : TTImp
          untagged = foldl (\t,c => `(~(t) <|> ~(rhs c))) (rhs d) ds


  decSum : (constants, withArgs : List DCon) -> TTImp
  decSum [] []        = `(fail $ "Uninhabited type: " ++ ~(tpeName))
  decSum [] (w :: ws) = withArgs w ws
  decSum cs []        = consts cs
  decSum cs (w :: ws) = `(~(consts cs) <|> ~(withArgs w ws))

  decRecord : DCon -> TTImp
  decRecord c = case c.args of
    Const       => consts [c]
    Fields [<x] => `(map ~(var c.name) . fromJSON)
    Values [<x] => `(map ~(var c.name) . fromJSON)
    Fields sx   => decFields sx c.applied
    Values sx   => decValues sx c.applied

  export
  fromJsonClause : (fun : Name) -> TypeInfo -> Clause
  fromJsonClause fun x = case map (dcon o) x.cons of
    [c] => var fun .= decRecord c
    cs  =>
      let (consts,withArgs) := partition isConst cs
       in  var fun .= decSum consts withArgs

  export
  fromJsonDef : Name -> TypeInfo -> Decl
  fromJsonDef fun ti = def fun [fromJsonClause fun ti]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

err : Named a => a -> TTImp
err v = primVal $ Str $ "Unexpected constructor tag for \{v.nameStr}: "

export
customFromJSON : Options -> List Name -> ParamTypeInfo -> Res (List TopLevel)
customFromJSON o nms p =
  let fun  := funName p "fromJson"
      impl := implName p "FromJSON"
   in Right [ TL (fromJsonClaim fun p)
                 (fromJsonDef nms o p.namePrim (err p) fun p.info)
            , TL (fromJsonImplClaim impl p) (fromJsonImplDef fun impl)
            ]

||| Generate declarations and implementations for
||| `FromJSON` for a given data type
||| using default settings.
export %inline
FromJSON : List Name -> ParamTypeInfo -> Res (List TopLevel)
FromJSON = customFromJSON defaultOptions
