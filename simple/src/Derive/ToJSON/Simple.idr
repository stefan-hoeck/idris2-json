module Derive.ToJSON.Simple

import JSON.Simple.Option
import JSON.Simple.ToJSON
import public Derive.Show
import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| General type of a `toJSON` function with the given list
||| of implicit and auto-implicit arguments, plus the given argument type
||| to be displayed.
|||
||| TODO: Use fresh name for `v`
export
generalToJsonType : (implicits : List Arg) -> (arg : TTImp) -> TTImp
generalToJsonType is arg = piAll `(~(arg) -> JSON) is

||| Top-level function declaration implementing the `toJSON` function for
||| the given data type.
export
toJsonClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
toJsonClaim vis fun p =
  let tpe := generalToJsonType (allImplicits p "ToJSON") p.applied
   in simpleClaim vis fun tpe

||| Top-level declaration of the `ToJSON` implementation for the given data type.
export
toJsonImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
toJsonImplClaim vis impl p = implClaimVis vis impl (implType "ToJSON" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

||| Top-level definition of the `ToJSON` implementation for the given data type.
export
toJsonImplDef : (fun, impl : Name) -> Decl
toJsonImplDef f i = def i [patClause (var i) (var "MkToJSON" `app` var f)]

parameters (nms : List Name) (o : Options)

  encValue : BoundArg 2 Regular -> TTImp
  encValue (BA (MkArg _  _ _ t) [x,_] _) =
    assertIfRec nms t `(toJSON ~(var x))

  encField : BoundArg 2 RegularNamed -> TTImp
  encField (BA a [x,_]  _) =
    let nm := fieldNamePrim o (argName a)
     in assertIfRec nms a.type `(jpair ~(nm) ~(var x))

  encArgs : (isRecord : Bool) -> (tag : TTImp) -> ArgInfo -> TTImp
  encArgs _    tag Const         = `(JString  ~(tag))
  encArgs True _   (Fields [<v]) = encValue $ toRegular v
  encArgs True _   (Values [<v]) = encValue v
  encArgs _    _   (Fields sx)   = `(JObject ~(listOf $ map encField sx))
  encArgs _    _   (Values sx)   = `(JArray ~(listOf $ map encValue sx))

  encSum : DCon -> TTImp
  encSum (DC n b _ tag Const) = encArgs False tag Const
  encSum (DC n b _ tag args)  =
    let flds := encArgs False tag args
     in case o.sum of
          UntaggedValue         => flds
          ObjectWithSingleField => `(singleField ~(tag) ~(flds))
          TwoElemArray          => `(twoElemArray ~(tag) ~(flds))
          (TaggedObject tg cs)  =>
            let tf := primVal $ Str tg
                cf := primVal $ Str cs
             in `(taggedObject ~(tf) ~(cf) ~(tag) ~(flds))

  sumClause : (fun : Name) -> DCon -> Clause
  sumClause fun c = patClause (var fun `app` c.bound) (encSum c)

  recClause : (fun : Name) -> DCon -> Clause
  recClause fun c = patClause (var fun `app` c.bound) (encArgs True c.tag c.args)

  export
  toJsonClauses : (fun : Name) -> TypeInfo -> List Clause
  toJsonClauses fun ti = case ti.cons of
    -- single constructor
    [x] =>
      if o.unwrapRecords then [recClause fun $ dcon o x]
      else [sumClause fun (dcon o x)]

    -- multi-constructor
    xs  => map (sumClause fun . dcon o) xs

  export
  toJsonDef : Name -> TypeInfo -> Decl
  toJsonDef fun ti = def fun (toJsonClauses fun ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

export
customToJSON :
     Visibility
  -> Options
  -> List Name
  -> ParamTypeInfo
  -> Res (List TopLevel)
customToJSON vis o nms p =
  let fun  := funName p "toJson"
      impl := implName p "ToJSON"
   in Right
        [ TL (toJsonClaim vis fun p) (toJsonDef nms o fun p.info)
        , TL (toJsonImplClaim vis impl p) (toJsonImplDef fun impl)
        ]

||| Generate declarations and implementations for `ToJSON` for a given data type
||| using default settings.
export %inline
ToJSON : List Name -> ParamTypeInfo -> Res (List TopLevel)
ToJSON = customToJSON Export defaultOptions
