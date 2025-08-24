module Derive.ToJSON

import JSON.Option
import JSON.ToJSON
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
generalToJsonType is arg = piAll `({0 v : _} -> Encoder v => ~(arg) -> v) is

||| Top-level function declaration implementing the `toJSON` function for
||| the given data type.
export
toJsonClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
toJsonClaim fun p =
  let tpe := generalToJsonType (allImplicits p "ToJSON") p.applied
   in public' fun tpe

||| Top-level declaration of the `ToJSON` implementation for the given data type.
export
toJsonImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
toJsonImplClaim impl p = implClaim impl (implType "ToJSON" p)

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

  encArgs : (unwrapUnary : Bool) -> (tag : TTImp) -> ArgInfo -> TTImp
  encArgs _    tag Const         = `(string  ~(tag))
  encArgs True _   (Fields [<v]) = encValue $ toRegular v
  encArgs True _   (Values [<v]) = encValue v
  encArgs _    _   (Fields sx)   = `(object ~(listOf $ map encField sx))
  encArgs _    _   (Values sx)   = `(array ~(listOf $ map encValue sx))

  encSum : DCon -> TTImp
  encSum (DC n b _ tag Const) = encArgs o.unwrapUnary tag Const
  encSum (DC n b _ tag args)  =
    let flds := encArgs o.unwrapUnary tag args
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
  recClause fun c = patClause (var fun `app` c.bound) (encArgs o.unwrapUnary c.tag c.args)

  export
  toJsonClauses : (fun : Name) -> TypeInfo -> List Clause
  toJsonClauses fun ti = case ti.cons of
    -- single constructor
    [x] => if o.unwrapRecords then [recClause fun $ dcon o x]
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
customToJSON : Options -> List Name -> ParamTypeInfo -> Res (List TopLevel)
customToJSON o nms p =
  let fun  := funName p "toJson"
      impl := implName p "ToJSON"
   in Right
        [ TL (toJsonClaim fun p) (toJsonDef nms o fun p.info)
        , TL (toJsonImplClaim impl p) (toJsonImplDef fun impl)
        ]

||| Generate declarations and implementations for `ToJSON` for a given data type
||| using default settings.
export %inline
ToJSON : List Name -> ParamTypeInfo -> Res (List TopLevel)
ToJSON = customToJSON defaultOptions
