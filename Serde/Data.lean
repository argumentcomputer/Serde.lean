import Serde.ForStdLib

abbrev Serde.Name := String

/-
Missing in Lean so we probably should decide what to do about this:
* Signed integers (`i8` through `i128`)
* `u128` (can use `USize` I think)
* `f64` (really no doubles?)
-/
inductive Primitive where
  | bool : Bool   → Primitive
  | char : Char   → Primitive
  | u8   : UInt8  → Primitive
  | u16  : UInt16 → Primitive
  | u32  : UInt32 → Primitive
  | u64  : UInt64 → Primitive
  | f32  : Float  → Primitive

open Serde Std in
/--
Basically a verbatim copy of https://serde.rs/data-model.html
-/
inductive Serde where
  | prim : Primitive → Serde
  | str : String → Serde
  | bArr : ByteArray → Serde
  | unit : Serde
  | unitStruct : Name → Serde
  -- TODO: Figure out what to do about `unit_variant`
  | newStruct : Name → Serde → Serde
  -- TODO: Figure out what to do about `newtype_variant`
  | seq : List Serde → Serde
  | tuple (n : Nat): Vector Serde n → Serde 
  | tupleStruct (n : Nat): Name → Vector Serde n → Serde
  -- TODO: Figure out what to do about `tuple_variant`
  | map : RBNode String (fun _ => Serde) → Serde
  | mapStruct : Name → RBNode String (fun _ => Serde) → Serde
  -- TODO: Figure out what to do about `struct_variant`