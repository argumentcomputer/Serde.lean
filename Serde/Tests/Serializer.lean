import Serde.Deriving.Serialize

open Serde

inductive test where
  | con1 : test
  | con2 : Bool → test
  | con3 : Nat → test
deriving Serialize, Lean.ToJson

inductive Vector : Nat → Type where
  | nil  : Vector 0
  | cons : Bool → {n : Nat} → Vector n → Vector (n+1)
deriving Lean.ToJson

open test

#eval Serialize.serialize con1

#eval Serialize.serialize (con2 true)

#eval Serialize.serialize (con3 4)

structure Howdy where
  greeting : String
  goodbye : Nat
deriving Serialize

#eval Serialize.serialize (⟨"hi", 2⟩ : Howdy)