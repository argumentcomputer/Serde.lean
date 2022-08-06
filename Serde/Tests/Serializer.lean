import Serde.Deriving.Serialize

open Serde

inductive test where
  | con1 : test
  | con2 : Bool → test
  | con3 : Nat → test
deriving Serialize

open test

#eval Serialize.serialize con1

#eval Serialize.serialize (con2 true)

#eval Serialize.serialize (con3 4)

-- structure Howdy where
--   greeting : String
-- deriving Serialize