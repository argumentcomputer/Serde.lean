import Std.Data.RBMap

namespace Std

/--
TODO: Write a nice API around `Vector`
-/
inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → Vector α n → Vector α (n+1)

@[specialize] def toList : RBNode α (fun _ => β) → List (α × β)
  | .leaf => []
  | .node _ l k v r => toList l ++ [(k,v)] ++ toList r

@[specialize] def fromList [Ord α] (abs : List (α × β)) : RBNode α (fun _ => β) := 
  abs.foldr (fun (a, b) obj => obj.insert compare a b) .leaf