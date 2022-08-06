import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Serde

open Std in
@[specialize] def toList : RBNode α (fun _ => β) → List (α × β)
  | .leaf => []
  | .node _ l k v r => toList l ++ [(k,v)] ++ toList r

open Std in
@[specialize] def fromList [Ord α] (abs : List (α × β)) : RBNode α (fun _ => β) := 
  abs.foldr (fun (a, b) obj => obj.insert compare a b) .leaf

section fake_serde

open Std in
inductive Serde where
  | bool : Bool → Serde
  | num : Nat → Serde
  | str : String → Serde
  | arr : List Serde → Serde
  | obj : RBNode String (fun _ => Serde) → Serde

partial def print : Serde → String 
  | .bool b => s!"b{b}"
  | .num n  => s!"#{n}"
  | .str s => s!"\"{s}\""
  | .arr ss =>
    let ps := ss.map print
    let printed := ", ".intercalate ps
    s!"[{printed}]"
  | .obj dict => 
    let list := toList dict
    let strings := list.map fun (name, serd) =>
      s!"{name}: {print serd}"
    let strings := "\n".intercalate strings
    "{" ++ strings ++ "}"

instance : ToString Serde := ⟨print⟩

def objFromKV (kv : List (String × Serde)) : Serde := .obj $ fromList kv

class Serialize (α : Type) where
  serialize : α → Serde

instance : Serialize Bool := ⟨.bool⟩

instance : Serialize Nat := ⟨.num⟩

instance : Serialize String := ⟨.str⟩

instance {α : Type} [Serialize α] : Serialize (List α) where
  serialize as := .arr <| as.map Serialize.serialize

instance {α : Type} [Serialize α] : Serialize (Array α) where
  serialize as := Serialize.serialize as.toList

end fake_serde

end Serde

section handler

namespace Lean.Elab.Deriving.Foo
open Lean.Parser.Term
open Meta

universe u

open Command Serde

open Serialize

-- TODO : Finish figuring this out
def mkStructureSerializeFuns (_ : Context) (_ : Name) : TermElabM Syntax := pure .missing

def mkAltRHS (funcID : Ident) (ctor : ConstructorVal) (binders : Array (Ident × Expr)) (userNames : Option (Array Name)): TermElabM Term := do
  let mkSerialize (id : Ident) (type : Expr) : TermElabM Term := do
    if type.isAppOf ctor.induct then `($funcID:ident $id:ident)
    else ``(serialize $id:ident)
  
  match binders, userNames with
    | #[], _ => 
      ``(serialize $(quote ctor.name.getString!))
    | #[(x, t)], none => 
      ``(objFromKV [($(quote ctor.name.getString!), $(← mkSerialize x t))])
    | xs, none =>
      let xs ← xs.mapM fun (x, t) => mkSerialize x t
      ``(objFromKV [($(quote ctor.name.getString!), Serialize.arr #[$[$xs:term],*])])
    | xs, some userNames =>
      let xs ← xs.mapIdxM fun idx (x, t) => do
        `(($(quote userNames[idx]!.getString!), $(← mkSerialize x t)))
      ``(objFromKV [($(quote ctor.name.getString!), objFromKV [$[$xs:term],*])])

def mkOneMatch (funcID : Ident) (indVal : InductiveVal) (ctorInfo : ConstructorVal) : TermElabM (TSyntax `Lean.Parser.Term.matchAlt) := do
  forallTelescopeReducing ctorInfo.type fun xs _ => do
    let mut patterns := #[]
    for _ in [:indVal.numIndices] do
      patterns := patterns.push (← `(_))
    let mut ctorArgs := #[]
    for _ in [:indVal.numParams] do
      ctorArgs := ctorArgs.push (←`(_))
    let mut binders := #[]
    let mut userNames := #[]
    for i in [:ctorInfo.numFields] do
      let x := xs[indVal.numParams + i]!
      let localDecl ← getLocalDecl x.fvarId!
      if !localDecl.userName.hasMacroScopes then
        userNames := userNames.push localDecl.userName
      let a := mkIdent (← mkFreshUserName `a)
      binders := binders.push (a, localDecl.type)
      ctorArgs := ctorArgs.push a
    patterns := patterns.push (← `(@$(mkIdent ctorInfo.name):ident $ctorArgs:term*))
    let rhs ← mkAltRHS funcID ctorInfo binders (if userNames.size == binders.size then some userNames else none)
    `(matchAltExpr| | $[$patterns:term],* => $rhs:term)

def mkInductiveMatch (funcID : Ident) (header : Header) (declName : Name) : TermElabM (TSyntax `term) := do
   let indVal ← getConstInfoInduct declName
   let discrs ← mkDiscrs header indVal
   let mut alts : List (TSyntax `Lean.Parser.Term.matchAlt) := []
   for ctor in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctor
    alts := alts.cons (← mkOneMatch funcID indVal ctorInfo)
   let altsArray : TSyntaxArray `Lean.Parser.Term.matchAlt := ⟨alts⟩
   `(match $[$discrs],* with $altsArray:matchAlt*)

def mkInductiveSerializeFuns (ctx : Context) (declName : Name) : TermElabM Syntax := do
  let funcID := mkIdent ctx.auxFunNames[0]!
  let header ← mkHeader ``Serialize 1 ctx.typeInfos[0]!
  let rhs ← mkInductiveMatch funcID header declName
  `(private partial def $funcID:ident $header.binders:bracketedBinder* := $rhs)

def mkSerializeCmds (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "serialize" declName
  if isStructure (← getEnv) declName then
    return #[← mkStructureSerializeFuns ctx declName] ++ (← mkInstanceCmds ctx ``Serialize #[declName])
  else
    return #[← mkInductiveSerializeFuns ctx declName] ++ (← mkInstanceCmds ctx ``Serialize #[declName])

def mkSerializeHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size > 1 then 
    return false 
  else
    let cmds ← liftTermElabM none <| mkSerializeCmds declNames[0]!
    cmds.forM elabCommand
    return true

initialize
  registerBuiltinDerivingHandler ``Serialize mkSerializeHandler

end Lean.Elab.Deriving.Foo

end handler