import Mutable.Mutable

universe u

def Thunk' (α : Type u) : Type u := Mutable (Unit → α)

variable {α : Type u}

def Thunk'.mk (fn : Unit → α) : Thunk' α := Mutable.mk fn

protected def Thunk'.pure (a : α) : Thunk' α :=
  .mk fun _ ↦ a

protected def Thunk'.get (x : Thunk' α) : α :=
  Mutable.getModify x (fun f ↦ let a := f (); ⟨a, fun _ ↦ a⟩) (fun _ ↦ rfl)

@[inline] protected def Thunk'.map (f : α → β) (x : Thunk' α) : Thunk' β :=
  .mk fun _ => f x.get

@[inline] protected def Thunk'.bind (x : Thunk' α) (f : α → Thunk' β) : Thunk' β :=
  .mk fun _ => (f x.get).get

#eval show IO Unit from do
  let _ : OfNat (Thunk' Nat) 0 := ⟨.pure 0⟩
  let _ : Inhabited (Thunk' Nat) := ⟨.pure 0⟩
  let _ : Add (Thunk' Nat) := ⟨fun x y ↦ .mk fun _ ↦ x.get + y.get⟩
  let mut l := [Thunk'.pure 1]
  for _ in [0 : 32] do
    l := l.sum :: l
  IO.println l.head!.get
#eval show IO Unit from do
  let _ : OfNat (Thunk' Nat) 0 := ⟨.pure 0⟩
  let _ : Inhabited (Thunk' Nat) := ⟨0⟩
  let _ : Add (Thunk' Nat) := ⟨fun x y ↦ .mk fun _ ↦ x.get + y.get⟩
  let mut l := [1]
  for _ in [0 : 32] do
    l := l.sum :: l
  IO.println l.head!
