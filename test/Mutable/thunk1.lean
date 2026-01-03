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

/-! lean4/tests/lean/thunk.lean -/

/-- info: 1 -/
#guard_msgs in #eval (Thunk'.pure 1).get
/-- info: 2 -/
#guard_msgs in #eval (Thunk'.mk fun _ => 2).get
/--
info: 3
4
---
info: 5
-/
#guard_msgs in #eval
  let t1 := Thunk'.mk fun _ => dbg_trace 4; 5
  let t2 := Thunk'.mk fun _ => dbg_trace 3; 0
  let v2 := t2.get
  let v1 := t1.get
  v1 + v2
/--
info: 6
7
---
info: 8
-/
#guard_msgs in #eval
  let t1 := Thunk'.pure 8 |>.map fun n => dbg_trace 7; n
  let t2 := Thunk'.mk fun _ => dbg_trace 6; 0
  let v2 := t2.get
  let v1 := t1.get
  v1 + v2

/--
info: 9
10
---
info: 11
-/
#guard_msgs in #eval
  let t1 := Thunk'.pure 11 |>.bind fun n => dbg_trace 10; Thunk'.pure n
  let t2 := Thunk'.mk fun _ => dbg_trace 9; 0
  let v2 := t2.get
  let v1 := t1.get
  v1 + v2
