/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

/-!
# Mutable

-/

universe u v

-- waiting lean4#2292
/-
structure Mutable (α : Type u) : Type u where
  mk ::
  get : α

attribute [extern "lean_st_mk_ref"] Mutable.mk
attribute [extern "lean_st_ref_get"] Mutable.get
-/

opaque MutableAux (α : Type u) : Subtype (· = α) := ⟨α, rfl⟩

def Mutable (α : Type u) : Type u := (MutableAux α).val

namespace Mutable
variable {α : Type u} {β : Type v}

@[extern "lean_st_mk_ref"]
def mk (a : α) : Mutable α := (MutableAux α).2.mpr a

@[extern "lean_st_ref_get", never_extract]
def get (x : @& Mutable α) : α := (MutableAux α).2.mp x

set_option linter.unusedVariables false in
@[extern "lean_Mutable_set", never_extract]
unsafe def set (x : @& Mutable α) (a : α) (b : @& β) : β := b

@[simp] theorem mk_get (x : Mutable α) : mk x.get = x := by simp [mk, Mutable.get]
@[simp] theorem get_mk (x : α) : (mk x).get = x := by simp [mk, Mutable.get]

def rec {motive : Mutable α → Sort _} (h : ∀ a, motive (mk a)) (x : Mutable α) : motive x :=
  mk_get x ▸ h _

theorem ext {x y : Mutable α} (get : x.get = y.get) : x = y := by
  simpa [Mutable.get] using congrArg (MutableAux α).2.mpr get

theorem ext_iff {x y : Mutable α} : x = y ↔ x.get = y.get :=
  ⟨congrArg get, ext⟩

@[simp]
theorem mk_inj {x y : α} : mk x = mk y ↔ x = y :=
  ext_iff.trans (by simp)

unsafe def modifyUnsafe (x : Mutable α) (f : α → α) : α :=
  let a := f x.get; x.set a a

set_option linter.unusedVariables false in
unsafe abbrev modifyImpl (x : Mutable α)
    (f : α → α) (hf : ∀ a, f a = a) : α :=
  Mutable.modifyUnsafe x f

@[implemented_by Mutable.modifyImpl]
def modify (x : Mutable α)
    (f : α → α) (hf : ∀ a, f a = a) : α :=
  f x.get

unsafe def getModifyUnsafe (x : Mutable α) (f : α → β × α) : β :=
  let (b, a) := f x.get; x.set a b

set_option linter.unusedVariables false in
unsafe abbrev getModifyImpl (x : Mutable α)
    (f : α → β × α) (hgf : ∀ a, (f a).snd = a) : β :=
  Mutable.getModifyUnsafe x f

@[implemented_by Mutable.getModifyImpl]
def getModify (x : Mutable α) (f : α → β × α) (hgf : ∀ a, (f a).snd = a) : β :=
  (f x.get).fst

@[simp]
theorem getModify_mk {a : α} {f : α → β × α} {hgf : ∀ a, (f a).snd = a} :
    (mk a).getModify f hgf = (f a).fst := by
  simp [getModify]

end Mutable
