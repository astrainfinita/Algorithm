/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.GetElem
import Algorithm.Data.DFinsupp'.Defs
import Mathlib.Data.Setoid.Basic

universe u v

namespace Vector
variable {α : Type*} {n : ℕ}

set_option linter.unusedVariables false in -- TODO: generalize
@[nolint unusedArguments]
protected abbrev WithDefault (α : Type u) (n : Nat) (f : Fin n → α) := Vector α n

instance {α n f} : Inhabited (Vector.WithDefault α n f) where
  default := .ofFn f

@[simp]
lemma get_default {f} : (default : Vector.WithDefault α n f).get = f := by
  ext i
  exact getElem_ofFn i.2

end Vector

class AssocDArray.ReadOnly (C : Type*) (ι : outParam Type*)
    (α : outParam Type*) (d : outParam <| ι → α) extends
    GetElemAllValid C ι α where
  toDFinsupp' : C → Π₀' i, [α, d i]
  coe_toDFinsupp'_eq_getElem : ∀ a, ⇑(toDFinsupp' a) = (a[·])
export AssocDArray.ReadOnly (toDFinsupp' coe_toDFinsupp'_eq_getElem)

/-- `AssocDArray C ι α d` is a data structure that acts like a finitely supported function
  `Π₀' i, [α, d i]` with single point update operation. -/
class AssocDArray (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) (d : outParam <| ι → α) extends
    AssocDArray.ReadOnly C ι α d, GetSetElemAllValid C ι α where
  getElem_default i : (default : C)[i] = d i

abbrev DefaultDict.ReadOnly (C : Type*) (ι : outParam Type*)
    (α : outParam Type*) (d : outParam α) :=
  AssocDArray.ReadOnly C ι α (fun _ ↦ d)

/-- `DefaultDict C ι α d` is a data structure that acts like a finitely supported function
  `ι →₀' [α, d]` with single point update operation. -/
abbrev DefaultDict (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) (d : outParam α) :=
  AssocDArray C ι α (fun _ ↦ d)

attribute [simp] AssocDArray.getElem_default coe_toDFinsupp'_eq_getElem

section AssocDArray

variable {C ι α : Type*} {d : ι → α}

variable [Inhabited C] [AssocDArray C ι α d]

instance : OfFn C ι α d where
  ofFn := default
  getElem_ofFn i := AssocDArray.getElem_default i

lemma toDFinsupp'_apply_eq_getElem (a : C) (i : ι) : toDFinsupp' a i = a[i] := by simp

@[simp]
lemma toDFinsupp'_setElem [DecidableEq ι] (a : C) (i : ι) (v : α) :
    toDFinsupp' a[i ↦ v] = (toDFinsupp' a).update i v := by
  ext; simp [getElem_setElem_eq_update, - getElem_setElem]

@[simp]
lemma toDFinsupp'_default :
    toDFinsupp' (default : C) = default := by
  ext; simp

end AssocDArray

namespace Vector.WithDefault
variable {α : Type*} {n : ℕ} {f : Fin n → α}

instance : AssocDArray (Vector.WithDefault α n f) (Fin n) α f where
  getElem a i _ := a.get i
  setElem a i := a.set i
  getElem_setElem_self a i v := a.getElem_set_self i.2
  getElem_setElem_of_ne a i v j hij := a.getElem_set_ne i.2 j.2 (by omega)
  getElem_default i := congrFun get_default i
  toDFinsupp' a := DFinsupp'.equivFunOnFintype.symm (get a)
  coe_toDFinsupp'_eq_getElem _ := DFinsupp'.coe_equivFunOnFintype_symm _

end Vector.WithDefault

namespace DefaultDict

export AssocDArray (getElem_default)

class Ext (C : Type*) [Inhabited C] (ι : outParam Type*) (α : outParam Type*)
    (d : outParam α) [DefaultDict C ι α d] : Prop where
  ext : ∀ {m₁ m₂ : C}, (∀ i : ι, m₁[i] = m₂[i]) → m₁ = m₂

variable {C : Type*} [Inhabited C] {ι : Type*} {α : Type*} {d : α} [DefaultDict C ι α d]

variable (C)

protected def Quotient := @Quotient C (Setoid.ker (fun (a : C) (i : ι) ↦ a[i]))

instance : Inhabited (DefaultDict.Quotient C) :=
  inferInstanceAs <| Inhabited (@Quotient C (Setoid.ker _))

instance : DefaultDict (DefaultDict.Quotient C) ι α d where
  getElem c i _ := Quotient.lift (·[·] : C → ι → α) (fun _ _ ↦ id) c i
  setElem q i v := q.map' (·[i ↦ v]) fun _ _ hm ↦ funext fun j ↦ by
    classical simp [congrFun hm j]
  getElem_setElem_self q i v := q.inductionOn (getElem_setElem_self · i v)
  getElem_setElem_of_ne q i v j := q.inductionOn (getElem_setElem_of_ne · v)
  getElem_default := getElem_default
  toDFinsupp' := Quotient.lift toDFinsupp' (fun _ _ ↦ by
    simpa only [DFunLike.ext'_iff, coe_toDFinsupp'_eq_getElem] using id)
  coe_toDFinsupp'_eq_getElem a := by
    induction a using Quotient.ind
    exact coe_toDFinsupp'_eq_getElem _

instance : Ext (DefaultDict.Quotient C) ι α d where
  ext {m₁ m₂} := m₂.inductionOn <| m₁.inductionOn (fun _ _ ha ↦ Quotient.sound <| funext ha)
export Ext (ext)

def listIndicator (l : List ι) (f : ∀ i ∈ l, α) : C :=
  match l with
  | [] => default
  | (i :: l) => (listIndicator l (fun i hi ↦ f i (List.mem_cons_of_mem _ hi)))[i ↦
    f i List.mem_cons_self]

variable {C}

lemma getElem_listIndicator [DecidableEq ι] (l : List ι) (f : ∀ i ∈ l, α) (i) :
    (listIndicator C l f)[i] = if hi : i ∈ l then f i hi else d :=
  match l with
  | [] => by simp [listIndicator, getElem_default]
  | _ :: l => by
    rw [listIndicator, getElem_setElem_eq_update, Function.update_apply]
    split_ifs with h₁ h₂ h₂
    · simp [h₁]
    · simp [h₁] at h₂
    · simp_rw [getElem_listIndicator, dif_pos (List.mem_of_ne_of_mem h₁ h₂)]
    · simp_rw [getElem_listIndicator, dif_neg (List.not_mem_of_not_mem_cons h₂)]

variable [Ext C ι α d]
variable (C)

def indicator (s : Finset ι) (f : ∀ i ∈ s, α) : C :=
  let this := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι ↦ ↑l = s.1)
    (fun m ↦ m = s.1) (fun i ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) ⟨s.1, rfl⟩
  this.liftOn (fun l ↦ listIndicator C l (fun i hi ↦ f i (l.2 ▸ hi : i ∈ s.1)))
    (fun l₁ l₂ hl ↦ ext <| by classical simp [getElem_listIndicator, List.Perm.mem_iff hl])

variable {C}

lemma getElem_indicator [DecidableEq ι] (s : Finset ι) (f : ∀ i ∈ s, α) (i) :
    (indicator C s f)[i] = if hi : i ∈ s then f i hi else d := by
  unfold indicator
  change _ = if hi : i ∈ s.1 then _ else _
  obtain ⟨l, hl⟩ := s.1.exists_rep
  simp_rw [← hl, Equiv.subtypeQuotientEquivQuotientSubtype_mk]
  dsimp
  rw [getElem_listIndicator]
  rfl

abbrev toOfFn [Fintype ι] (f : ι → α) : OfFn C ι α f where
  ofFn := indicator C Finset.univ (fun i _ ↦ f i)
  getElem_ofFn _ := by
    convert (getElem_indicator _ _ _).trans <| dif_pos <| Finset.mem_univ _
    classical infer_instance

end DefaultDict

class HasDefaultAssocDArray (ι : Type u) (α : Type v) (f : ι → α)
    (DefaultAssocDArray : outParam <| Type max u v)
    [Inhabited DefaultAssocDArray] where
  [toAssocDArray : AssocDArray DefaultAssocDArray ι α f]

@[nolint unusedArguments]
def DefaultAssocDArray (ι : Type u) (α : Type v) (f : ι → α) {D : Type _} [Inhabited D]
    [HasDefaultAssocDArray ι α f D] :=
  D

instance {n α f} : HasDefaultAssocDArray (Fin n) α f (Vector.WithDefault α n f) where

example {n α f} := DefaultAssocDArray (Fin n) α f
