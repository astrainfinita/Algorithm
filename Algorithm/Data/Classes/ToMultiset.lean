/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.Erase
import Mathlib.Data.Multiset.AddSub

variable {C α : Type*}

class Membership.IsEmpty (C : Type*) {α : outParam Type*} [Membership α C] where
  isEmpty : C → Bool
  isEmpty_iff_forall_not_mem {c} : isEmpty c ↔ ∀ a, a ∉ c
export Membership.IsEmpty (isEmpty isEmpty_iff_forall_not_mem)

lemma isEmpty_eq_false_iff_exists_mem [Membership α C] [Membership.IsEmpty C] {c : C} :
    isEmpty c = false ↔ ∃ a, a ∈ c := by
  rw [Bool.eq_false_iff, not_iff_comm, isEmpty_iff_forall_not_mem]
  push_neg
  rfl

@[mk_iff]
class LawfulEmptyCollection (C : Type*) (α : outParam Type*)
    [Membership α C] [EmptyCollection C] : Prop where
  not_mem_empty (x : α) : x ∉ (∅ : C)
export LawfulEmptyCollection (not_mem_empty)

class ToMultiset (C : Type*) (α : outParam Type*) extends Membership α C, Membership.IsEmpty C where
  toMultiset : C → Multiset α
  mem c a := a ∈ toMultiset c
  mem_toMultiset {x c} : x ∈ toMultiset c ↔ x ∈ c := by rfl
export ToMultiset (toMultiset mem_toMultiset)

attribute [simp] mem_toMultiset

/--
The size function derived from `ToMultiset`.

Use `size` for computation whenever possible, as it is usually faster.
-/
def sizeTM [ToMultiset C α] (c : C) : Nat :=
  (toMultiset c).card

lemma card_toMultiset [ToMultiset C α] (c : C) : (toMultiset c).card = sizeTM c := rfl

lemma sizeTM_eq_card_toMultiset [ToMultiset C α] (c : C) : sizeTM c = (toMultiset c).card :=
  rfl

class Size (C : Type*) {α : outParam Type*} [ToMultiset C α] where
  size : C → Nat
  size_eq_sizeTM c : size c = sizeTM c
export Size (size size_eq_sizeTM)

attribute [simp] size_eq_sizeTM

class ToMultiset.LawfulInsert (C : Type*) (α : outParam Type*)
    [ToMultiset C α] [Insert α C] : Prop where
  toMultiset_insert a (c : C) : toMultiset (insert a c) = a ::ₘ (toMultiset c)
export ToMultiset.LawfulInsert (toMultiset_insert)

attribute [simp] toMultiset_insert

@[mk_iff lawfulErase_iff_toMultiset]
class LawfulErase (C : Type*) (α : outParam Type*)
    [ToMultiset C α] [Erase C α] : Prop where
  toMultiset_erase [DecidableEq α] (c : C) a : toMultiset (erase c a) = (toMultiset c).erase a
export LawfulErase (toMultiset_erase)

attribute [simp] toMultiset_erase

section instances

instance : Membership.IsEmpty (List α) where
  isEmpty := List.isEmpty
  isEmpty_iff_forall_not_mem := by simp [List.eq_nil_iff_forall_not_mem]

instance : ToMultiset (List α) α where
  toMultiset := (↑)
  mem_toMultiset := .rfl

instance : Size (List α) where
  size := List.length
  size_eq_sizeTM _ := rfl

instance : Membership.IsEmpty (Array α) where
  isEmpty := Array.isEmpty
  isEmpty_iff_forall_not_mem := by simp [Array.eq_empty_iff_forall_not_mem]

instance : ToMultiset (Array α) α where
  toMultiset c := ↑c.toList
  mem_toMultiset := Array.mem_def.symm

instance : Size (Array α) where
  size := Array.size
  size_eq_sizeTM _ := rfl

end instances

section ToMultiset

variable [ToMultiset C α]

section LawfulEmptyCollection
variable [EmptyCollection C]

lemma lawfulEmptyCollection_iff_toMultiset :
    LawfulEmptyCollection C α ↔ toMultiset (∅ : C) = 0 := by
  simp_rw [lawfulEmptyCollection_iff, Multiset.eq_zero_iff_forall_notMem, mem_toMultiset]

alias ⟨_, LawfulEmptyCollection.of_toMultiset⟩ := lawfulEmptyCollection_iff_toMultiset

@[simp]
lemma toMultiset_empty [LawfulEmptyCollection C α] :
    toMultiset (∅ : C) = 0 := by
  rwa [← lawfulEmptyCollection_iff_toMultiset]

end LawfulEmptyCollection

@[simp]
lemma toMultiset_list (l : List α) : toMultiset l = ↑l := rfl

section IsEmpty

lemma isEmpty_iff_sizeTM_eq_zero {c : C} : isEmpty c ↔ sizeTM c = 0 := by
  simp [isEmpty_iff_forall_not_mem, sizeTM, Multiset.eq_zero_iff_forall_notMem]

lemma isEmpty_iff_size_eq_zero [Size C] {c : C} : isEmpty c ↔ size c = 0 := by
  simp [isEmpty_iff_sizeTM_eq_zero]

lemma isEmpty_eq_decide_sizeTM (c : C) : isEmpty c = decide (sizeTM c = 0) := by
  simp only [← isEmpty_iff_sizeTM_eq_zero, Bool.decide_coe]

lemma isEmpty_eq_sizeTM_beq_zero (c : C) : isEmpty c = (sizeTM c == 0) := by
  rw [isEmpty_eq_decide_sizeTM]
  cases sizeTM c <;> rfl

lemma toMultiset_iff_isEmpty {c : C} : isEmpty c ↔ toMultiset c = 0 := by
  simp only [isEmpty_iff_sizeTM_eq_zero, sizeTM, Multiset.card_eq_zero]

alias ⟨toMultiset_of_isEmpty, _⟩ := toMultiset_iff_isEmpty

attribute [simp] toMultiset_of_isEmpty

lemma ToMultiset.not_isEmpty_of_mem {c : C} {x} (hx : x ∈ c) : ¬isEmpty c := by
  simpa [sizeTM, isEmpty_iff_sizeTM_eq_zero, Multiset.eq_zero_iff_forall_notMem] using ⟨x, hx⟩

end IsEmpty

variable [DecidableEq α]

theorem count_toMultiset_eq_zero {a : α} {c : C} : (toMultiset c).count a = 0 ↔ a ∉ c := by
  simp

theorem count_toMultiset_ne_zero {a : α} {c : C} : (toMultiset c).count a ≠ 0 ↔ a ∈ c := by
  simp [mem_toMultiset]

class Mergeable (C : Type*) (α : outParam Type*) [ToMultiset C α] where
  merge : C → C → C
  toMultiset_merge s t : toMultiset (merge s t) = toMultiset s + toMultiset t
export Mergeable (merge toMultiset_merge)

attribute [simp] toMultiset_merge

end ToMultiset
