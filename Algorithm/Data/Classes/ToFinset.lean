/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToMultiset
import Mathlib.Data.Finset.Card

variable {C α : Type*}

class ToFinset (C : Type*) (α : outParam Type*) extends Membership α C, Membership.IsEmpty C where
  toFinset : C → Finset α
  mem c a := a ∈ toFinset c
  mem_toFinset {x c} : x ∈ toFinset c ↔ x ∈ c := by rfl
export ToFinset (toFinset mem_toFinset)

attribute [simp] mem_toFinset

class ToFinset.LawfulInsert (C : Type*) (α : outParam Type*)
    [ToFinset C α] [Insert α C] : Prop where
  toFinset_insert a (c : C) : [DecidableEq α] → toFinset (insert a c) = Insert.insert a (toFinset c)
export ToFinset.LawfulInsert (toFinset_insert)

attribute [simp] toFinset_insert

section ToFinset

variable [ToFinset C α] (c : C)

instance (priority := 100) ToFinset.toToMultiset : ToMultiset C α where
  toMultiset c := (toFinset c).val
  mem_toMultiset := mem_toFinset

lemma card_toFinset : (toFinset c).card = sizeTM c := rfl

lemma sizeTM_eq_card_toFinset : sizeTM c = (toFinset c).card := rfl

@[simp]
lemma toFinset_val : (toFinset c).val = toMultiset c := rfl

lemma nodup_toMultiset : (toMultiset c).Nodup := (toFinset c).nodup

section LawfulEmptyCollection
variable [EmptyCollection C]

lemma lawfulEmptyCollection_iff_toFinset :
    LawfulEmptyCollection C α ↔ toFinset (∅ : C) = ∅ := by
  simp_rw [lawfulEmptyCollection_iff, Finset.eq_empty_iff_forall_notMem, mem_toFinset]

alias ⟨_, LawfulEmptyCollection.of_toFinset⟩ := lawfulEmptyCollection_iff_toFinset

@[simp]
lemma toFinset_empty [LawfulEmptyCollection C α] :
    toFinset (∅ : C) = ∅ := by
  rwa [← lawfulEmptyCollection_iff_toFinset]

end LawfulEmptyCollection

section LawfulErase
variable [Erase C α]

lemma lawfulErase_iff_toFinset :
    LawfulErase C α ↔ ∀ [DecidableEq α] (c : C) a, toFinset (erase c a) = (toFinset c).erase a := by
  simp [lawfulErase_iff_toMultiset, ← Finset.val_inj]

@[simp]
lemma toFinset_erase [LawfulErase C α] [DecidableEq α] (c : C) a :
    toFinset (erase c a) = (toFinset c).erase a := by
  exact lawfulErase_iff_toFinset.mp inferInstance c a

end LawfulErase

end ToFinset
