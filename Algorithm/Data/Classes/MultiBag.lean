/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToMultiset

abbrev DecidableMem (α : Type*) (C : Type*) [Membership α C] :=
  ∀ (a : α) (c : C), Decidable (a ∈ c)

class MultiBag.ReadOnly (C : Type*) (α : outParam Type*) extends
    ToMultiset C α where
  [decidableMem : DecidableMem α C]
  count : α → C → Nat
  count_eq_count_toMultiset : [DecidableEq α] → ∀ a c,
    count a c = (toMultiset c).count a := by intros; rfl
export MultiBag.ReadOnly (count count_eq_count_toMultiset)

class MultiBag (C : Type*) (α : outParam Type*) extends
    MultiBag.ReadOnly C α,
    EmptyCollection C, LawfulEmptyCollection C α,
    Insert α C, ToMultiset.LawfulInsert C α,
    Erase C α, LawfulErase C α

attribute [instance 100] MultiBag.ReadOnly.decidableMem

attribute [simp] count_eq_count_toMultiset toMultiset_insert

section MultiBag.ReadOnly
variable {C α : Type*} [MultiBag.ReadOnly C α] (c : C)

theorem count_eq_zero {a : α} {c : C} : count a c = 0 ↔ a ∉ c := by
  classical exact count_eq_count_toMultiset a c ▸ count_toMultiset_eq_zero

theorem count_ne_zero {a : α} {c : C} : count a c ≠ 0 ↔ a ∈ c := by
  classical exact count_eq_count_toMultiset a c ▸ count_toMultiset_ne_zero

end MultiBag.ReadOnly
