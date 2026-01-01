/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.Bag

variable {α : Type*} [BEq α] [Hashable α]

namespace Std.HashSet

instance : LawfulEmptyCollection (HashSet α) α where
  not_mem_empty _ := not_mem_empty

variable [LawfulBEq α]

instance : ToFinset (HashSet α) α where
  isEmpty := isEmpty
  isEmpty_iff_forall_not_mem := isEmpty_iff_forall_not_mem
  toFinset c := ⟨c.toList, by simpa [List.Nodup] using c.inner.distinct_keys⟩
  mem_toFinset := by simp [toList]; rfl

instance : Size (HashSet α) where
  size := size
  size_eq_sizeTM _ := length_toList.symm

instance : Erase (HashSet α) α where
  erase := erase

instance : LawfulErase (HashSet α) α := lawfulErase_iff_toFinset.mpr fun _ a ↦ by
  ext; simp [Erase.erase, mem_erase, eq_comm (a := a)]

instance : Bag (HashSet α) α where
  toFinset_insert a c {_} := by
    ext; simp [mem_insert, eq_comm (a := a)]

end Std.HashSet
