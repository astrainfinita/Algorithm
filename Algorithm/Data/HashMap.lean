/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.Dict

namespace Std.HashMap
variable {ι α : Type*} [BEq ι] [Hashable ι]

instance : LawfulEmptyCollection (HashMap ι α) ι where
  not_mem_empty _ := not_mem_empty

variable [LawfulBEq ι]

instance : ToFinset (HashMap ι α) ι where
  isEmpty := isEmpty
  isEmpty_iff_forall_not_mem := isEmpty_iff_forall_not_mem
  toFinset c := ⟨c.keys, by simpa [List.Nodup] using c.distinct_keys⟩
  mem_toFinset := by simp

instance : Size (HashMap ι α) where
  size := size
  size_eq_sizeTM := by simp [sizeTM_eq_card_toFinset, toFinset]

instance : Dict (HashMap ι α) ι α where
  setElem := insert
  valid_setElem := by simp
  getElem_setElem_self := by simp
  getElem_setElem_of_ne _ _ _ _ hij := by simp [getElem_insert, hij]
  erase := erase
  valid_erase := by simp
  getElem_erase_of_ne := by simp

end Std.HashMap
