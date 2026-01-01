/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.Bag
import Algorithm.Data.Classes.DefaultDict
import Algorithm.Data.Classes.GetElem

variable {C ι α : Type*}

class Dict.ReadOnly (C : Type*) (ι : outParam Type*) (α : outParam Type*) extends
    Bag.ReadOnly C ι,
    GetElem C ι α (fun c i ↦ i ∈ c)

class Dict (C : Type*) (ι : outParam Type*) (α : outParam Type*) extends
    Bag.ReadOnly C ι,
    EmptyCollection C, LawfulEmptyCollection C ι,
    GetSetEraseElem? C ι α (fun c i ↦ i ∈ c)

section Dict
variable [Dict C ι α]

instance : Dict.ReadOnly C ι α where

instance : Inhabited C where
  default := ∅

instance : LawfulErase C ι := lawfulErase_iff_toFinset.mpr fun c i ↦ by
  ext; simp [valid_erase, eq_comm]

def Dict.DefaultDict (C : Type*) := C

def Dict.toDefaultDict : C ≃ Dict.DefaultDict C := Equiv.refl _

instance : Inhabited (Dict.DefaultDict C) where
  default := Dict.toDefaultDict ∅

instance [Dict C ι α] : DefaultDict (Dict.DefaultDict C) ι (Option α) fun _ ↦ none where
  getElem a i _ := (Dict.toDefaultDict.symm a)[i]?
  toDFinsupp' a := .mk' ((Dict.toDefaultDict.symm a)[·]?)
    (.mk ⟨toMultiset (Dict.toDefaultDict.symm a), fun i ↦ by
      simp [mem_toMultiset, or_iff_not_imp_left] ⟩)
  coe_toDFinsupp'_eq_getElem := by simp
  setElem c i x := Dict.toDefaultDict <| alterElem (Dict.toDefaultDict.symm c) i (fun _ ↦ x)
  getElem_setElem_self := by simp
  getElem_setElem_of_ne _ _ _ _ hij := by simp [hij]
  getElem_default _ := by simpa [default] using getElem?_neg (cont := C) _ _ (not_mem_empty _)

end Dict
