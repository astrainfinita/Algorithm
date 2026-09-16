module

public import Algorithm.Data.Classes.GetElem

public section

section AllValid

variable {C ι α : Type*} [GetElemAllValid C ι α]

-- Public statements must retain the compound collection/index in the proof arguments.
theorem getElem_rw_collection (f : C → C) (c d : C) (i : ι) (h : f c = d) :
    (f c)[i] = d[i] := by
  rw [h]

theorem getElem_rw_index (c : C) (f : ι → ι) (i j : ι) (h : f i = j) :
    c[f i] = c[j] := by
  rw [h]

end AllValid

-- Partial indexing still uses the standard bounds tactic.
theorem array_getElem_fallback (xs : Array Nat) (i : Nat) (h : i + 1 < xs.size) :
    xs[i] = xs[i]'(by omega) := rfl

-- The fallback must still reject out-of-bounds accesses.
example (xs : Array Nat) : xs = xs := by
  fail_if_success let x := xs[xs.size]
  rfl

namespace PrivateFallback

-- The body is private, so public proofs cannot discharge validity by unfolding it.
def Valid (_ : Unit) (_ : Nat) : Prop := True

private theorem valid_all (c : Unit) (i : Nat) : Valid c i := True.intro

instance : GetElem Unit Nat Nat Valid where
  getElem _ i _ := i

macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| exact valid_all _ _)

-- The fallback must retain native abstraction so tactics can use private lemmas.
theorem lookup (i : Nat) : ()[i] = i := rfl

end PrivateFallback
