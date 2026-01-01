/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Lean.Meta.Tactic.Simp.RegisterCommand

/-- The simpset `getElem_simps` is used by the tactic `get_elem_tactic_extensible`. -/
register_simp_attr getElem_simps

macro_rules
| `(tactic| get_elem_tactic_extensible) =>
  `(tactic| simp +contextual only [getElem_simps,
    ne_eq, ite_true, ite_false, dite_true, dite_false,
    ite_cond_eq_true, ite_cond_eq_false, dite_cond_eq_true, dite_cond_eq_false, ite_self,
    and_true, true_and, and_false, false_and, and_self, and_not_self, not_and_self,
    and_imp, not_and, or_self, or_true, true_or, or_false, false_or,
    iff_self, iff_true, true_iff, iff_false, false_iff, false_implies, forall_false,
    implies_true, true_implies, not_false_eq_true, not_true_eq_false, not_iff_self,
    ne_eq, *] at *; done)

/-
was `simp_all [getElem_simps]`

TODO: make a better tactic. `simp` lemmas about `?Valid ?c[?i ↦ ?x] ?j` is so bad.
-/
