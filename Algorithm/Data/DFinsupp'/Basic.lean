/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.DFinsupp'.Defs
import Mathlib.Data.Finset.Preimage

/-!
Modified from `Mathlib.Data.DFinsupp.Basic`
-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variable {d : ∀ i, β i} {d₁ : ∀ i, β₁ i} {d₂ : ∀ i, β₂ i}

namespace DFinsupp'

section Basic

section Piecewise

variable (x y : Π₀' i, [β i, d i]) (s : Set ι) [∀ i, Decidable (i ∈ s)]

/-- `x.piecewise y s` is the finitely supported function equal to `x` on the set `s`,
  and to `y` on its complement. -/
def piecewise : Π₀' i, [β i, d i] :=
  zipWith (fun i x y => if i ∈ s then x else y) (fun i => ite_self (d i)) x y

theorem piecewise_apply (i : ι) : x.piecewise y s i = if i ∈ s then x i else y i :=
  zipWith_apply _ _ x y i

@[simp, norm_cast]
theorem coe_piecewise : ⇑(x.piecewise y s) = s.piecewise x y := by
  ext
  apply piecewise_apply

end Piecewise

end Basic

section FilterAndSubtypeDomain

/-- `filter p f` is the function which is `f i` if `p i` is true and `d i` otherwise. -/
def filter (p : ι → Prop) [DecidablePred p] (x : Π₀' i, [β i, d i]) : Π₀' i, [β i, d i] :=
  ⟨fun i => if p i then x i else d i,
    x.support'.map fun xs =>
      ⟨xs.1, fun i => (xs.prop i).imp_right fun H : x i = d i => by simp only [H, ite_self]⟩⟩

@[simp]
theorem filter_apply (p : ι → Prop) [DecidablePred p] (i : ι) (f : Π₀' i, [β i, d i]) :
    f.filter p i = if p i then f i else d i :=
  rfl

theorem filter_apply_pos {p : ι → Prop} [DecidablePred p] (f : Π₀' i, [β i, d i]) {i : ι}
    (h : p i) : f.filter p i = f i := by simp only [filter_apply, if_pos h]

theorem filter_apply_neg {p : ι → Prop} [DecidablePred p] (f : Π₀' i, [β i, d i]) {i : ι}
    (h : ¬p i) : f.filter p i = d i := by simp only [filter_apply, if_neg h]

@[simp]
theorem filter_default (p : ι → Prop) [DecidablePred p] :
    (default : Π₀' i, [β i, d i]).filter p = d := by
  ext
  simp

/-- `subtypeDomain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtypeDomain (p : ι → Prop) [DecidablePred p] (x : Π₀' i, [β i, d i]) :
    Π₀' i : Subtype p, [β i, d i] :=
  ⟨fun i => x (i : ι),
    x.support'.map fun xs =>
      ⟨(Multiset.filter p xs.1).attach.map fun j => ⟨j.1, (Multiset.mem_filter.1 j.2).2⟩, fun i =>
        (xs.prop i).imp_left fun H =>
          Multiset.mem_map.2
            ⟨⟨i, Multiset.mem_filter.2 ⟨H, i.2⟩⟩, Multiset.mem_attach _ _, Subtype.eta _ _⟩⟩⟩

@[simp]
theorem subtypeDomain_default {p : ι → Prop} [DecidablePred p] :
    subtypeDomain p (default : Π₀' i, [β i, d i]) = Subtype.restrict p d :=
  rfl

@[simp]
theorem subtypeDomain_apply {p : ι → Prop} [DecidablePred p] {i : Subtype p}
    {v : Π₀' i, [β i, d i]} : (subtypeDomain p v) i = v i :=
  rfl

end FilterAndSubtypeDomain

section Basic

variable [DecidableEq ι]

variable {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i} {i : ι}

theorem filter_single (p : ι → Prop) [DecidablePred p] (i : ι) (x : β i) :
    (single d i x).filter p = if p i then single d i x else default := by
  ext j
  have := apply_ite (fun x : Π₀' i, [β i, d i] => x j) (p i) (single d i x) default
  dsimp at this
  rw [filter_apply, this]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · rw [single_eq_of_ne hij, ite_self, ite_self]

@[simp]
theorem filter_single_pos {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : p i) :
    (single d i x).filter p = single d i x := by rw [filter_single, if_pos h]

@[simp]
theorem filter_single_neg {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i) :
    (single d i x).filter p = default := by rw [filter_single, if_neg h]

theorem piecewise_single_erase (x : Π₀' i, [β i, d i]) (i : ι)
    [∀ i' : ι, Decidable <| (i' ∈ ({i} : Set ι))] : -- Porting note: added Decidable hypothesis
    (single d i (x i)).piecewise (x.erase i) {i} = x := by
  ext j; rw [piecewise_apply]; split_ifs with h
  · rw [(id h : j = i), single_eq_same]
  · exact erase_ne h

@[simp]
theorem filter_ne_eq_erase (f : Π₀' i, [β i, d i]) (i : ι) : f.filter (· ≠ i) = f.erase i := by
  ext1 j
  simp only [DFinsupp'.filter_apply, DFinsupp'.erase_apply, ite_not]

@[simp]
theorem filter_ne_eq_erase' (f : Π₀' i, [β i, d i]) (i : ι) : f.filter (i ≠ ·) = f.erase i := by
  rw [← filter_ne_eq_erase f i]
  congr with j
  exact ne_comm

end Basic

section SupportBasic

variable [DecidableEq ι]

variable [∀ (i) (x : β i), Decidable (x ≠ d i)]

/-- Equivalence between dependent functions with finite support `s : Finset ι` and functions
`∀ i, {x : β i // x ≠ d i}`. -/
@[simps]
def subtypeSupportEqEquiv (s : Finset ι) :
    {f : Π₀' i, [β i, d i] // f.support = s} ≃ ∀ i : s, {x : β i // x ≠ d i} where
  toFun | ⟨f, hf⟩ => fun ⟨i, hi⟩ ↦ ⟨f i, (f.mem_support_toFun i).1 <| hf.symm ▸ hi⟩
  invFun f := ⟨mk d s fun i ↦ (f i).1, Finset.ext fun i ↦ by
    -- TODO: `simp` fails to use `(f _).2` inside `∃ _, _`
    calc
      i ∈ support (mk d s fun i ↦ (f i).1) ↔ ∃ h : i ∈ s, (f ⟨i, h⟩).1 ≠ d i := by simp
      _ ↔ ∃ _ : i ∈ s, True := exists_congr fun h ↦ (iff_true _).mpr (f _).2
      _ ↔ i ∈ s := by simp⟩
  left_inv := by
    rintro ⟨f, rfl⟩
    ext i
    simpa using Eq.symm
  right_inv f := by
    ext1
    simp

/-- Equivalence between all dependent finitely supported functions `f : Π₀' i, [β i, d i]` and type
of pairs `⟨s : Finset ι, f : ∀ i : s, {x : β i // x ≠ d i}⟩`. -/
@[simps! apply_fst apply_snd_coe]
def sigmaFinsetFunEquiv : (Π₀' i, [β i, d i]) ≃ Σ s : Finset ι, ∀ i : s, {x : β i // x ≠ d i} :=
  (Equiv.sigmaFiberEquiv DFinsupp'.support).symm.trans (.sigmaCongrRight subtypeSupportEqEquiv)

section FilterAndSubtypeDomain

variable {p : ι → Prop} [DecidablePred p]

theorem filter_def (f : Π₀' i, [β i, d i]) :
    f.filter p = mk d (f.support.filter p) fun i => f i.1 := by
  ext i; by_cases h1 : p i <;> by_cases h2 : f i ≠ d i <;> simp at h2 <;> simp [h1, h2]

@[simp]
theorem support_filter (f : Π₀' i, [β i, d i]) : (f.filter p).support = f.support.filter p := by
  ext i; by_cases h : p i <;> simp [h]

theorem subtypeDomain_def (f : Π₀' i, [β i, d i]) :
    f.subtypeDomain p = mk _ (f.support.subtype p) fun i => f i := by
  ext i; by_cases h2 : f i ≠ d i <;> try simp at h2; dsimp; simp [h2]

@[simp, nolint simpNF] -- Porting note: simpNF claims that LHS does not simplify, but it does
theorem support_subtypeDomain {f : Π₀' i, [β i, d i]} :
    (subtypeDomain p f).support = f.support.subtype p := by
  ext i
  simp

end FilterAndSubtypeDomain

end SupportBasic

instance [DecidableEq ι] [∀ i, DecidableEq (β i)] : DecidableEq (Π₀' i, [β i, d i]) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ i ∈ f.support, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ => ext fun i => if h : i ∈ f.support then h₂ i h else by
      have hf : f i = d i := by rwa [mem_support_iff, not_not] at h
      have hg : g i = d i := by rwa [h₁, mem_support_iff, not_not] at h
      rw [hf, hg],
     by rintro rfl; simp⟩

section Equiv

open Finset

variable {κ : Type*}

/-- Reindexing (and possibly removing) terms of a `DFinsupp'`. -/
noncomputable def comapDomain [DecidableEq ι] (h : κ → ι) (hh : Function.Injective h)
    (f : Π₀' i, [β i, d i]) : Π₀' k, [β (h k), d (h k)] where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨((Multiset.toFinset s.1).preimage h hh.injOn).val, fun x =>
        (s.prop (h x)).imp_left fun hx => mem_preimage.mpr <| Multiset.mem_toFinset.mpr hx⟩

@[simp]
theorem comapDomain_apply [DecidableEq ι]
    (h : κ → ι) (hh : Function.Injective h) (f : Π₀' i, [β i, d i])
    (k : κ) : comapDomain h hh f k = f (h k) :=
  rfl

@[simp]
theorem comapDomain_default [DecidableEq ι] (h : κ → ι) (hh : Function.Injective h) :
    comapDomain h hh (default : Π₀' i, [β i, d i]) = default := by
  ext
  rw [default_apply, comapDomain_apply, default_apply]

@[simp]
theorem comapDomain_single [DecidableEq ι] [DecidableEq κ] (h : κ → ι) (hh : Function.Injective h)
    (k : κ) (x : β (h k)) : comapDomain h hh (single d (h k) x) = single _ k x := by
  ext i
  rw [comapDomain_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik.symm, single_eq_of_ne (hh.ne hik.symm)]

/-- A computable version of comapDomain when an explicit left inverse is provided. -/
def comapDomain' (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h)
    (f : Π₀' i, [β i, d i]) : Π₀' k, [β (h k), d (h k)] where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨Multiset.map h' s.1, fun x =>
        (s.prop (h x)).imp_left fun hx => Multiset.mem_map.mpr ⟨_, hx, hh' _⟩⟩

@[simp]
theorem comapDomain'_apply (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h)
    (f : Π₀' i, [β i, d i]) (k : κ) :
    comapDomain' h hh' f k = f (h k) :=
  rfl

@[simp]
theorem comapDomain'_default (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h) :
    comapDomain' h hh' (default : Π₀' i, [β i, d i]) = default := by
  ext
  rw [default_apply, comapDomain'_apply, default_apply]

/-- Reindexing terms of a `DFinsupp'`.

This is the `DFinsupp'` version of `Equiv.piCongrLeft'`. -/
@[simps apply]
def equivCongrLeft (h : ι ≃ κ) : (Π₀' i, [β i, d i]) ≃ Π₀' k, [β (h.symm k), d (h.symm k)]
    where
  toFun := comapDomain' h.symm h.right_inv
  invFun f :=
    mapRange (fun i => Equiv.cast <| congr_arg β <| h.symm_apply_apply i)
      (fun i => (Equiv.cast_eq_iff_heq _).mpr <| by rw [Equiv.symm_apply_apply])
      (@comapDomain' _ _ _ _ h _ h.left_inv f)
  left_inv f := by
    ext i
    rw [mapRange_apply, comapDomain'_apply, comapDomain'_apply, Equiv.cast_eq_iff_heq,
      h.symm_apply_apply]
  right_inv f := by
    ext k
    rw [comapDomain'_apply, mapRange_apply, comapDomain'_apply, Equiv.cast_eq_iff_heq,
      h.apply_symm_apply]

variable {α : Option ι → Type v} {dα : ∀ i, α i}

/-- Adds a term to a `DFinsupp'`, making a `DFinsupp'` indexed by an `Option`.

This is the `DFinsupp'` version of `Option.rec`. -/
def extendWith (a : α none) (f : Π₀' i, [α (some i), dα (some i)]) : Π₀' i, [α i, dα i] where
  toFun := fun i ↦ match i with | none => a | some _ => f _
  support' :=
    f.support'.map fun s =>
      ⟨none ::ₘ Multiset.map some s.1, fun i =>
        Option.rec (Or.inl <| Multiset.mem_cons_self _ _)
          (fun i =>
            (s.prop i).imp_left fun h => Multiset.mem_cons_of_mem <| Multiset.mem_map_of_mem _ h)
          i⟩

@[simp]
theorem extendWith_none (f : Π₀' i, [α (some i), dα (some i)]) (a : α none) :
    f.extendWith a none = a :=
  rfl

@[simp]
theorem extendWith_some (f : Π₀' i, [α (some i), dα (some i)]) (a : α none) (i : ι) :
    f.extendWith a (some i) = f i :=
  rfl

@[simp]
theorem extendWith_single [DecidableEq ι] (i : ι) (x : α (some i)) :
    (single _ i x).extendWith (dα none) = single dα (some i) x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_of_ne (Option.some_ne_none _)]
  · rw [extendWith_some]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hij, single_eq_of_ne ((Option.some_injective _).ne hij)]

@[simp]
theorem extendWith_default [DecidableEq ι] (x : α none) :
    (default : Π₀' i, [α (some i), dα (some i)]).extendWith x = single dα none x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_same]
  · rw [extendWith_some, single_eq_of_ne (Option.some_ne_none _).symm, default_apply]

/-- Bijection obtained by separating the term of index `none` of a `DFinsupp'` over `Option ι`.

This is the `DFinsupp'` version of `Equiv.piOptionEquivProd`. -/
@[simps]
noncomputable def equivProdDFinsupp' [DecidableEq ι] :
    (Π₀' i, [α i, dα i]) ≃ α none × Π₀' i, [α (some i), dα (some i)] where
  toFun f := (f none, comapDomain some (Option.some_injective _) f)
  invFun f := f.2.extendWith f.1
  left_inv f := by
    ext i
    cases i with
    | none => rw [extendWith_none]
    | some i => rw [extendWith_some, comapDomain_apply]
  right_inv x := by
    dsimp only
    ext
    · exact extendWith_none x.snd _
    · rw [comapDomain_apply, extendWith_some]

end Equiv

end DFinsupp'
