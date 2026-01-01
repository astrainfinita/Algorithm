
/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.DFinsupp'.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
Modified from `Mathlib.Data.DFinsupp.Basic`
-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

open BigOperators

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variable {d : ∀ i, β i} {d₁ : ∀ i, β₁ i} {d₂ : ∀ i, β₂ i}
variable [DecidableEq ι]

namespace DFinsupp'

section ProdAndSum

/-- `DFinsupp'.prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive /-- `DFinsupp'.sum f g` is the sum of `g i (f i)` over the support of `f`. -/]
def prod [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid γ] (f : Π₀' i, [β i, d i])
    (g : ∀ i, β i → γ) : γ :=
  ∏ i ∈ f.support, g i (f i)

@[to_additive (attr := simp)]
theorem _root_.map_dfinsupp'_prod
    {R S H : Type*} [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid R] [CommMonoid S]
    [FunLike H R S] [MonoidHomClass H R S] (h : H) (f : Π₀' i, [β i, d i])
    (g : ∀ i, β i → R) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod _ _ _

@[to_additive]
theorem prod_mapRange_index
    [∀ (i) (x : β₁ i), Decidable (x ≠ d₁ i)] [∀ (i) (x : β₂ i), Decidable (x ≠ d₂ i)]
    [CommMonoid γ] {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i (d₁ i) = d₂ i}
    {g : Π₀' i, [β₁ i, d₁ i]} {h : ∀ i, β₂ i → γ}
    (h0 : ∀ i, h i (d₂ i) = 1) : (mapRange f hf g).prod h = g.prod fun i b => h i (f i b) := by
  rw [mapRange_def]
  refine (Finset.prod_subset support_mk_subset ?_).trans ?_
  · intro i h1 h2
    simp only [mem_support_toFun, ne_eq] at h1
    simp only [Finset.coe_sort_coe, mem_support_toFun, mk_apply, ne_eq, h1, not_false_iff,
      dite_eq_ite, ite_true, not_not] at h2
    simp [h2, h0]
  · refine Finset.prod_congr rfl ?_
    intro i h1
    simp only [mem_support_toFun, ne_eq] at h1
    simp [h1]

@[to_additive]
theorem prod_default_index [∀ (i) (x : β i), Decidable (x ≠ d i)]
    [CommMonoid γ] {h : ∀ i, β i → γ} : (default : Π₀' i, [β i, d i]).prod h = 1 :=
  rfl

@[to_additive]
theorem prod_single_index [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid γ]
    {i : ι} {b : β i} {h : ∀ i, β i → γ} (hd : h i (d i) = 1) :
    (single d i b).prod h = h i b := by
  by_cases h : b ≠ d i
  · simp [DFinsupp'.prod, support_single_ne h]
  · rw [not_not] at h
    simp [h, prod_default_index, hd]

@[to_additive]
theorem prod_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} [DecidableEq ι₁]
    [DecidableEq ι₂] {d₁ : ∀ i, β₁ i} {d₂ : ∀ i, β₂ i} [∀ (i) (x : β₁ i), Decidable (x ≠ d₁ i)]
    [∀ (i) (x : β₂ i), Decidable (x ≠ d₂ i)] [CommMonoid γ] (f₁ : Π₀' i, [β₁ i, d₁ i])
    (f₂ : Π₀' i, [β₂ i, d₂ i]) (h : ∀ i, β₁ i → ∀ i, β₂ i → γ) :
    (f₁.prod fun i₁ x₁ => f₂.prod fun i₂ x₂ => h i₁ x₁ i₂ x₂) =
      f₂.prod fun i₂ x₂ => f₁.prod fun i₁ x₁ => h i₁ x₁ i₂ x₂ :=
  Finset.prod_comm

@[to_additive (attr := simp)]
theorem prod_one [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid γ]
    {f : Π₀' i, [β i, d i]} : (f.prod fun _ _ => (1 : γ)) = 1 :=
  Finset.prod_const_one

@[to_additive (attr := simp)]
theorem prod_mul [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid γ]
    {f : Π₀' i, [β i, d i]} {h₁ h₂ : ∀ i, β i → γ} :
    (f.prod fun i b => h₁ i b * h₂ i b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib

@[to_additive (attr := simp)]
theorem prod_inv [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommGroup γ]
    {f : Π₀' i, [β i, d i]} {h : ∀ i, β i → γ} : (f.prod fun i b => (h i b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (invMonoidHom : γ →* γ) _ f.support).symm

@[to_additive]
theorem prod_eq_one [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid γ]
    {f : Π₀' i, [β i, d i]} {h : ∀ i, β i → γ} (hyp : ∀ i, h i (f i) = 1) : f.prod h = 1 :=
  Finset.prod_eq_one fun i _ => hyp i

theorem smul_sum {α : Type*} [Monoid α] [∀ (i) (x : β i), Decidable (x ≠ d i)]
    [AddCommMonoid γ] [DistribMulAction α γ] {f : Π₀' i, [β i, d i]} {h : ∀ i, β i → γ} {c : α} :
    c • f.sum h = f.sum fun a b => c • h a b :=
  Finset.smul_sum

@[to_additive]
theorem _root_.dfinsupp'_prod_mem [∀ (i) (x : β i), Decidable (x ≠ d i)]
    [CommMonoid γ] {S : Type*} [SetLike S γ] [SubmonoidClass S γ]
    (s : S) (f : Π₀' i, [β i, d i]) (g : ∀ i, β i → γ)
    (h : ∀ c, f c ≠ d c → g c (f c) ∈ s) : f.prod g ∈ s :=
  prod_mem fun _ hi => h _ <| mem_support_iff.1 hi

@[to_additive (attr := simp)]
theorem prod_eq_prod_fintype [Fintype ι] [∀ (i : ι) (x : β i), Decidable (x ≠ d i)]
    -- Porting note: `f` was a typeclass argument
    [CommMonoid γ] (v : Π₀' i, [β i, d i]) {f : ∀ i, β i → γ} (hf : ∀ i, f i (d i) = 1) :
    v.prod f = ∏ i, f i (DFinsupp'.equivFunOnFintype v i) := by
  suffices (∏ i ∈ v.support, f i (v i)) = ∏ i, f i (v i) by simp [DFinsupp'.prod, this]
  apply Finset.prod_subset v.support.subset_univ
  intro i _ hi
  rw [mem_support_iff, not_not] at hi
  rw [hi, hf]

section CommMonoidWithZero
variable [CommMonoidWithZero γ] [Nontrivial γ] [NoZeroDivisors γ]
  [Π i, DecidableEq (β i)] {f : Π₀' i, [β i, d i]} {g : Π i, β i → γ}

@[simp]
lemma prod_eq_zero_iff : f.prod g = 0 ↔ ∃ i ∈ f.support, g i (f i) = 0 := Finset.prod_eq_zero_iff
lemma prod_ne_zero_iff : f.prod g ≠ 0 ↔ ∀ i ∈ f.support, g i (f i) ≠ 0 := Finset.prod_ne_zero_iff

end CommMonoidWithZero

@[to_additive]
theorem prod_subtypeDomain_index [∀ (i) (x : β i), Decidable (x ≠ d i)]
    [CommMonoid γ] {v : Π₀' i, [β i, d i]} {p : ι → Prop} [DecidablePred p] {h : ∀ i, β i → γ}
    (hp : ∀ x ∈ v.support, p x) : (v.subtypeDomain p).prod (fun i b => h i b) = v.prod h := by
  refine Finset.prod_bij (fun p _ ↦ p) ?_ ?_ ?_ ?_ <;> aesop

end ProdAndSum

end DFinsupp'

section

namespace MonoidHom

variable {R S : Type*}
variable [∀ (i) (x : β i), Decidable (x ≠ d i)]

@[to_additive (attr := simp, norm_cast)]
theorem coe_dfinsupp'_prod [Monoid R] [CommMonoid S]
    (f : Π₀' i, [β i, d i]) (g : ∀ i, β i → R →* S) :
    ⇑(f.prod g) = f.prod fun a b => ⇑(g a b) :=
  coe_finset_prod _ _

@[to_additive]
theorem dfinsupp'_prod_apply [Monoid R] [CommMonoid S]
    (f : Π₀' i, [β i, d i]) (g : ∀ i, β i → R →* S) (r : R) :
    (f.prod g) r = f.prod fun a b => (g a b) r :=
  finset_prod_apply _ _ _

end MonoidHom

end
