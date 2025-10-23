/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Set.Finite.Basic

/-!
Modified from `Mathlib.Data.DFinsupp.Basic`
-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variable {d : ∀ i, β i} {d₁ : ∀ i, β₁ i} {d₂ : ∀ i, β₂ i}
variable (β)

/-- A dependent function `Π i, β i` with finite support, with notation `Π₀' i, [β i, d i]`.

Note that `DFinsupp'.support` is the preferred API for accessing the support of the function,
`DFinsupp'.support'` is an implementation detail that aids computability; see the implementation
notes in this file for more information. -/
structure DFinsupp' (d : ∀ i, β i) : Type max u v where mk' ::
  /-- The underlying function of a dependent function with finite support (aka `DFinsupp'`). -/
  toFun : ∀ i, β i
  /-- The support of a dependent function with finite support (aka `DFinsupp'`). -/
  support' : Trunc { s : Multiset ι // ∀ i, i ∈ s ∨ toFun i = d i }

variable {β}

/--
`Π₀' i, [β i, d i]` denotes the type of dependent functions with finite support `DFinsupp β d`.
-/
notation3 "Π₀' "(...)", ""[" β:(scoped β => β) ", " d:(scoped d => d) "]" => DFinsupp' β d

/--
`ι →₀' [β, d]` denotes the type of functions with finite support
`DFinsupp' (fun _ : ι ↦ β) (fun _ : ι ↦ d)`.
-/
notation3 ι " →₀' ""[" β ", " d "]" => DFinsupp' (fun _ : ι ↦ β) (fun _ : ι ↦ d)

namespace DFinsupp'

section Basic

instance instDFunLike : DFunLike (Π₀' i, [β i, d i]) ι β :=
  ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ ↦ fun (h : f₁ = f₂) ↦ by
    subst h
    congr
    apply Subsingleton.elim ⟩

/-- Helper instance for when there are too many metavariables to apply `DFunLike.coeFunForall`
directly. -/
instance instCoeFun : CoeFun (Π₀' i, [β i, d i]) fun _ => ∀ i, β i :=
  inferInstance

@[simp]
theorem toFun_eq_coe (f : Π₀' i, [β i, d i]) : f.toFun = f :=
  rfl

@[ext]
theorem ext {f g : Π₀' i, [β i, d i]} (h : ∀ i, f i = g i) : f = g :=
  DFunLike.ext _ _ h

lemma ne_iff {f g : Π₀' i, [β i, d i]} : f ≠ g ↔ ∃ i, f i ≠ g i := DFunLike.ne_iff

instance instInhabited : Inhabited (Π₀' i, [β i, d i]) :=
  ⟨⟨d, Trunc.mk <| ⟨∅, fun _ => Or.inr rfl⟩⟩⟩

@[simp, norm_cast] lemma coe_mk' (f : ∀ i, β i) (s) : ⇑(⟨f, s⟩ : Π₀' i, [β i, d i]) = f := rfl

@[simp, norm_cast] lemma coe_default : ⇑(default : Π₀' i, [β i, d i]) = d := rfl

theorem default_apply (i : ι) : (default : Π₀' i, [β i, d i]) i = d i :=
  rfl

/-! ### Declarations about `mapRange` -/


section mapRange

/-- The composition of `f : ∀ i, β₁ i → β₂ i` and `g : Π₀' i, [β₁ i, d₁ i]` is
  `mapRange f hf g : Π₀ i, [β₂ i, d₂ i]`, well defined when `f i (d₁ i) = d₂ i`.
-/
def mapRange (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i (d₁ i) = d₂ i)
    (x : Π₀' i, [β₁ i, d₁ i]) : Π₀' i, [β₂ i, d₂ i] :=
  ⟨fun i => f i (x i),
    x.support'.map fun s => ⟨s.1, fun i => (s.2 i).imp_right fun h : x i = d₁ i => by
      rw [← hf i, ← h]⟩⟩

@[simp]
theorem mapRange_apply (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i (d₁ i) = d₂ i)
    (g : Π₀' i, [β₁ i, d₁ i]) (i : ι) : mapRange f hf g i = f i (g i) :=
  rfl

@[simp]
theorem mapRange_id (h : ∀ i, id (d₁ i) = d₁ i := fun _ => rfl)
    (g : Π₀' i : ι, [β₁ i, d₁ i]) : mapRange (fun i => (id : β₁ i → β₁ i)) h g = g := by
  ext
  rfl

theorem mapRange_comp (f : ∀ i, β₁ i → β₂ i) (f₂ : ∀ i, β i → β₁ i)
    (hf : ∀ i, f i (d₁ i) = d₂ i) (hf₂ : ∀ i, f₂ i (d i) = d₁ i)
    (h : ∀ i, (f i ∘ f₂ i) (d i) = d₂ i) (g : Π₀' i : ι, [β i, d i]) :
    mapRange (fun i => f i ∘ f₂ i) h g = mapRange f hf (mapRange f₂ hf₂ g) := by
  ext
  simp only [mapRange_apply]; rfl

@[simp]
theorem mapRange_default (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i (d₁ i) = d₂ i) :
    mapRange f hf (default : Π₀' i, [β₁ i, d₁ i]) = d₂ := by
  ext
  simp only [mapRange_apply, coe_default, hf]

end mapRange

/-! ### Declarations about `zipWith` -/


section zipWith

/-- Let `f i` be a binary operation `β₁ i → β₂ i → β i` such that `f i (d₁ i) (d₂ i) = d i`.
Then `zipWith f hf` is a binary operation
`Π₀' i, [β₁ i, d₁ i] → Π₀' i, [β₂ i, d₂ i] → Π₀' i, [β i, d i]`. -/
def zipWith (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i (d₁ i) (d₂ i) = d i)
    (x : Π₀' i, [β₁ i, d₁ i]) (y : Π₀' i, [β₂ i, d₂ i]) :
    Π₀' i, [β i, d i] :=
  ⟨fun i => f i (x i) (y i), by
    refine x.support'.bind fun xs => ?_
    refine y.support'.map fun ys => ?_
    refine ⟨xs + ys, fun i => ?_⟩
    obtain h1 | (h1 : x i = d₁ i) := xs.prop i
    · left
      rw [Multiset.mem_add]
      left
      exact h1
    obtain h2 | (h2 : y i = d₂ i) := ys.prop i
    · left
      rw [Multiset.mem_add]
      right
      exact h2
    right; rw [← hf, ← h1, ← h2]⟩

@[simp]
theorem zipWith_apply (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i (d₁ i) (d₂ i) = d i)
    (g₁ : Π₀' i, [β₁ i, d₁ i])
    (g₂ : Π₀' i, [β₂ i, d₂ i]) (i : ι) : zipWith f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
  rfl

@[simp]
theorem zipWith_default_left (f : ∀ i, β i → β i → β i)
    (hf : ∀ i x, f i (d i) x = x) (x : Π₀' i, [β i, d i]) :
    zipWith f (fun _ ↦ hf _ _) default x = x := by
  ext
  simp [hf]

@[simp]
theorem zipWith_default_right (f : ∀ i, β i → β i → β i)
    (hf : ∀ i x, f i x (d i) = x) (x : Π₀' i, [β i, d i]) :
    zipWith f (fun _ ↦ hf _ _) x default = x := by
  ext
  simp [hf]

@[simp]
theorem zipWith_swap (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i (d₁ i) (d₂ i) = d i)
    (x : Π₀' i, [β₂ i, d₂ i]) (y : Π₀' i, [β₁ i, d₁ i]) :
    zipWith (fun i x y ↦ f i y x) hf x y = zipWith f hf y x := by
  ext; rfl

end zipWith

end Basic

section Basic

theorem finite_support (f : Π₀' i, [β i, d i]) : Set.Finite { i | f i ≠ d i } :=
  Trunc.induction_on f.support' fun xs ↦
    xs.1.finite_toSet.subset fun i H ↦ ((xs.prop i).resolve_right H)

section mk

variable [DecidableEq ι]

variable (d) in
/-- Create an element of `Π₀' i, [β i, d i]` from a finset `s` and a function `x`
defined on this `Finset`. -/
def mk (s : Finset ι) (x : ∀ i : (↑s : Set ι), β (i : ι)) : Π₀' i, [β i, d i] :=
  ⟨fun i => if H : i ∈ s then x ⟨i, H⟩ else d i,
    Trunc.mk ⟨s.1, fun i => if H : i ∈ s then Or.inl H else Or.inr <| dif_neg H⟩⟩

variable {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i} {i : ι}

@[simp]
theorem mk_apply : (mk d s x : ∀ i, β i) i = if H : i ∈ s then x ⟨i, H⟩ else d i :=
  rfl

theorem mk_of_mem (hi : i ∈ s) : (mk d s x : ∀ i, β i) i = x ⟨i, hi⟩ :=
  dif_pos hi

theorem mk_of_not_mem (hi : i ∉ s) : (mk d s x : ∀ i, β i) i = d i :=
  dif_neg hi

variable (d) in
theorem mk_injective (s : Finset ι) : Function.Injective (@mk ι β d _ s) := by
  intro x y H
  ext i
  have h1 : (mk d s x : ∀ i, β i) i = (mk d s y : ∀ i, β i) i := by rw [H]
  obtain ⟨i, hi : i ∈ s⟩ := i
  dsimp only [mk_apply, Subtype.coe_mk] at h1
  simpa only [dif_pos hi] using h1

end mk

instance unique [∀ i, Subsingleton (β i)] : Unique (Π₀' i, [β i, d i]) :=
  DFunLike.coe_injective.unique

instance uniqueOfIsEmpty [IsEmpty ι] : Unique (Π₀' i, [β i, d i]) :=
  DFunLike.coe_injective.unique

/-- Given `Fintype ι`, `equivFunOnFintype` is the `Equiv` between `Π₀' i, [β i, d i]` and
  `Π i, β i`. (All dependent functions on a finite type are finitely supported.) -/
@[simps apply]
def equivFunOnFintype [Fintype ι] : (Π₀' i, [β i, d i]) ≃ ∀ i, β i
    where
  toFun := (⇑)
  invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun _ => Or.inl <| Finset.mem_univ_val _⟩⟩
  left_inv _ := DFunLike.coe_injective rfl
  right_inv _ := rfl

@[simp]
theorem equivFunOnFintype_symm_coe [Fintype ι] (f : Π₀' i, [β i, d i]) :
    equivFunOnFintype.symm f = f :=
  Equiv.symm_apply_apply _ _

@[simp]
theorem coe_equivFunOnFintype_symm [Fintype ι] (f : ∀ i, β i) :
    (equivFunOnFintype (d := d)).symm f = f :=
  (equivFunOnFintype (d := d)).apply_symm_apply _

/-! ### Declarations about `single` -/


section single

variable [DecidableEq ι]

variable (d) in
/-- The function `single i b : Π₀' i, [β i, d i]` sends `i` to `b`
and all other points to `d i`. -/
def single (i : ι) (b : β i) : Π₀' i, [β i, d i] :=
  ⟨Function.update d i b, Trunc.mk
    ⟨{i}, fun j => (Decidable.eq_or_ne j i).imp (by simp) fun h => Function.update_of_ne h _ _⟩⟩

theorem single_eq_functionUpdate {i b} : ⇑(single d i b) = Function.update d i b :=
  rfl

@[simp]
theorem single_apply {i i' b} :
    (single d i b : Π₀' i, [β i, d i]) i' = if h : i = i' then Eq.recOn h b else d i' := by
  rw [single_eq_functionUpdate, Function.update]
  simp [@eq_comm _ i i']

@[simp]
theorem single_eq_self (i) : single d i (d i) = default :=
  DFunLike.coe_injective <| Function.update_eq_self _ _

-- @[simp] -- Porting note (#10618): simp can prove this
theorem single_eq_same {i b} : single d i b i = b := by
  simp only [single_apply, dite_eq_ite, ite_true]

theorem single_eq_of_ne {i i' b} (h : i ≠ i') : single d i b i' = d i' := by
  simp only [single_apply, dif_neg h]

theorem single_injective {i} : Function.Injective (single d i) := fun _ _ H =>
  Function.update_injective _ i <| DFunLike.coe_injective.eq_iff.mpr H

theorem single_eq_single_iff (i j : ι) (xi : β i) (xj : β j) :
    single d i xi = single d j xj ↔ i = j ∧ HEq xi xj ∨ xi = d i ∧ xj = d j := by
  constructor
  · intro h
    by_cases hij : i = j
    · subst hij
      exact Or.inl ⟨rfl, heq_of_eq (DFinsupp'.single_injective h)⟩
    · have h_coe : ⇑(DFinsupp'.single d i xi) = DFinsupp'.single d j xj := congr_arg (⇑) h
      have hci := congr_fun h_coe i
      have hcj := congr_fun h_coe j
      rw [DFinsupp'.single_eq_same] at hci hcj
      rw [DFinsupp'.single_eq_of_ne (Ne.symm hij)] at hci
      rw [DFinsupp'.single_eq_of_ne hij] at hcj
      exact Or.inr ⟨hci, hcj.symm⟩
  · rintro (⟨rfl, hxi⟩ | ⟨hi, hj⟩)
    · rw [eq_of_heq hxi]
    · rw [hi, hj, DFinsupp'.single_eq_self, DFinsupp'.single_eq_self]

/-- `DFinsupp'.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`DFinsupp'.single_injective` -/
theorem single_left_injective {b : ∀ i : ι, β i} (h : ∀ i, b i ≠ d i) :
    Function.Injective (fun i => single d i (b i) : ι → Π₀' i, [β i, d i]) := fun _ _ H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h _ hb.1).left

@[simp]
theorem single_eq_default {i : ι} {xi : β i} : single d i xi = default ↔ xi = d i := by
  rw [← single_eq_self i, single_eq_single_iff]
  simp

/-- Equality of sigma types is sufficient (but not necessary) to show equality of `DFinsupp'`s. -/
theorem single_eq_of_sigma_eq {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩) :
    DFinsupp'.single d i xi = DFinsupp'.single d j xj := by
  cases h
  rfl

@[simp]
theorem equivFunOnFintype_single [Fintype ι] (i : ι) (m : β i) :
    DFinsupp'.equivFunOnFintype (DFinsupp'.single d i m) = Function.update d i m := by
  ext x
  dsimp [Function.update]
  simp [@eq_comm _ i]

@[simp]
theorem equivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : β i) :
    DFinsupp'.equivFunOnFintype.symm (Function.update d i m) = DFinsupp'.single d i m := by
  ext i'
  simp only [← single_eq_functionUpdate, equivFunOnFintype_symm_coe]

section SingleAndZipWith

@[simp]
theorem zipWith_single_single (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i (d₁ i) (d₂ i) = d i)
    {i} (b₁ : β₁ i) (b₂ : β₂ i) :
    zipWith f hf (single d₁ i b₁) (single d₂ i b₂) = single d i (f i b₁ b₂) := by
  ext j
  rw [zipWith_apply]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rw [single_eq_same, single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hij, single_eq_of_ne hij, single_eq_of_ne hij, hf]

end SingleAndZipWith

end single

/-! ### Declarations about `update` -/


section update

variable [DecidableEq ι]

variable (f : Π₀' i, [β i, d i]) (i) (b : β i)

/-- Replace the value of a `Π₀' i, [β i, d i]` at a given point `i : ι` by a given value `b : β i`.
If `b = 0`, this amounts to removing `i` from the support.
Otherwise, `i` is added to it.

This is the (dependent) finitely-supported version of `Function.update`. -/
def update : Π₀' i, [β i, d i] :=
  ⟨Function.update f i b,
    f.support'.map fun s =>
      ⟨i ::ₘ s.1, fun j => by
        rcases eq_or_ne i j with (rfl | hi)
        · simp
        · obtain hj | (hj : f j = d j) := s.prop j
          · exact Or.inl (Multiset.mem_cons_of_mem hj)
          · exact Or.inr ((Function.update_of_ne hi.symm b _).trans hj)⟩⟩

@[simp, norm_cast] lemma coe_update : (f.update i b : ∀ i : ι, β i) = Function.update f i b := rfl

@[simp]
theorem update_self : f.update i (f i) = f := by
  ext
  simp

end update

/-! ### Declarations about `erase` -/


section erase

variable [DecidableEq ι]

/-- Redefine `f i` to be `d i`. -/
def erase (i : ι) (x : Π₀' i, [β i, d i]) : Π₀' i, [β i, d i] :=
  ⟨fun j ↦ if j = i then d j else x.1 j,
    x.support'.map fun xs ↦ ⟨xs.1, fun j ↦ (xs.prop j).imp_right (by simp only [·, ite_self])⟩⟩

@[simp]
theorem erase_apply {i j : ι} {f : Π₀' i, [β i, d i]} :
    (f.erase i) j = if j = i then d j else f j :=
  rfl

-- @[simp] -- Porting note (#10618): simp can prove this
theorem erase_same {i : ι} {f : Π₀' i, [β i, d i]} : (f.erase i) i = d i := by simp

theorem erase_ne {i i' : ι} {f : Π₀' i, [β i, d i]} (h : i' ≠ i) : (f.erase i) i' = f i' := by
  simp [h]

@[simp]
theorem erase_default (i : ι) : erase i (default : Π₀' i, [β i, d i]) = default :=
  ext fun _ => ite_self _

theorem erase_single (j : ι) (i : ι) (x : β i) :
    (single d i x).erase j = if i = j then default else single d i x := by
  ext k
  rw [erase_apply]
  split_ifs <;> simp [*]
  tauto

@[simp]
theorem erase_single_same (i : ι) (x : β i) : (single d i x).erase i = default := by
  rw [erase_single, if_pos rfl]

@[simp]
theorem erase_single_ne {i j : ι} (x : β i) (h : i ≠ j) :
    (single d i x).erase j = single d i x := by
  rw [erase_single, if_neg h]

@[simp]
theorem update_eq_erase (f : Π₀' i, [β i, d i]) (i : ι) :
    f.update i (d i) = f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp
  · simp [hi.symm]

end erase

end Basic

variable [DecidableEq ι]

theorem single_zipWith_erase (f : ∀ i, β i → β i → β i)
    (hf₁ : ∀ i x, f i (d i) x = x) (hf₂ : ∀ i x, f i x (d i) = x)
    (i : ι) (x : Π₀' i, [β i, d i]) :
    zipWith f (fun _ ↦ hf₁ _ _) (single d i (x i)) (x.erase i) = x :=
  ext fun i' =>
    if h : i = i' then by
      subst h; simp only [zipWith_apply, single_apply, erase_apply, hf₂, dite_eq_ite, if_true]
    else by
      simp only [zipWith_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), hf₁]

protected theorem induction_on {p : (Π₀' i, [β i, d i]) → Prop} (x : Π₀' i, [β i, d i])
    (f : ∀ i, β i → β i → β i) (hf₁ : ∀ i x, f i (d i) x = x) (hf₂ : ∀ i x, f i x (d i) = x)
    (h0 : p default)
    (ha : ∀ (i b) (x : Π₀' i, [β i, d i]), x i = d i → b ≠ d i → p x →
      p (zipWith f (fun _ ↦ hf₁ _ _) (single d i b) x)) :
    p x := by
  cases x with | _ x s
  induction s using Trunc.induction_on with | h s
  cases s with | _ s H
  induction s using Multiset.induction_on generalizing x with | empty | cons i s ih
  · have : x = d := funext fun i => (H i).resolve_left (Multiset.notMem_zero _)
    subst this
    exact h0
  have H2 : p (erase i ⟨x, Trunc.mk ⟨i ::ₘ s, H⟩⟩) := by
    dsimp only [erase, Trunc.map, Trunc.bind, Trunc.liftOn, Trunc.lift_mk,
      Function.comp, Subtype.coe_mk]
    have H2 : ∀ j, j ∈ s ∨ ite (j = i) (d j) (x j) = d j := by
      intro j
      cases H j with | _ H2
      · cases Multiset.mem_cons.1 H2 with | _ H3
        · right; exact if_pos H3
        · left; exact H3
      right
      split_ifs <;> [rfl; exact H2]
    have H3 : ∀ aux, (⟨fun j : ι => ite (j = i) (d j) (x j), Trunc.mk ⟨i ::ₘ s, aux⟩⟩ :
          Π₀' i, [β i, d i]) =
        ⟨fun j : ι => ite (j = i) (d j) (x j), Trunc.mk ⟨s, H2⟩⟩ :=
      fun _ ↦ ext fun _ => rfl
    rw [H3]
    apply ih
  have H3 : zipWith f (fun i ↦ hf₁ _ _) (single d i _) _ =
      (⟨x, Trunc.mk ⟨i ::ₘ s, H⟩⟩ : Π₀' i, [β i, d i]) :=
    single_zipWith_erase f hf₁ hf₂ _ _
  rw [← H3]
  change p (zipWith _ _ (single d i (x i)) _)
  cases Classical.em (x i = d i) with | _ h
  · rw [h, single_eq_self, zipWith_default_left]
    exact H2
  refine ha _ _ _ ?_ h H2
  rw [erase_same]

theorem induction_on' {p : (Π₀' i, [β i, d i]) → Prop} (x : Π₀' i, [β i, d i])
    (f : ∀ i, β i → β i → β i) (hf₁ : ∀ i x, f i (d i) x = x) (hf₂ : ∀ i x, f i x (d i) = x)
    (h0 : p default)
    (ha : ∀ (i b) (x : Π₀' i, [β i, d i]), x i = d i → b ≠ d i → p x →
      p (zipWith f (fun _ ↦ hf₁ _ _) x (single d i b))) : p x :=
  DFinsupp'.induction_on x (fun i x y ↦ f i y x) hf₂ hf₁ h0 <| by simpa only [zipWith_swap] using ha

section SupportBasic

variable [∀ (i) (x : β i), Decidable (x ≠ d i)]

/-- Set `{i | f x ≠ d i}` as a `Finset`. -/
def support (f : Π₀' i, [β i, d i]) : Finset ι :=
  (f.support'.lift fun xs => (Multiset.toFinset xs.1).filter fun i => f i ≠ d i) <| by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hy i).resolve_right h, h⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hx i).resolve_right h, h⟩

@[simp]
theorem support_mk_subset {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} : (mk d s x).support ⊆ s :=
  fun _ H => Multiset.mem_toFinset.1 (Finset.mem_filter.1 H).1

@[simp]
theorem support_mk'_subset {f : ∀ i, β i} {s : Multiset ι} {h} :
    (mk' f <| Trunc.mk ⟨s, h⟩ : Π₀' i, [β i, d i]).support ⊆ s.toFinset := fun i H =>
  Multiset.mem_toFinset.1 <| by simpa using (Finset.mem_filter.1 H).1

@[simp]
theorem mem_support_toFun (f : Π₀' i, [β i, d i]) (i) : i ∈ f.support ↔ f i ≠ d i := by
  cases f with | _ f s
  induction s using Trunc.induction_on with | h s
  dsimp only [support, Trunc.lift_mk]
  rw [Finset.mem_filter, Multiset.mem_toFinset, coe_mk']
  exact and_iff_right_of_imp (s.prop i).resolve_right

theorem eq_mk_support (f : Π₀' i, [β i, d i]) : f = mk d f.support fun i => f i := by aesop

@[simp]
theorem support_default : (default : Π₀' i, [β i, d i]).support = ∅ :=
  rfl

theorem mem_support_iff {f : Π₀' i, [β i, d i]} {i : ι} : i ∈ f.support ↔ f i ≠ d i :=
  f.mem_support_toFun _

theorem not_mem_support_iff {f : Π₀' i, [β i, d i]} {i : ι} : i ∉ f.support ↔ f i = d i :=
  not_iff_comm.1 mem_support_iff.symm

@[simp]
theorem support_eq_empty {f : Π₀' i, [β i, d i]} : f.support = ∅ ↔ f = default :=
  ⟨fun H => ext <| by simpa [Finset.ext_iff] using H, by simp (config := { contextual := true })⟩

instance decidableDefault : DecidablePred (Eq (default : Π₀' i, [β i, d i])) := fun _ =>
  decidable_of_iff _ <| support_eq_empty.trans eq_comm

theorem support_subset_iff {s : Set ι} {f : Π₀' i, [β i, d i]} :
    ↑f.support ⊆ s ↔ ∀ i ∉ s, f i = d i := by
  simp [Set.subset_def]; exact forall_congr' fun i => not_imp_comm

theorem support_single_ne {i : ι} {b : β i} (hb : b ≠ d i) :
    (single d i b).support = {i} := by
  ext j; by_cases h : i = j
  · subst h
    simp [hb]
  simp [Ne.symm h, h]

theorem support_single_subset {i : ι} {b : β i} : (single d i b).support ⊆ {i} :=
  support_mk'_subset

section MapRangeAndZipWith

theorem mapRange_def [∀ (i) (x : β₁ i), Decidable (x ≠ d₁ i)] {f : ∀ i, β₁ i → β₂ i}
    {hf : ∀ i, f i (d₁ i) = d₂ i} {g : Π₀' i, [β₁ i, d₁ i]} :
    mapRange f hf g = mk d₂ g.support fun i => f i.1 (g i.1) := by
  ext i
  by_cases h : g i ≠ d₁ i <;> simp at h <;> simp [h, hf]

@[simp]
theorem mapRange_single {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i (d₁ i) = d₂ i} {i : ι} {b : β₁ i} :
    mapRange f hf (single d₁ i b) = single d₂ i (f i b) :=
  DFinsupp'.ext fun i' => by
    by_cases h : i = i'
    · subst i'
      simp
    · simp [h, hf]

variable [∀ (i) (x : β₁ i), Decidable (x ≠ d₁ i)] [∀ (i) (x : β₂ i), Decidable (x ≠ d₂ i)]

theorem support_mapRange {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i (d₁ i) = d₂ i}
    {g : Π₀' i, [β₁ i, d₁ i]} : (mapRange f hf g).support ⊆ g.support := by simp [mapRange_def]

theorem zipWith_def {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
    [dec : DecidableEq ι] {d : ∀ i : ι, β i} {d₁ : ∀ i : ι, β₁ i} {d₂ : ∀ i : ι, β₂ i}
    [∀ (i : ι) (x : β₁ i), Decidable (x ≠ d₁ i)] [∀ (i : ι) (x : β₂ i), Decidable (x ≠ d₂ i)]
    {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i (d₁ i) (d₂ i) = d i}
    {g₁ : Π₀' i, [β₁ i, d₁ i]} {g₂ : Π₀' i, [β₂ i, d₂ i]} :
    zipWith f hf g₁ g₂ = mk d (g₁.support ∪ g₂.support) fun i => f i.1 (g₁ i.1) (g₂ i.1) := by
  ext i
  by_cases h1 : g₁ i ≠ d₁ i <;> by_cases h2 : g₂ i ≠ d₂ i <;> simp only [not_not, Ne] at h1 h2 <;>
    simp [h1, h2, hf]

theorem support_zipWith {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i (d₁ i) (d₂ i) = d i}
    {g₁ : Π₀' i, [β₁ i, d₁ i]} {g₂ : Π₀' i, [β₂ i, d₂ i]} :
    (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  simp [zipWith_def]

end MapRangeAndZipWith

theorem erase_def (i : ι) (f : Π₀' i, [β i, d i]) :
    f.erase i = mk d (f.support.erase i) fun j => f j.1 := by
  ext j
  by_cases h1 : j = i <;> by_cases h2 : f j ≠ d j <;> simp at h2 <;> simp [h1, h2]

@[simp]
theorem support_erase (i : ι) (f : Π₀' i, [β i, d i]) :
    (f.erase i).support = f.support.erase i := by
  ext j
  by_cases h1 : j = i
  · simp only [h1, mem_support_toFun, erase_apply, ite_true, ne_eq, not_true,
    Finset.mem_erase, false_and]
  · by_cases h2 : f j ≠ d j <;> simp at h2 <;> simp [h1, h2]

theorem support_update_ne (f : Π₀' i, [β i, d i]) (i : ι) {b : β i} (h : b ≠ d i) :
    support (f.update i b) = insert i f.support := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp [h]
  · simp [hi.symm]

theorem support_update (f : Π₀' i, [β i, d i]) (i : ι) (b : β i) [Decidable (b = d i)] :
    support (f.update i b) = if b = d i then support (f.erase i) else insert i f.support := by
  ext j
  split_ifs with hb
  · subst hb
    simp [update_eq_erase, support_erase]
  · rw [support_update_ne f _ hb]

end SupportBasic

instance instDecidableEq [∀ i, DecidableEq (β i)] : DecidableEq (Π₀' i, [β i, d i]) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ i ∈ f.support, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ => ext fun i => if h : i ∈ f.support then h₂ i h else by
      have hf : f i = d i := by rwa [mem_support_iff, not_not] at h
      have hg : g i = d i := by rwa [h₁, mem_support_iff, not_not] at h
      rw [hf, hg],
     by rintro rfl; simp⟩

end DFinsupp'
