/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Algorithm.Data.DFinsupp.Defs
public import Mathlib.Data.Fintype.Pi

/-!
Modified from `Mathlib.Data.DFinsupp.Basic`
-/

@[expose] public section

instance DFinsupp'.fintype {ι : Type*} {π : ι → Type*} [DecidableEq ι] {dπ : ∀ i, π i}
    [Fintype ι] [∀ i, Fintype (π i)] : Fintype (Π₀' i, [π i, dπ i]) :=
  Fintype.ofEquiv (∀ i, π i) DFinsupp'.equivFunOnFintype.symm

instance DFinsupp'.infinite_of_left {ι : Type*} {π : ι → Type*} [∀ i, Nontrivial (π i)]
    {dπ : ∀ i, π i} [Infinite ι] : Infinite (Π₀' i, [π i, dπ i]) := by
  letI := Classical.decEq ι; choose m hm using fun i => exists_ne (dπ i : π i);
    exact Infinite.of_injective _ (DFinsupp'.single_left_injective hm)

/-- See `DFinsupp'.infinite_of_right` for this in instance form, with the drawback that
it needs all `π i` to be infinite. -/
theorem DFinsupp'.infinite_of_exists_right {ι : Type*} {π : ι → Type*} (i : ι) [Infinite (π i)]
    {dπ : ∀ i, π i} : Infinite (Π₀' i, [π i, dπ i]) :=
  letI := Classical.decEq ι
  Infinite.of_injective (fun j => DFinsupp'.single dπ i j) DFinsupp'.single_injective

/-- See `DFinsupp'.infinite_of_exists_right` for the case that only one `π ι` is infinite. -/
instance DFinsupp'.infinite_of_right {ι : Type*} {π : ι → Type*} [∀ i, Infinite (π i)]
    {dπ : ∀ i, π i} [Nonempty ι] : Infinite (Π₀' i, [π i, dπ i]) :=
  DFinsupp'.infinite_of_exists_right (Classical.arbitrary ι)
