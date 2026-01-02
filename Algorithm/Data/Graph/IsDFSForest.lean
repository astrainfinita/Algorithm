/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToList
import Algorithm.Data.Forest
import Algorithm.Data.Graph.AdjList
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace AdjListClass
variable
  {V : Type*} {Info : Type*}
  {EColl : Type*} [ToList EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl] {g : G}

variable (g) in
inductive IsDFSForest : Set V → Set V → Forest V → Prop
  | nil (i : Set V) : IsDFSForest i i .nil
  | node {i o : Set V} {v : V} {c : Forest V} {s : Forest V}
    (m : Set V)
    (hv : v ∉ i)
    (hc : IsDFSForest (insert v i) m c)
    (roots_subset_succ : c.roots ⊆ g..succSet {v})
    (succ_marked : g..succSet {v} ⊆ m)
    (hs : IsDFSForest m o s) : IsDFSForest i o (.node v c s)

namespace IsDFSForest
variable {i m o : Set V} {f f₁ f₂ : Forest V}

lemma append (hf₁ : g..IsDFSForest i m f₁) (hf₂ : g..IsDFSForest m o f₂) :
    g..IsDFSForest i o (f₁ ++ f₂) := by
  induction hf₁ with
  | nil _ => exact hf₂
  | node m₁ hv hc roots_subset_succ succ_marked _ _ ihs =>
    exact node m₁ hv hc roots_subset_succ succ_marked (ihs hf₂)

lemma union (hf : g..IsDFSForest i o f) : i ∪ f.support = o := by
  induction hf with
  | nil i => exact Set.union_empty _
  | node _ _ _ _ _ _ ihc ihs =>
    dsimp
    rw [Set.union_insert, ← Set.insert_union,
      ← Set.union_assoc, ihc, ihs]

lemma subset (hf : g..IsDFSForest i o f) : i ⊆ o :=
  hf.union ▸ Set.subset_union_left

lemma support_subset (hf : g..IsDFSForest i o f) : f.support ⊆ o :=
  hf.union ▸ Set.subset_union_right

lemma inter (hf : g..IsDFSForest i o f) : i ∩ f.support = ∅ := by
  induction hf with
  | nil _ => exact Set.inter_empty _
  | node _ hv hc _ _ _ ihc ihs =>
    dsimp
    rw [Set.inter_insert_of_notMem hv, Set.inter_union_distrib_left,
      Set.union_empty_iff]
    rw [← Set.subset_empty_iff] at ihc ihs ⊢
    rw [← Set.subset_empty_iff]
    exact ⟨(Set.inter_subset_inter_left _ (Set.subset_insert _ _)).trans ihc,
      (Set.inter_subset_inter_left _ ((Set.subset_insert _ _).trans hc.subset)).trans ihs⟩

lemma sound (hf : g..IsDFSForest i o f) :
    ∀ v ∈ f.support, ∃ r ∈ f.roots, g..Reachable r v := by
  induction hf with
  | nil _ => nofun
  | node _ hv hc roots_subset_succ _ _ ihc ihs =>
    dsimp
    rintro w (rfl | hw | hw)
    · exact ⟨w, .inl rfl, .refl _ _⟩
    · obtain ⟨r, hr, hrw⟩ := ihc w hw
      exact ⟨_, .inl rfl,
        (mem_succSet_singleton_iff.mp (roots_subset_succ hr)).to_reachable.trans hrw⟩
    · obtain ⟨r, hr, hrw⟩ := ihs w hw
      exact ⟨r, .inr hr, hrw⟩

lemma succSet_support_subset (hf : g..IsDFSForest i o f) :
    g..succSet f.support ⊆ o := by
  induction hf with
  | nil _ => nofun
  | node _ hv hc _ succ_marked hs ihc ihs =>
    dsimp
    intro w hw
    simp only [Set.mem_union, mem_succSet_iff, Set.mem_insert_iff, exists_eq_or_imp] at hw
    obtain (hw | ⟨r, (hr | hr), hrw⟩) := hw
    · apply succ_marked.trans hs.subset
      simpa using hw
    · apply ihc.trans hs.subset
      simpa using ⟨r, hr, hrw⟩
    · apply ihs
      simpa using ⟨r, hr, hrw⟩

lemma succSet_subset' (hf : g..IsDFSForest i o f) (h : g..succSet i ⊆ o) :
    g..succSet o ⊆ o := by
  conv_lhs => rw [← hf.union]
  simpa using ⟨h, hf.succSet_support_subset⟩

-- lemma succSet_subset (hf : g.IsDFSForest i o f) (h : g.succSet i ⊆ i) :
--     g.succSet o ⊆ o :=
--   hf.succSet_subset' (h.trans hf.subset)

lemma complete' (hf : g..IsDFSForest i o f) (h : g..succSet i ⊆ o) :
    ∀ v, ∀ r ∈ f.support, g..Reachable r v → v ∈ o := by
  intro v r hr h
  rw [g..reachable_eq_reflTransGen] at h
  induction h with
  | refl => exact hf.support_subset hr
  | tail _ e ih => exact hf.succSet_subset' h ⟨_, ih, e⟩

lemma complete (hf : g..IsDFSForest ∅ o f) :
    ∀ v, ∀ r ∈ f.support, g..Reachable r v → v ∈ f.support := by
  convert hf.complete' (by simp)
  simp [← hf.union]

lemma spec (hf : g..IsDFSForest ∅ o f) :
    f.support = o ∧ ∀ v, v ∈ f.support ↔ ∃ r ∈ f.roots, g..Reachable r v :=
  ⟨by simp [← hf.union],
    fun v ↦ ⟨hf.sound v, fun ⟨r, hr, hrv⟩ ↦ hf.complete v r (f.roots_subset_support hr) hrv⟩⟩

end IsDFSForest

end AdjListClass
