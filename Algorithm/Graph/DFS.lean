/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Graph.AdjList
import Algorithm.Data.Graph.IsDFSForest
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace AdjListClass
variable {V : Type*} {Info : Type*}
  {EColl : Type*} [ToList EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl]

-- 也许在以后可以改成存迭代器
-- 如何形式化各种使用 dfs 的算法？如 Tarjan's SCC

def dfsForest' (g : G)
    [Fintype V] {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    Forest V × { b : BoolArray // [DecidableEq V] →
      (toDFinsupp' visited).support ⊆ (toDFinsupp' b).support } :=
  match vs with
  | [] => (.nil, ⟨visited, @fun _ ↦ subset_rfl⟩)
  | v :: vs =>
    if visited[v] then
      g..dfsForest' vs visited
    else
      have h [DecidableEq V] : (toDFinsupp' visited).support ⊆
          (toDFinsupp' visited[v ↦ true]).support := by
        simp [DFinsupp'.support_update_ne]
      let (fc, ⟨vis₁, h₁⟩) := g..dfsForest' (g..succList v) visited[v ↦ true]
      let (fs, ⟨vis₂, h₂⟩) := g..dfsForest' vs vis₁
      (Forest.node v fc fs, ⟨vis₂, @fun _ ↦ (h.trans h₁).trans h₂⟩)
termination_by by classical exact ((toDFinsupp' visited).supportᶜ.card, vs)
decreasing_by
  all_goals
    letI : DecidableEq V := by classical infer_instance
    simp_wf
  · simp [Prod.lex_iff]
  · apply Prod.Lex.left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    refine ⟨v, by simp [*], ?_⟩
    rw [Finset.subset_iff]
    simp [*, Function.update]
  · have : (toDFinsupp' vis₁).supportᶜ.card ≤ (toDFinsupp' visited).supportᶜ.card := by
      apply Finset.card_le_card
      simpa using h.trans h₁
    simpa [Prod.lex_iff, ← le_iff_lt_or_eq] using this

lemma roots_dfsForest'_fst_subset (g : G)
    [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    (g..dfsForest' vs visited).1.roots ⊆ {v | v ∈ vs} := by
  match vs with
  | [] => unfold dfsForest'; exact Set.empty_subset _
  | v :: vs =>
    unfold dfsForest'; split
    · intro _ h
      simpa using .inr (g..roots_dfsForest'_fst_subset vs visited h)
    dsimp
    rintro _ (rfl | h)
    · simp
    · simp only [List.mem_cons]
      exact .inr <| g..roots_dfsForest'_fst_subset vs _ h

lemma subset_support_toDFinsupp'_dfsForest'_snd (g : G)
    [DecidableEq V] [Fintype V] {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    {v | v ∈ vs} ⊆ (toDFinsupp' (g..dfsForest' vs visited).2.val).support := by
  match vs with
  | [] => simp
  | v :: vs =>
    simp only [List.mem_cons]
    unfold dfsForest'; split
    · rintro _ (rfl | h)
      · apply (g..dfsForest' vs visited).2.prop
        simpa
      · exact g..subset_support_toDFinsupp'_dfsForest'_snd vs visited h
    · dsimp
      rintro _ (rfl | h)
      · apply (g..dfsForest' _ _).2.prop
        apply (g..dfsForest' _ _).2.prop
        simp
      · exact g..subset_support_toDFinsupp'_dfsForest'_snd vs _ h

lemma isDFSForest_dfsForest' (g : G)
    [DecidableEq V] [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    g..IsDFSForest
      (toDFinsupp' visited).support
      (toDFinsupp' (g..dfsForest' vs visited).2.val).support
      (g..dfsForest' vs visited).1 := by
  induction vs, visited using dfsForest'.induct g (BoolArray := BoolArray) with
  | case1 => unfold dfsForest'; constructor
  | case2 _ _ _ h ih => rwa [dfsForest', if_pos h]
  | case3 visited v vs hv _ _ _ _ hc _ _ _ hs ih₁ ih₂ =>
    rw [dfsForest', if_neg hv]
    let rc := g..dfsForest' (g..succList v) visited[v ↦ true]
    dsimp; apply IsDFSForest.node (toDFinsupp' rc.2.val).support
    · simp [hv]
    · convert ih₁
      simp [DFinsupp'.support_update_ne]
    · exact g..succList_eq_succSet _ ▸ (g..roots_dfsForest'_fst_subset _ _)
    · exact g..succList_eq_succSet _ ▸ (g..subset_support_toDFinsupp'_dfsForest'_snd _ _)
    · rw [hs] at ih₂
      dsimp [rc]; rwa [hc, hs]

def dfsForest (g : G)
    [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    Forest V × BoolArray :=
  (g..dfsForest' vs visited).map id Subtype.val

lemma dfsForest_spec' (g : G)
    [Fintype V] (BoolArray : Type*) [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false] (vs : List V) :
    let (f, vis) := (g..dfsForest vs (default : BoolArray))
    ([DecidableEq V] → f.support = (toDFinsupp' vis).support) ∧
      ∀ v, v ∈ f.support ↔ ∃ r ∈ vs, g..Reachable r v := by
  letI : DecidableEq V := by classical infer_instance
  have := g..isDFSForest_dfsForest' vs (default : BoolArray)
  simp only [toDFinsupp'_default, DFinsupp'.support_default, Finset.coe_empty] at this
  dsimp
  refine ⟨@fun _ ↦ by convert this.spec.1,
    fun v ↦ ⟨fun hv ↦ ?_, fun ⟨r, hr, hrv⟩ ↦ this.complete v r ?_ hrv⟩⟩
  · obtain ⟨r, hr, hrv⟩ := this.sound v hv
    exact ⟨r, g..roots_dfsForest'_fst_subset vs _ hr, hrv⟩
  · exact this.spec.1 ▸ g..subset_support_toDFinsupp'_dfsForest'_snd vs default hr

lemma dfsForest_spec (g : G)
    [Fintype V] (BoolArray : Type*) [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false] (vs : List V) :
    let (f, vis) := (g..dfsForest vs (default : BoolArray))
    f.support = {v : V | vis[v]} ∧ ∀ v : V, vis[v] ↔ ∃ r ∈ vs, g..Reachable r v := by
  letI : Unique (DecidableEq V) := uniqueOfSubsingleton <| by classical infer_instance
  have H := g..dfsForest_spec' BoolArray vs
  dsimp at H ⊢
  simp only [Unique.forall_iff] at H
  convert H
  · ext; simp
  · simp [H.1]

def dfs' (g : G) [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    { b : BoolArray // ([DecidableEq V] →
      (toDFinsupp' visited).support ⊆ (toDFinsupp' b).support) ∧
      b = (dfsForest' g vs visited).2.val } :=
  match vs with
  | [] => ⟨visited, @fun _ ↦ subset_rfl, by unfold dfsForest'; rfl⟩
  | v :: vs =>
    if hv : visited[v] then
      let ⟨vis, h, hvis⟩ := g..dfs' vs visited
      ⟨vis, @fun _ ↦ h, by rw [hvis, dfsForest']; simp [hv]⟩
    else
      have h [DecidableEq V] : (toDFinsupp' visited).support ⊆
          (toDFinsupp' visited[v ↦ true]).support := by
        simp [DFinsupp'.support_update_ne]
      let ⟨vis₁, h₁, hvis₁⟩ := g..dfs' (g..succList v) visited[v ↦ true]
      let ⟨vis₂, h₂, hvis₂⟩ := g..dfs' vs vis₁
      ⟨vis₂, @fun _ ↦ (h.trans h₁).trans h₂, by rw [hvis₂, hvis₁, dfsForest']; simp [hv]⟩
termination_by by classical exact ((toDFinsupp' visited).supportᶜ.card, vs)
decreasing_by
  all_goals
    letI : DecidableEq V := by classical infer_instance
    simp_wf
  · simp [Prod.lex_iff]
  · apply Prod.Lex.left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    refine ⟨v, by simp [*], ?_⟩
    rw [Finset.subset_iff]
    simp [*, Function.update]
  · have : (toDFinsupp' vis₁).supportᶜ.card ≤ (toDFinsupp' visited).supportᶜ.card := by
      apply Finset.card_le_card
      simpa using h.trans h₁
    simpa [Prod.lex_iff, ← le_iff_lt_or_eq] using this

def dfs (g : G) [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    BoolArray :=
  (g..dfs' vs visited).val

@[simp]
lemma dfsForest_snd (g : G)
    [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    (g..dfsForest vs visited).snd = g..dfs vs visited :=
  (g..dfs' vs visited).prop.2.symm

lemma dfs_spec (g : G)
    [Fintype V] (BoolArray : Type*) [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false] (vs : List V) :
    ∀ v : V, (g..dfs vs (default : BoolArray))[v] ↔ ∃ r ∈ vs, g..Reachable r v :=
  g..dfsForest_snd vs (default : BoolArray) ▸ (g..dfsForest_spec BoolArray vs).2

def dfsForestTR (g : G)
    [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List (Forest V × List V)) (visited : BoolArray) :
    Forest V × BoolArray :=
  match vs with
  | [] => (.nil, default)
  | [(f, [])] => (f, visited)
  | (_, []) :: (_, []) :: _ => (.nil, default)
  | (f, []) :: (fs, v :: vs) :: vss => g..dfsForestTR ((Forest.node v f fs, vs) :: vss) visited
  | (f, v :: vs) :: vss =>
    if visited[v] then
      g..dfsForestTR ((f, vs) :: vss) visited
    else
      g..dfsForestTR ((.nil, g..succList v) :: (f, vs) :: vss) visited[v ↦ true]
termination_by by classical exact
  ((toDFinsupp' visited).supportᶜ.card, (vs.map (·.snd.length + 1)).sum)
decreasing_by
  all_goals
    letI : DecidableEq V := by classical infer_instance
    simp_wf
  · simp [Prod.lex_iff]
    omega
  · simp [Prod.lex_iff]
  · apply Prod.Lex.left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    refine ⟨v, by simp [*], ?_⟩
    rw [Finset.subset_iff]
    simp [*, Function.update]

def dfs'TR (g : G) [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List (List V)) (visited : BoolArray) :
    BoolArray :=
  match vs with
  | [] => visited
  | [] :: vss => g..dfs'TR vss visited
  | (v :: vs) :: vss =>
    if visited[v] then
      g..dfs'TR (vs :: vss) visited
    else
      g..dfs'TR (g..succList v :: (vs :: vss)) visited[v ↦ true]
termination_by by classical exact
  ((toDFinsupp' visited).supportᶜ.card, (vs.map (·.length + 1)).sum)
decreasing_by
  all_goals
    letI : DecidableEq V := by classical infer_instance
    simp_wf
  · simp [Prod.lex_iff]
  · simp [Prod.lex_iff]
  · apply Prod.Lex.left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    refine ⟨v, by simp [*], ?_⟩
    rw [Finset.subset_iff]
    simp [*, Function.update]

def dfsTR (g : G) [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    BoolArray :=
  match vs with
  | [] => visited
  | v :: vs =>
    if visited[v] then
      g..dfsTR vs visited
    else
      g..dfsTR (g..succList v ++ vs) visited[v ↦ true]
termination_by by classical exact ((toDFinsupp' visited).supportᶜ.card, vs.length)
decreasing_by
  all_goals
    letI : DecidableEq V := by classical infer_instance
    simp_wf
  · simp [Prod.lex_iff]
  · apply Prod.Lex.left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    refine ⟨v, by simp [*], ?_⟩
    rw [Finset.subset_iff]
    simp [*, Function.update]

lemma dfsTR_spec' (g : G)
    [Fintype V] [DecidableEq V]
    {BoolArray : Type*} [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    g..traversal (toDFinsupp' visited).support {v | v ∈ vs ∧ v ∉ (toDFinsupp' visited).support} =
      g..traversal (toDFinsupp' (g..dfsTR vs visited)).support ∅ := by
  induction vs, visited using dfsTR.induct g (BoolArray := BoolArray) with
  | case1 => simp [dfsTR]
  | case2 _ v _ hv ih =>
    simp only [dfsTR, List.mem_cons]
    rw [if_pos hv, ← ih]
    ext w
    simp [traversal]
    aesop
  | case3 _ _ _ hv ih =>
    rw [dfsTR, if_neg hv, ← ih]
    simp? says
      simp only [List.mem_cons, DFinsupp'.mem_support_toFun, coe_toDFinsupp'_eq_getElem,
        ne_eq, Bool.not_eq_false, Bool.not_eq_true, toDFinsupp'_setElem, List.mem_append,
        mem_succList_iff, DFinsupp'.coe_update]
    rw [DFinsupp'.support_update_ne _ _ (by simp), Finset.coe_insert, traversal_insert]
    · simp [hv]
    · ext; simp (config := { contextual := true })
    · unfold Function.update
      aesop

lemma dfsTR_spec (g : G)
    [Fintype V] (BoolArray : Type*) [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) :
    g..traversal ∅ {v | v ∈ vs} = {v : V | (g..dfsTR vs (default : BoolArray))[v]} := by
  letI : DecidableEq V := by classical infer_instance
  trans g..traversal {v | (g..dfsTR vs (default : BoolArray))[v]} ∅
  · convert g..dfsTR_spec' vs (default : BoolArray) <;> aesop
  · simp

end AdjListClass
