/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Algorithm.Data.Graph.IsDFSForest

/-!
# Depth-first search

Depth-first search and its correctness proofs.
-/

@[expose] public section

namespace AdjListClass
variable {V : Type*} {Info : Type*}
  {EColl : Type*} [ToList EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl]

attribute [local instance] WellFoundedLT.toWellFoundedRelation

/-- Vertices incident to an edge that have not yet been visited. -/
noncomputable def unvisitedSupport (g : G) {BoolArray : Type*}
    [DefaultDict.ReadOnly BoolArray V Bool fun _ ↦ false]
    (visited : BoolArray) : Finset V :=
  {v ∈ support g | ¬visited[v]}

lemma unvisitedSupport_set_true [DecidableEq V] (g : G) {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (visited : BoolArray) (v : V) :
    unvisitedSupport g visited[v ↦ true] = (unvisitedSupport g visited).erase v := by
  ext w
  by_cases hw : w = v
  · subst hw
    simp [unvisitedSupport]
  · simp [unvisitedSupport, hw, Ne.symm hw]

lemma unvisitedSupport_set_true_ssubset (g : G) {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (visited : BoolArray) (v : V) (hvs : v ∈ support g) (hv : ¬visited[v]) :
    unvisitedSupport g visited[v ↦ true] ⊂ unvisitedSupport g visited := by
  classical
  rw [unvisitedSupport_set_true]
  exact Finset.erase_ssubset (Finset.mem_filter.mpr ⟨hvs, hv⟩)

lemma unvisitedSupport_set_true_of_notMem (g : G) {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (visited : BoolArray) {v : V} (hv : v ∉ support g) :
    unvisitedSupport g visited[v ↦ true] = unvisitedSupport g visited := by
  classical
  rw [unvisitedSupport_set_true]
  exact Finset.erase_eq_of_notMem fun h ↦ hv (Finset.mem_filter.mp h).1

lemma unvisitedSupport_antitone (g : G)
    {BoolArray : Type*} [DefaultDict.ReadOnly BoolArray V Bool fun _ ↦ false]
    {visited visited' : BoolArray}
    (h : ∀ v : V, visited[v] → visited'[v]) :
    unvisitedSupport g visited' ⊆ unvisitedSupport g visited :=
  fun v hv ↦ Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hv).1, mt (h v) (Finset.mem_filter.mp hv).2⟩

@[simp]
private lemma visited_set_true {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (visited : BoolArray) (v : V) :
    {w : V | visited[v ↦ true][w]} = insert v {w : V | visited[w]} := by
  classical
  ext w
  by_cases h : v = w
  · subst w
    simp
  · simp [h, Ne.symm h]

/-- Visiting a new vertex decreases the first component, unless it has no successors;
in that case it suffices to decrease the worklist measure. -/
private lemma dfs_visit_decreases (g : G) {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (visited : BoolArray) (v : V) (hv : ¬visited[v])
    {α : Type*} {r : α → α → Prop} {m n : α} (h : succList g v = [] → r m n) :
    Prod.Lex (· < ·) r
      (unvisitedSupport g visited[v ↦ true], m)
      (unvisitedSupport g visited, n) := by
  by_cases hvs : v ∈ support g
  · exact Prod.Lex.left _ _ (unvisitedSupport_set_true_ssubset g visited v hvs hv)
  · rw [unvisitedSupport_set_true_of_notMem g visited hvs]
    exact Prod.Lex.right _ (h (succList_eq_nil_of_notMem_support g hvs))

-- 也许在以后可以改成存迭代器
-- 如何形式化各种使用 dfs 的算法？如 Tarjan's SCC

def dfsForest' (g : G)
    {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    Forest V × { b : BoolArray // {v : V | visited[v]} ⊆ {v : V | b[v]} } :=
  match vs with
  | [] => (.nil, ⟨visited, subset_rfl⟩)
  | v :: vs =>
    if visited[v] then
      dfsForest' g vs visited
    else
      have h : {w : V | visited[w]} ⊆ {w : V | visited[v ↦ true][w]} := by simp
      let (fc, ⟨vis₁, h₁⟩) := dfsForest' g (succList g v) visited[v ↦ true]
      let (fs, ⟨vis₂, h₂⟩) := dfsForest' g vs vis₁
      (Forest.node v fc fs, ⟨vis₂, (h.trans h₁).trans h₂⟩)
termination_by (unvisitedSupport g visited, vs)
decreasing_by
  · simp [Prod.lex_iff]
  · apply dfs_visit_decreases g visited v ‹_›
    intro hnil
    cases vs <;> simp +arith [hnil]
  · simpa [Prod.lex_iff] using
      lt_or_eq_of_le (α := Finset V) (unvisitedSupport_antitone g (h.trans h₁))

lemma roots_dfsForest'_fst_subset (g : G)
    {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    (dfsForest' g vs visited).1.roots ⊆ {v | v ∈ vs} := by
  match vs with
  | [] => unfold dfsForest'; exact Set.empty_subset _
  | v :: vs =>
    unfold dfsForest'; split
    · intro _ h
      simpa using .inr (roots_dfsForest'_fst_subset g vs visited h)
    dsimp
    rintro _ (rfl | h)
    · simp
    · simp only [List.mem_cons]
      exact .inr <| roots_dfsForest'_fst_subset g vs _ h

lemma subset_visited_dfsForest'_snd (g : G)
    {BoolArray : Type*}
    [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    {v | v ∈ vs} ⊆ {v : V | (dfsForest' g vs visited).2.val[v]} := by
  match vs with
  | [] => simp
  | v :: vs =>
    simp only [List.mem_cons]
    unfold dfsForest'; split
    · rintro _ (rfl | h)
      · apply (dfsForest' g vs visited).2.prop
        simpa
      · exact subset_visited_dfsForest'_snd g vs visited h
    · dsimp
      rintro _ (rfl | h)
      · apply (dfsForest' g _ _).2.prop
        apply (dfsForest' g _ _).2.prop
        simp
      · exact subset_visited_dfsForest'_snd g vs _ h

lemma isDFSForest_dfsForest' (g : G)
    {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    IsDFSForest g
      {v : V | visited[v]}
      {v : V | (dfsForest' g vs visited).2.val[v]}
      (dfsForest' g vs visited).1 := by
  induction vs, visited using dfsForest'.induct g (BoolArray := BoolArray) with
  | case1 => unfold dfsForest'; constructor
  | case2 _ _ _ h ih => rwa [dfsForest', ite_eq_left h]
  | case3 visited v vs hv _ _ _ _ hc _ _ _ _ ih₁ ih₂ =>
    rw [dfsForest', ite_eq_right hv]
    let rc := dfsForest' g (succList g v) visited[v ↦ true]
    dsimp; apply IsDFSForest.node {v : V | rc.2.val[v]}
    · simp [hv]
    · simpa using ih₁
    · exact succList_eq_succSet g _ ▸ (roots_dfsForest'_fst_subset g _ _)
    · exact succList_eq_succSet g _ ▸ (subset_visited_dfsForest'_snd g _ _)
    · have hrc := congrArg (fun r ↦ r.2.val) hc
      cases hrc
      exact ih₂

def dfsForest (g : G)
    {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    Forest V × BoolArray :=
  (dfsForest' g vs visited).map id Subtype.val

lemma dfsForest_spec' (g : G)
    (BoolArray : Type*) [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false] (vs : List V) :
    let (f, vis) := (dfsForest g vs (default : BoolArray))
    (f.support = {v : V | vis[v]}) ∧
      ∀ v, v ∈ f.support ↔ ∃ r ∈ vs, Reachable g r v := by
  have := isDFSForest_dfsForest' g vs (default : BoolArray)
  simp only [DefaultDict.getElem_default, Bool.false_eq_true, Set.ofPred_false] at this
  dsimp
  refine ⟨this.spec.1,
    fun v ↦ ⟨fun hv ↦ ?_, fun ⟨r, hr, hrv⟩ ↦ this.complete v r ?_ hrv⟩⟩
  · obtain ⟨r, hr, hrv⟩ := this.sound v hv
    exact ⟨r, roots_dfsForest'_fst_subset g vs _ hr, hrv⟩
  · exact this.spec.1 ▸ subset_visited_dfsForest'_snd g vs default hr

lemma dfsForest_spec (g : G)
    (BoolArray : Type*) [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false] (vs : List V) :
    let (f, vis) := (dfsForest g vs (default : BoolArray))
    f.support = {v : V | vis[v]} ∧ ∀ v : V, vis[v] ↔ ∃ r ∈ vs, Reachable g r v := by
  have h := dfsForest_spec' g BoolArray vs
  exact ⟨h.1, fun v ↦ by simpa only [h.1, Set.mem_ofPred_eq] using h.2 v⟩

def dfs' (g : G) {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    { b : BoolArray // ({v : V | visited[v]} ⊆ {v : V | b[v]}) ∧
      b = (dfsForest' g vs visited).2.val } :=
  match vs with
  | [] => ⟨visited, subset_rfl, by unfold dfsForest'; rfl⟩
  | v :: vs =>
    if hv : visited[v] then
      let ⟨vis, h, hvis⟩ := dfs' g vs visited
      ⟨vis, h, by rw [hvis, dfsForest']; simp [hv]⟩
    else
      have h : {w : V | visited[w]} ⊆ {w : V | visited[v ↦ true][w]} := by simp
      let ⟨vis₁, h₁, hvis₁⟩ := dfs' g (succList g v) visited[v ↦ true]
      let ⟨vis₂, h₂, hvis₂⟩ := dfs' g vs vis₁
      ⟨vis₂, (h.trans h₁).trans h₂, by rw [hvis₂, hvis₁, dfsForest']; simp [hv]⟩
termination_by (unvisitedSupport g visited, vs)
decreasing_by
  · simp [Prod.lex_iff]
  · apply dfs_visit_decreases g visited v ‹_›
    intro hnil
    cases vs <;> simp +arith [hnil]
  · simpa [Prod.lex_iff] using
      lt_or_eq_of_le (α := Finset V) (unvisitedSupport_antitone g (h.trans h₁))

def dfs (g : G) {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    BoolArray :=
  (dfs' g vs visited).val

@[simp]
lemma dfsForest_snd (g : G)
    {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    (dfsForest g vs visited).snd = dfs g vs visited :=
  (dfs' g vs visited).prop.2.symm

lemma dfs_spec (g : G)
    (BoolArray : Type*) [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false] (vs : List V) :
    ∀ v : V, (dfs g vs (default : BoolArray))[v] ↔ ∃ r ∈ vs, Reachable g r v :=
  dfsForest_snd g vs (default : BoolArray) ▸ (dfsForest_spec g BoolArray vs).2

def dfsForestTR (g : G)
    {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List (Forest V × List V)) (visited : BoolArray) :
    Forest V × BoolArray :=
  match vs with
  | [] => (.nil, default)
  | [(f, [])] => (f, visited)
  | (_, []) :: (_, []) :: _ => (.nil, default)
  | (f, []) :: (fs, v :: vs) :: vss => dfsForestTR g ((Forest.node v f fs, vs) :: vss) visited
  | (f, v :: vs) :: vss =>
    if visited[v] then
      dfsForestTR g ((f, vs) :: vss) visited
    else
      dfsForestTR g ((.nil, succList g v) :: (f, vs) :: vss) visited[v ↦ true]
termination_by (unvisitedSupport g visited, vs.flatMap Prod.snd)
decreasing_by
  · simp [Prod.lex_iff]
  · simp [Prod.lex_iff]
  · apply dfs_visit_decreases g visited v ‹_›
    intro hnil
    simp [hnil]

def dfs'TR (g : G) {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List (List V)) (visited : BoolArray) :
    BoolArray :=
  match vs with
  | [] => visited
  | [] :: vss => dfs'TR g vss visited
  | (v :: vs) :: vss =>
    if visited[v] then
      dfs'TR g (vs :: vss) visited
    else
      dfs'TR g (succList g v :: (vs :: vss)) visited[v ↦ true]
termination_by (unvisitedSupport g visited, vs.flatten, vs)
decreasing_by
  · simp [Prod.lex_iff]
  · simp [Prod.lex_iff]
  · apply dfs_visit_decreases g visited v ‹_›
    intro hnil
    simp [hnil, Prod.lex_iff]

def dfsTR (g : G) {BoolArray : Type*} [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    BoolArray :=
  match vs with
  | [] => visited
  | v :: vs =>
    if visited[v] then
      dfsTR g vs visited
    else
      dfsTR g (succList g v ++ vs) visited[v ↦ true]
termination_by (unvisitedSupport g visited, vs)
decreasing_by
  · simp [Prod.lex_iff]
  · apply dfs_visit_decreases g visited v ‹_›
    intro hnil
    simp [hnil]

lemma dfsTR_spec' (g : G)
    {BoolArray : Type*} [Inhabited BoolArray] [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) (visited : BoolArray) :
    traversal g {v : V | visited[v]} {v | v ∈ vs ∧ ¬visited[v]} =
      traversal g {v : V | (dfsTR g vs visited)[v]} ∅ := by
  induction vs, visited using dfsTR.induct g (BoolArray := BoolArray) with
  | case1 => simp [dfsTR]
  | case2 _ v _ hv ih =>
    simp only [dfsTR, ite_eq_left hv, List.mem_cons]
    rw [← ih]
    ext w
    simp [traversal]
    aesop
  | case3 _ _ _ hv ih =>
    rw [dfsTR, ite_eq_right hv, ← ih]
    rw [visited_set_true, traversal_insert]
    · simp [hv]
    · ext; simp (config := { contextual := true })
    · classical
      ext
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_union, List.mem_append,
        List.mem_cons, mem_succList_iff, mem_succSet_singleton_iff, Set.mem_insert_iff]
      aesop

lemma dfsTR_spec (g : G)
    (BoolArray : Type*) [Inhabited BoolArray]
    [DefaultDict BoolArray V Bool fun _ ↦ false]
    (vs : List V) :
    traversal g ∅ {v | v ∈ vs} = {v : V | (dfsTR g vs (default : BoolArray))[v]} := by
  simpa using dfsTR_spec' g vs (default : BoolArray)

end AdjListClass
