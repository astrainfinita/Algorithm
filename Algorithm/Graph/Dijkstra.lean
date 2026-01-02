/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToList
import Algorithm.Data.Classes.IndexedMinHeap
import Algorithm.Data.Graph.AdjList
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Order

section -- should be in mathlb
variable {γ : Type*}

theorem upperBounds_total [LinearOrder γ] (s t : Set γ) :
    upperBounds s ⊆ upperBounds t ∨ upperBounds t ⊆ upperBounds s := by
  by_cases h : upperBounds s ⊆ upperBounds t
  · exact .inl h
  · right
    obtain ⟨b, hbs, hbt⟩ := Set.not_subset.mp h
    intro x hx
    have : b ≤ x := by
      by_contra! hbx
      exact hbt (upperBounds_mono_mem hbx.le hx)
    exact upperBounds_mono_mem this hbs

theorem lowerBounds_total [LinearOrder γ] (s t : Set γ) :
    lowerBounds s ⊆ lowerBounds t ∨ lowerBounds t ⊆ lowerBounds s :=
  upperBounds_total (γ := γᵒᵈ) s t

theorem isLUB_union_iff [LinearOrder γ] {a : γ} {s t : Set γ} :
    IsLUB (s ∪ t) a ↔ IsLUB s a ∧ a ∈ upperBounds t ∨ a ∈ upperBounds s ∧ IsLUB t a := by
  wlog hst : upperBounds s ⊆ upperBounds t
  · rw [Set.union_comm, or_comm, and_comm (b := IsLUB t a), and_comm (a := IsLUB s a)]
    exact this ((upperBounds_total s t).resolve_left hst)
  have : ∀ b, b ∈ upperBounds s ∧ b ∈ upperBounds t ↔ b ∈ upperBounds s := fun b ↦
    ⟨fun h ↦ h.1, fun h ↦ ⟨h, hst h⟩⟩
  simp only [isLUB_iff_le_iff, upperBounds_union, Set.mem_inter_iff, this]
  constructor
  · exact fun h ↦ .inl ⟨h, hst ((h a).mp le_rfl)⟩
  · rintro (h | h) b
    · exact h.1 b
    · exact ⟨fun hab ↦ upperBounds_mono_mem hab h.1, fun hbs ↦ (h.2 b).mpr (hst hbs)⟩

theorem isGLB_union_iff [LinearOrder γ] {a : γ} {s t : Set γ} :
    IsGLB (s ∪ t) a ↔ IsGLB s a ∧ a ∈ lowerBounds t ∨ a ∈ lowerBounds s ∧ IsGLB t a :=
  isLUB_union_iff (γ := γᵒᵈ)

end

namespace Multiset -- should be in mathlb
variable {α : Type*} [SemilatticeInf α] [OrderTop α]

theorem inf_congr {m₁ m₂ : Multiset α} (hm : ∀ a, a ∈ m₁ ↔ a ∈ m₂) : m₁.inf = m₂.inf := by
  haveI : DecidableEq α := by classical infer_instance
  rw [← m₁.inf_dedup, ← m₂.inf_dedup]
  congr 1
  ext a
  simp [count_dedup, hm]

end Multiset

namespace Finset -- should be in mathlb
variable {β α : Type*} [SemilatticeInf α] [OrderTop α] [DecidableEq β]

@[simp]
theorem inf_toFinset (m : Multiset β) (f : β → α) : m.toFinset.inf f = (m.map f).inf := by
  change (m.dedup.map f).inf = _
  haveI : DecidableEq α := by classical infer_instance
  rw [← (m.dedup.map f).inf_dedup, ← (m.map f).inf_dedup, Multiset.dedup_map_dedup_eq]

end Finset

namespace Quiver.Path
universe v u
variable {V : Type u} {C : Type*} [AddMonoid C] [Quiver.{v} V] {a b : V}

def cost (f : ∀ a b : V, (a ⟶ b) → C) {a b : V} : Path a b → C
  | nil => 0
  | cons p e => p.cost f + f _ _ e

@[simp]
theorem cost_nil (f : ∀ a b : V, (a ⟶ b) → C) {a : V} : (nil : Path a a).cost f = 0 :=
  rfl

@[simp]
theorem cost_cons (f : ∀ a b : V, (a ⟶ b) → C) (a b c : V) (p : Path a b) (e : b ⟶ c) :
    (p.cons e).cost f = p.cost f + f b c e :=
  rfl

@[simp]
theorem cost_comp (f : ∀ a b : V, (a ⟶ b) → C) {a b c : V} (p : Path a b) :
    ∀ (q : Path b c), (p.comp q).cost f = p.cost f + q.cost f
  | nil => by simp
  | cons _ _ => by simp [cost_comp, add_assoc]

end Quiver.Path

namespace AdjListClass
variable {V : Type*} {Info : Type*}
  {EColl : Type*} [ToList EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl]
  {CostType : Type*}

def IsLowerBoundOfEdges (g : G)
    [AddMonoid CostType] [Preorder CostType]
    (c : Info → CostType)
    (ss : Set V)
    (cs : ∀ s ∈ ss, CostType)
    (t : V) (d : WithTop CostType) : Prop :=
  d ∈ lowerBounds (⋃ s, ⋃ hs : s ∈ ss, Set.range
    fun e : g..toQuiver s ⟶ g..toQuiver t ↦ ↑(cs s hs + c (e : g..E).info))

lemma IsLowerBoundOfEdges.elim {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType}
    (h : g..IsLowerBoundOfEdges c ss cs t d)
    {s : V} (hs : s ∈ ss) (e : g..toQuiver s ⟶ g..toQuiver t) :
    d ≤ cs s hs + c (e : g..E).info := by
  apply h
  simpa using ⟨s, hs, e, rfl⟩

lemma isLowerBoundOfEdges_iff {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType} :
    g..IsLowerBoundOfEdges c ss cs t d ↔
      ∀ s, ∀ hs : s ∈ ss, ∀ e : g..toQuiver s ⟶ g..toQuiver t,
        d ≤ cs s hs + c (e : g..E).info := by
  constructor
  · intro h s hs e
    exact h.elim hs e
  · simp only [IsLowerBoundOfEdges, WithTop.coe_add, mem_lowerBounds, Set.mem_iUnion,
      Set.mem_range, forall_exists_index]
    rintro h - s hs e ⟨rfl⟩
    exact h s hs e

def IsLeastOfEdges (g : G)
    [AddMonoid CostType] [Preorder CostType]
    (c : Info → CostType)
    (ss : Set V)
    (cs : ∀ s ∈ ss, CostType)
    (t : V) (d : WithTop CostType) : Prop :=
  IsLeast (⋃ s, ⋃ hs : s ∈ ss, Set.range
    fun e : g..toQuiver s ⟶ g..toQuiver t ↦ ↑(cs s hs + c (e : g..E).info)) d

lemma isLeastOfEdges_iff {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType} :
    g..IsLeastOfEdges c ss cs t d ↔
      (∃ s, ∃ hs : s ∈ ss, ∃ e : g..toQuiver s ⟶ g..toQuiver t,
        cs s hs + c (e : g..E).info = d) ∧
      ∀ s, ∀ hs : s ∈ ss, ∀ e : g..toQuiver s ⟶ g..toQuiver t,
        d ≤ cs s hs + c (e : g..E).info :=
  Iff.and (by simp) isLowerBoundOfEdges_iff

lemma IsLeastOfEdges.isLowerBoundOfEdges {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType}
    (h : g..IsLeastOfEdges c ss cs t d) :
    g..IsLowerBoundOfEdges c ss cs t d :=
  h.2

lemma isLeastOfEdges_congr {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss ss' : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType}
    (hs : ss = ss') :
    g..IsLeastOfEdges c ss cs t d = g..IsLeastOfEdges c ss' (fun v hv ↦ cs v (hs ▸ hv)) t d := by
  congr!

lemma isLeastOfEdges_union {g : G}
    [AddMonoid CostType] [LinearOrder CostType]
    {c : Info → CostType}
    {ss ss' : Set V}
    {cs : ∀ s ∈ ss ∪ ss', CostType}
    {t : V} {d : WithTop CostType} :
    g..IsLeastOfEdges c (ss ∪ ss') cs t d ↔
      g..IsLeastOfEdges c ss (fun v hv ↦ cs v (Set.mem_union_left _ hv)) t d ∧
        g..IsLowerBoundOfEdges c ss' (fun v hv ↦ cs v (Set.mem_union_right _ hv)) t d ∨
      g..IsLowerBoundOfEdges c ss (fun v hv ↦ cs v (Set.mem_union_left _ hv)) t d ∧
        g..IsLeastOfEdges c ss' (fun v hv ↦ cs v (Set.mem_union_right _ hv)) t d := by
  unfold IsLeastOfEdges
  -- was `simp_rw [Set.mem_union]`
  conv_lhs => congr; congr; ext; rw [Set.iUnion_congr_Prop (Set.mem_union _ _ _) fun _ ↦ rfl]
  simp_rw [Set.iUnion_or, Set.iUnion_union_distrib, isLeast_union_iff]
  rfl

def IsLowerBoundOfDist (g : G)
    [AddMonoid CostType] [Preorder CostType]
    (c : Info → CostType)
    (ss : Set V)
    (cs : ∀ s ∈ ss, CostType)
    (t : V) (d : WithTop CostType) : Prop :=
  d ∈ lowerBounds (⋃ s, ⋃ hs : s ∈ ss, Set.range
    fun p : Quiver.Path (g..toQuiver s) (g..toQuiver t) ↦
      ↑(cs s hs + p.cost fun _ _ e ↦ c (e : g..E).info))

lemma IsLowerBoundOfDist.elim {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType}
    (h : g..IsLowerBoundOfDist c ss cs t d)
    {s : V} (hs : s ∈ ss) (p : Quiver.Path (g..toQuiver s) (g..toQuiver t)) :
    d ≤ cs s hs + p.cost fun _ _ e ↦ c (e : g..E).info := by
  apply h
  simpa using ⟨s, hs, p, rfl⟩

lemma isLowerBoundOfDist_iff {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType} :
    g..IsLowerBoundOfDist c ss cs t d ↔
      ∀ s, ∀ hs : s ∈ ss, ∀ p : Quiver.Path (g..toQuiver s) (g..toQuiver t),
        d ≤ cs s hs + p.cost fun _ _ e ↦ c (e : g..E).info := by
  constructor
  · intro h s hs e
    exact h.elim hs e
  · simp only [IsLowerBoundOfDist, WithTop.coe_add, mem_lowerBounds, Set.mem_iUnion, Set.mem_range,
      forall_exists_index]
    rintro h - s hs e ⟨rfl⟩
    exact h s hs e

def IsDist' (g : G)
    [AddMonoid CostType] [Preorder CostType]
    (c : Info → CostType)
    (ss : Set V)
    (cs : ∀ s ∈ ss, CostType)
    (t : V) (d : WithTop CostType) : Prop :=
  IsLeast (⋃ s, ⋃ hs : s ∈ ss, Set.range
    fun p : Quiver.Path (g..toQuiver s) (g..toQuiver t) ↦
      ↑(cs s hs + p.cost fun _ _ e ↦ c (e : g..E).info)) d

lemma isDist'_iff {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType} :
    g..IsDist' c ss cs t d ↔
      (∃ s, ∃ hs : s ∈ ss, ∃ p : Quiver.Path (g..toQuiver s) (g..toQuiver t),
        cs s hs + (p.cost fun _ _ e ↦ c (e : g..E).info) = d) ∧
      ∀ s, ∀ hs : s ∈ ss, ∀ p : Quiver.Path (g..toQuiver s) (g..toQuiver t),
        d ≤ cs s hs + p.cost fun _ _ e ↦ c (e : g..E).info :=
  Iff.and (by simp) isLowerBoundOfDist_iff

lemma IsDist'.isLowerBoundOfDist {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType}
    (h : g..IsDist' c ss cs t d) :
    g..IsLowerBoundOfDist c ss cs t d :=
  h.2

lemma isDist'_congr {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss ss' : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType}
    (hs : ss = ss') :
    g..IsDist' c ss cs t d = g..IsDist' c ss' (fun v hv ↦ cs v (hs ▸ hv)) t d := by
  congr!

lemma isDist'_union {g : G}
    [AddMonoid CostType] [LinearOrder CostType]
    {c : Info → CostType}
    {ss ss' : Set V}
    {cs : ∀ s ∈ ss ∪ ss', CostType}
    {t : V} {d : WithTop CostType} :
    g..IsDist' c (ss ∪ ss') cs t d ↔
      g..IsDist' c ss (fun v hv ↦ cs v (Set.mem_union_left _ hv)) t d ∧
        g..IsLowerBoundOfDist c ss' (fun v hv ↦ cs v (Set.mem_union_right _ hv)) t d ∨
      g..IsLowerBoundOfDist c ss (fun v hv ↦ cs v (Set.mem_union_left _ hv)) t d ∧
        g..IsDist' c ss' (fun v hv ↦ cs v (Set.mem_union_right _ hv)) t d := by
  unfold IsDist'
  simp_rw [Set.mem_union, Set.iUnion_or, Set.iUnion_union_distrib, isLeast_union_iff]
  rfl

def IsDist (g : G)
    [AddMonoid CostType] [Preorder CostType]
    (c : Info → CostType)
    (ss : Set V)
    (cs : ∀ s ∈ ss, CostType)
    (t : V) (d : WithTop CostType) : Prop :=
  IsGLB (⋃ s, ⋃ hs : s ∈ ss, Set.range
    fun p : Quiver.Path (g..toQuiver s) (g..toQuiver t) ↦
      ↑(cs s hs + p.cost fun _ _ e ↦ c (e : g..E).info)) d

lemma isDist_top_iff {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} :
    g..IsDist c ss cs t ⊤ ↔ ∀ s ∈ ss, ¬g..Reachable s t := by
  constructor
  · simp only [IsDist, WithTop.coe_add, isGLB_iff_le_iff, le_top, true_iff]
    intro h
    specialize h ⊤
    simp only [mem_lowerBounds, Set.mem_iUnion, Set.mem_range, WithTop.top_le_iff,
      forall_exists_index, forall_comm (α := WithTop CostType)] at h
    simp only [forall_eq', WithTop.add_eq_top, WithTop.coe_ne_top, or_self] at h
    rintro s hs ⟨p⟩
    exact h s hs p
  · intro h
    simp only [IsDist, WithTop.coe_add]
    convert_to IsGLB ∅ ⊤
    · simp only [Set.iUnion_eq_empty, Set.range_eq_empty_iff]
      intro s hs
      exact .mk fun p ↦ h s hs ⟨p⟩
    · simp only [isGLB_empty_iff, isTop_top]

lemma IsDist.isLowerBoundOfDist {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType}
    (h : g..IsDist c ss cs t d) :
    g..IsLowerBoundOfDist c ss cs t d :=
  h.1

lemma isDist_congr {g : G}
    [AddMonoid CostType] [Preorder CostType]
    {c : Info → CostType}
    {ss ss' : Set V}
    {cs : ∀ s ∈ ss, CostType}
    {t : V} {d : WithTop CostType}
    (hs : ss = ss') :
    g..IsDist c ss cs t d = g..IsDist c ss' (fun v hv ↦ cs v (hs ▸ hv)) t d := by
  congr!

lemma isDist_union {g : G}
    [AddMonoid CostType] [LinearOrder CostType]
    {c : Info → CostType}
    {ss ss' : Set V}
    {cs : ∀ s ∈ ss ∪ ss', CostType}
    {t : V} {d : WithTop CostType} :
    g..IsDist c (ss ∪ ss') cs t d ↔
      g..IsDist c ss (fun v hv ↦ cs v (Set.mem_union_left _ hv)) t d ∧
        g..IsLowerBoundOfDist c ss' (fun v hv ↦ cs v (Set.mem_union_right _ hv)) t d ∨
      g..IsLowerBoundOfDist c ss (fun v hv ↦ cs v (Set.mem_union_left _ hv)) t d ∧
        g..IsDist c ss' (fun v hv ↦ cs v (Set.mem_union_right _ hv)) t d := by
  unfold IsDist
  simp_rw [Set.mem_union, Set.iUnion_or, Set.iUnion_union_distrib, isGLB_union_iff]
  rfl

def dijkstraStep (g : G) (c : Info → CostType)
    [AddCommMonoid CostType] [LinearOrder CostType]
    {DistArray : Type*} [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (heap : DistHeap) (res : DistArray)
    (hMinIdx : heap[minIdx heap] ≠ ⊤) :
    DistHeap × DistArray :=
  let v := minIdx heap
  let d := heap[v].untop hMinIdx
  let r := res[v ↦ ↑d]
  (decreaseKeysD heap[v ↦ ⊤] <|
    (toList g[v]).filterMap fun e ↦
      if r[g..snd e] = ⊤ then some (g..snd e, ↑(d + c e)) else none,
    r)

structure dijkstraStep.Spec (g : G) (c : Info → CostType)
    [AddMonoid CostType] [LinearOrder CostType]
    {DistArray : Type*} [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (init : DistHeap) (heap : DistHeap) (res : DistArray) : Prop where
  h₁ : ∀ v : V, heap[v] = ⊤ ∨ res[v] = ⊤
  h₂ : ∀ v : V, res[v] = ⊤ → ∃ d, heap[v] = min init[v] d ∧
    ((d = ⊤ ∧ ∀ s : V, res[s] ≠ ⊤ → IsEmpty (g..toQuiver s ⟶ g..toQuiver v)) ∨
      g..IsLeastOfEdges c {s | res[s] ≠ ⊤} (fun s hs ↦ res[s].untop hs) v d)
  h₃ : ∀ v : V, res[v] ≠ ⊤ →
    g..IsDist' c {s | init[s] ≠ ⊤} (fun s hs ↦ init[s].untop hs) v res[v]
  h₄ : ∀ v : V, (∃ s, init[s] ≠ ⊤ ∧ g..Reachable s v) ↔
    v ∈ g..traversal {v | res[v] ≠ ⊤} {v | heap[v] ≠ ⊤}

lemma dijkstraStep_snd_getElem (g : G) (c : Info → CostType)
    [DecidableEq V] [AddCommMonoid CostType] [LinearOrder CostType]
    {DistArray : Type*} [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (heap : DistHeap) (res : DistArray) (hMinIdx : heap[minIdx heap] ≠ ⊤) (v : V) :
    (dijkstraStep g c heap res hMinIdx).2[v] =
      if v = minIdx heap then heap[minIdx heap] else res[v] := by
  simp [dijkstraStep, eq_comm]

lemma dijkstraStep_snd_getElem_eq_top (g : G) (c : Info → CostType)
    [AddCommMonoid CostType] [LinearOrder CostType]
    {DistArray : Type*} [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (heap : DistHeap) (res : DistArray) (hMinIdx : heap[minIdx heap] ≠ ⊤) (v : V) :
    (dijkstraStep g c heap res hMinIdx).2[v] = ⊤ ↔
      v ≠ minIdx heap ∧ res[v] = ⊤ := by
  let +nondep : DecidableEq V := by classical infer_instance
  simp [dijkstraStep_snd_getElem]
  split_ifs with h
  · simpa [h]
  · simp [h]

lemma dijkstraStep_snd_support (g : G) (c : Info → CostType)
    [AddCommMonoid CostType] [LinearOrder CostType]
    {DistArray : Type*} [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (heap : DistHeap) (res : DistArray) (hMinIdx : heap[minIdx heap] ≠ ⊤) :
    {v : V | (dijkstraStep g c heap res hMinIdx).2[v] ≠ ⊤} =
      insert (minIdx heap) {v : V | res[v] ≠ ⊤} := by
  ext
  simp only [ne_eq, dijkstraStep_snd_getElem_eq_top, not_and, Set.mem_setOf_eq, Set.mem_insert_iff]
  tauto

lemma dijkstraStep_fst_getElem' (g : G) (c : Info → CostType)
    [DecidableEq V] [AddCommMonoid CostType] [LinearOrder CostType]
    {DistArray : Type*} [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (heap : DistHeap) (res : DistArray) (hMinIdx : heap[minIdx heap] ≠ ⊤)
    (spec₁ : ∀ v : V, heap[v] = ⊤ ∨ res[v] = ⊤) (v : V) :
    (dijkstraStep g c heap res hMinIdx).1[v] =
      if v = minIdx heap ∨ res[v] ≠ ⊤ then ⊤ else min heap[v]
        ((toMultiset g[minIdx heap]).filterMap fun e ↦
          if g..snd e = v then some (heap[minIdx heap] + c e) else none).inf := by
  simp? [dijkstraStep, ← Multiset.filterMap_coe, getElem_setElem_eq_update, - getElem_setElem] says
    simp only [dijkstraStep, WithTop.coe_untop, getElem_setElem_eq_update, WithTop.coe_add,
      decreaseKeysD_getElem, toMultiset_list, ← Multiset.filterMap_coe, coe_toList, ne_eq]
  split_ifs with h
  · simp? [Function.update_apply] says
      simp only [Function.update_apply, inf_eq_top_iff, ite_eq_left_iff, Multiset.inf_eq_top,
        Multiset.mem_filterMap, mem_toMultiset, Option.ite_none_right_eq_some, Option.some.injEq,
        Prod.exists, Prod.mk.injEq, exists_eq_right_right, exists_eq_right, forall_exists_index,
        and_imp]
    use fun hv ↦ (spec₁ v).resolve_right (h.resolve_left hv)
    rintro - e - h' ⟨rfl⟩ ⟨rfl⟩
    split_ifs at h' with snde
    · simp [h']
    · exact absurd h' (h.resolve_left snde)
  · push_neg at h
    simp? [Function.update_apply, h, Multiset.filterMap_filterMap] says
      simp only [ne_eq, h, not_false_eq_true,
        Function.update_of_ne, Function.update_apply, Multiset.filterMap_filterMap]
    congr!
    split; · rename_i snde; simp [snde, Ne.symm h.1]
    split; · simp
    split
    · rename_i ressnde hv
      subst hv
      exact absurd h.2 ressnde
    · rfl

lemma dijkstraStep_fst_getElem (g : G) (c : Info → CostType)
    [DecidableEq V] [DecidableEq Info]
    [AddCommMonoid CostType] [LinearOrder CostType]
    {DistArray : Type*} [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (heap : DistHeap) (res : DistArray) (hMinIdx : heap[minIdx heap] ≠ ⊤)
    (spec₁ : ∀ v : V, heap[v] = ⊤ ∨ res[v] = ⊤) (v : V) :
    (dijkstraStep g c heap res hMinIdx).1[v] =
      if v = minIdx heap ∨ res[v] ≠ ⊤ then ⊤ else min heap[v] <|
        (Finset.univ (α := g..toQuiver (minIdx heap) ⟶ g..toQuiver v)).inf
          fun e ↦ heap[minIdx heap] + c (e : g..E).info := by
  rw [dijkstraStep_fst_getElem' (spec₁ := spec₁), ← Multiset.inf_dedup]
  congr!
  rw [Finset.inf_def]
  apply Multiset.inf_congr
  intro d
  simp? says
    simp only [Multiset.mem_dedup, Multiset.mem_filterMap, mem_toMultiset,
      Option.ite_none_right_eq_some, Option.some.injEq, Multiset.mem_map, Finset.mem_val,
      Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl, rfl, rfl⟩
    exact ⟨homOfStar x hx, rfl⟩
  · rintro ⟨⟨⟨v, x, hx⟩, ⟨fste, snde⟩⟩, rfl⟩
    simp only [EmbeddingLike.apply_eq_iff_eq] at fste snde; subst fste snde
    exact ⟨x, hx, rfl, rfl⟩

lemma dijkstraStep_fst_getElem_eq_top (g : G) (c : Info → CostType)
    [AddCommMonoid CostType] [LinearOrder CostType]
    {DistArray : Type*} [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (heap : DistHeap) (res : DistArray) (hMinIdx : heap[minIdx heap] ≠ ⊤)
    (spec₁ : ∀ v : V, heap[v] = ⊤ ∨ res[v] = ⊤) (v : V) :
    (dijkstraStep g c heap res hMinIdx).1[v] = ⊤ ↔
      (heap[v] = ⊤ ∧ v ∉ g..succSet {minIdx heap}) ∨ v = minIdx heap ∨ res[v] ≠ ⊤ := by
  let +nondep : DecidableEq V := by classical infer_instance
  let +nondep : DecidableEq Info := by classical infer_instance
  dsimp
  rw [dijkstraStep_fst_getElem (spec₁ := spec₁)]
  simp? [hMinIdx, - not_or] says
    simp only [ne_eq, ite_eq_left_iff, inf_eq_top_iff, Finset.inf_eq_top_iff, Finset.mem_univ,
      WithTop.add_eq_top, hMinIdx, WithTop.coe_ne_top, or_self, imp_false, not_true_eq_false,
      succSet_singleton, Set.mem_setOf_eq]
  rw [← or_iff_not_imp_right]
  congr!
  rw [iff_not_comm]
  push_neg
  rw [exists_true_iff_nonempty]
  rfl

lemma dijkstraStep_fst_support (g : G) (c : Info → CostType)
    [AddCommMonoid CostType] [LinearOrder CostType]
    {DistArray : Type*} [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (heap : DistHeap) (res : DistArray) (hMinIdx : heap[minIdx heap] ≠ ⊤)
    (spec₁ : ∀ v : V, heap[v] = ⊤ ∨ res[v] = ⊤) :
    {v : V | (dijkstraStep g c heap res hMinIdx).1[v] ≠ ⊤} =
      ({v : V | heap[v] ≠ ⊤} ∪ (g..succSet {minIdx heap})) \
        (insert (minIdx heap) {v : V | res[v] ≠ ⊤}) := by
  ext
  simp only [ne_eq, dijkstraStep_fst_getElem_eq_top (spec₁ := spec₁), mem_succSet_iff,
    Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq, Set.mem_diff, Set.mem_union,
    Set.mem_insert_iff]
  tauto

lemma dijkstraStep_spec (g : G) (c : Info → CostType)
    [AddCommMonoid CostType] [LinearOrder CostType] [CanonicallyOrderedAdd CostType]
    {DistArray : Type*} [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (init : DistHeap) (heap : DistHeap) (res : DistArray)
    (h : dijkstraStep.Spec g c init heap res) (hMinIdx : heap[minIdx heap] ≠ ⊤) :
    dijkstraStep.Spec g c init (dijkstraStep g c heap res hMinIdx).1
      (dijkstraStep g c heap res hMinIdx).2 := by
  let +nondep : DecidableEq V := by classical infer_instance
  let +nondep : DecidableEq Info := by classical infer_instance
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have rMinIdx : res[minIdx heap] = ⊤ := (h₁ _).resolve_left hMinIdx
  constructor
  · intro v
    rw [dijkstraStep_fst_getElem_eq_top (spec₁ := h₁), dijkstraStep_snd_getElem_eq_top]
    tauto
  · intro w resw
    rw [dijkstraStep_snd_getElem_eq_top] at resw
    specialize h₂ w resw.2
    obtain ⟨d, h₂⟩ := h₂
    use min d <| (Finset.univ (α := g..toQuiver (minIdx heap) ⟶ g..toQuiver w)).inf
      fun e ↦ heap[minIdx heap] + c (e : g..E).info
    constructor; · rw [dijkstraStep_fst_getElem (spec₁ := h₁), if_neg (by tauto), h₂.1, min_assoc]
    replace h₂ := h₂.2
    rw [isLeastOfEdges_congr (dijkstraStep_snd_support _ _ _ _ _)]
    rw [isLeastOfEdges_congr Set.union_singleton.symm]
    rw [isLeastOfEdges_union]
    simp only [ne_eq, Set.mem_setOf_eq, dijkstraStep_snd_getElem]
    by_cases wmin : w = minIdx heap
    · subst wmin
      simp at resw
    · simp only [ne_eq, wmin, not_false_eq_true, true_and, min_def, Finset.le_inf_iff,
        Finset.mem_univ, forall_true_left] at resw ⊢
      split_ifs with he
      · obtain (⟨rfl, h₂⟩ | h₂) := h₂
        · refine .inl ⟨rfl, fun x ↦ ?_⟩
          split_ifs with hx
          · simp only [top_le_iff, WithTop.add_eq_top, hMinIdx, WithTop.coe_ne_top, or_self] at he
            subst hx
            exact fun _ ↦ IsEmpty.mk he
          · exact h₂ x
        right; left
        constructor
        · convert h₂
          rw [ite_eq_right_iff]
          rintro ⟨rfl⟩
          rename_i rMinIdx'
          simp [rMinIdx] at rMinIdx'
        · simpa only [isLowerBoundOfEdges_iff, Set.mem_singleton_iff, WithTop.coe_untop, forall_eq,
            ↓reduceIte]
      · right; right
        simp only [not_forall, not_le] at he
        obtain ⟨e, he⟩ := he
        constructor
        · intro d hd
          simp only [Set.mem_setOf_eq, WithTop.coe_add, WithTop.coe_untop, Set.mem_iUnion,
            Set.mem_range, exists_prop] at hd
          obtain ⟨v, resv, evw, rfl⟩ := hd
          split_ifs with hv
          · subst hv
            rw [Finset.inf_le_iff]
            · simpa using ⟨evw, le_rfl⟩
            · rw [WithTop.lt_top_iff_ne_top]
              simp only [ne_eq, WithTop.add_eq_top, WithTop.coe_ne_top, or_false]
              intro h
              simp [h] at he
          · rw [Finset.inf_le_iff]
            · simp only [Finset.mem_univ, true_and]
              refine ⟨e, he.le.trans ?_⟩
              obtain (⟨rfl, h₂⟩ | h₂) := h₂; · exact (h₂ v resv).elim evw
              convert h₂.isLowerBoundOfEdges.elim resv evw
              simp only [WithTop.coe_untop]
            · rw [WithTop.lt_top_iff_ne_top]
              simpa only [ne_eq, WithTop.add_eq_top, WithTop.coe_ne_top, or_false]
        · simp only [isLeastOfEdges_iff, WithTop.coe_untop, Set.mem_singleton_iff, exists_prop,
            exists_eq_left, ↓reduceIte, forall_eq]
          obtain ⟨e', -, he'⟩ := Finset.univ.exists_mem_eq_inf ⟨e, Finset.mem_univ _⟩
            fun e ↦ heap[minIdx heap] + c (e : g..E).info
          exact ⟨⟨e', he'.symm⟩, fun e ↦ Finset.inf_le (Finset.mem_univ _)⟩
  · intro w resw
    rw [ne_eq, dijkstraStep_snd_getElem_eq_top] at resw
    rw [dijkstraStep_snd_getElem]
    by_cases wmin : w ≠ minIdx heap
    · simp only [ne_eq, wmin, not_false_eq_true, true_and] at resw ⊢
      exact h₃ w resw
    rw [not_not] at wmin; subst wmin
    simp only [ne_eq, Set.mem_setOf_eq, ↓reduceIte]
    simp only [ne_eq, Set.mem_setOf_eq, isLeastOfEdges_iff, WithTop.coe_untop, exists_prop,
      isDist'_iff] at h₂ h₃ ⊢
    constructor
    · obtain ⟨d, hd, h₂⟩ := h₂ (minIdx heap) rMinIdx
      rw [min_def] at hd
      split_ifs at hd; · exact ⟨minIdx heap, hd ▸ hMinIdx, .nil, by simp [hd]⟩
      subst hd
      obtain (h₂ | h₂) := h₂; · exact absurd h₂.1 hMinIdx
      obtain ⟨⟨v, hv, e, he⟩, -⟩ := h₂
      specialize h₃ v hv
      obtain ⟨⟨s, hs, p, hp⟩, -⟩ := h₃
      exact ⟨s, hs, p.cons e, by simp [← add_assoc, hp, he]⟩
    · intro s inits p
      by_cases hs : res[s] = ⊤
      · obtain ⟨d, hd, -⟩ := h₂ s hs
        apply le_add_right
        exact (getElem_minIdx_le heap s).trans <| hd.symm ▸ (min_le_left _ _)
      have : ∀ (t : g..Quiver), res[(t : V)] = ⊤ → ∀ p : Quiver.Path (g..toQuiver s) t,
        ∃ (v w : V), res[v] ≠ ⊤ ∧ res[w] = ⊤ ∧
          ∃ (psv : Quiver.Path (g..toQuiver s) (g..toQuiver v))
            (evw : g..toQuiver v ⟶ g..toQuiver w)
            (pwt : Quiver.Path (g..toQuiver w) t),
              p = (psv.cons evw).comp pwt := by
        intro t ht p
        induction p with
        | nil => exact absurd ht hs
        | cons p e ih =>
          rename_i v t
          by_cases hv : res[(v : V)] = ⊤
          · obtain ⟨v', w', hv', hw', psv', ev'w', pw'v, rfl⟩ := ih hv
            exact ⟨v', w', hv', hw', psv', ev'w', pw'v.cons e, by simp⟩
          exact ⟨v, t, hv, ht, p, e, .nil, rfl⟩
      obtain ⟨v, w, hv, hw, psv, evw, pwt, rfl⟩ := this _ rMinIdx p
      simp only [Quiver.Path.cost_comp, Quiver.Path.cost_cons, WithTop.coe_add, ← add_assoc]
      obtain ⟨d, hd, (⟨rfl, h₂⟩ | ⟨-, h₂⟩)⟩ := h₂ w hw; · exact (h₂ v hv).elim evw
      replace h₃ := (h₃ v hv).2 s inits psv
      calc
        heap[minIdx heap]
          ≤ heap[w]                     := getElem_minIdx_le heap w
        _ ≤ d                           := by order only [hd]
        _ ≤ res[v] + c (evw : E g).info := h₂ v hv evw
        _ ≤ _                           := by grw [h₃]; exact self_le_add_right _ _
  · intro v
    -- simp? [dijkstraStep_snd_getElem_eq_top, dijkstraStep_fst_getElem_eq_top (spec₁ := h₁), h₄]
    simp only [ne_eq, h₄, dijkstraStep_snd_support,
      dijkstraStep_fst_getElem_eq_top (spec₁ := h₁), mem_succSet_iff, Set.mem_singleton_iff,
      exists_eq_left]
    rw [traversal_insert]
    · simpa
    · ext s
      simpa using (h₁ _).resolve_right
    · ext s
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_union, mem_succSet_iff,
        Set.mem_singleton_iff, exists_eq_left, Set.mem_insert_iff]
      tauto

def dijkstra (g : G) (c : Info → CostType)
    [Fintype V] [AddCommMonoid CostType] [LinearOrder CostType] [CanonicallyOrderedAdd CostType]
    (DistArray : Type*) [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (init : DistHeap) :
    DistArray :=
  (go init default spec_init).val.2
where
  go (heap : DistHeap) (res : DistArray) (spec : dijkstraStep.Spec g c init heap res) :
      { hr : DistHeap × DistArray //
        dijkstraStep.Spec g c init hr.1 hr.2 ∧ hr.1[minIdx hr.1] = ⊤ } :=
    if hh : heap[minIdx heap] = ⊤ then
      ⟨(heap, res), spec, hh⟩
    else
      let hr := g..dijkstraStep c heap res hh
      have : Fintype.card {v : V | hr.2[v] = ⊤} < Fintype.card {v : V | res[v] = ⊤} := by
        let +nondep : DecidableEq V := by classical infer_instance
        simp only [dijkstraStep_snd_getElem_eq_top, ne_eq, Set.coe_setOf, hr]
        exact Fintype.card_lt_of_injective_of_notMem (fun ⟨v, hv⟩ ↦ ⟨v, hv.2⟩)
          (by intro ⟨v, hv⟩ ⟨w, hw⟩; simp)
          (b := ⟨minIdx heap, (spec.1 _).resolve_left hh⟩) (by simp)
      go hr.1 hr.2 (g..dijkstraStep_spec c init heap res spec hh)
termination_by Fintype.card {v : V | res[v] = ⊤}
  spec_init : dijkstraStep.Spec g c init init default := by
    constructor
    · simp
    · simp only [DefaultDict.getElem_default, ne_eq,
        not_true_eq_false, IsEmpty.forall_iff, implies_true, and_true, Set.mem_setOf_eq,
        forall_true_left]
      intro h
      use ⊤
      simp [isLeastOfEdges_iff]
    · simp
    · simp [traversal]

lemma dijkstra_spec (g : G) (c : Info → CostType)
    [Fintype V] [AddCommMonoid CostType] [LinearOrder CostType] [CanonicallyOrderedAdd CostType]
    (DistArray : Type*) [Inhabited DistArray] [DefaultDict DistArray V (WithTop CostType) fun _ ↦ ⊤]
    {DistHeap : Type*} [Inhabited DistHeap] [IndexedMinHeap DistHeap V (WithTop CostType)]
    (init : DistHeap) (v : V) :
    g..IsDist c {s | init[s] ≠ ⊤} (fun s hs ↦ init[s].untop hs) v
      (g..dijkstra c DistArray init)[v] := by
  rw [dijkstra]
  have spec := (dijkstra.go g c DistArray init init default
    (dijkstra.spec_init g c DistArray init)).prop
  if hv : (g..dijkstra c DistArray init)[v] = ⊤ then
    unfold dijkstra at hv
    rw [hv, isDist_top_iff]
    dsimp
    have := (spec.1.4 v).not
    push_neg at this
    rw [this]
    have : v ∉ g..traversal {v | (dijkstra g c DistArray init)[v] ≠ ⊤} ∅ := by simpa [traversal]
    convert this
    ext v
    simp only [ne_eq, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    rw [eq_top_iff]
    apply le_trans _ (getElem_minIdx_le _ _)
    rw [spec.2]
  else
    exact IsLeast.isGLB <| spec.1.3 v hv

end AdjListClass
