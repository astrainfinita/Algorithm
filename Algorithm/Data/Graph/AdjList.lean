/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Algorithm.Data.Classes.DefaultDict
public import Algorithm.Data.Classes.ToList
-- import Mathlib.Data.List.Nodup
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Finset.Union

/-!
# Graphs represented by adjacency lists

Adjacency list interfaces and graph reachability.
-/

@[expose] public section

structure AdjList
    (V : Type*) (Info : Type*)
    (EColl : Type*) [ToMultiset EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    (StarColl : Type*) [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅] where
  protected snd : Info → V
  protected star : StarColl

structure AdjList₂
    (V : Type*) (Info : Type*)
    (EColl : Type*) [ToMultiset EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    (StarColl : Type*) [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅] extends
    AdjList V Info EColl StarColl where
  fst : Info → V
  costar : StarColl
  fst_star' v : ∀ e ∈ star[v], fst e = v
  snd_costar' v : ∀ e ∈ costar[v], snd e = v
  count_star_fst_eq_count_costar_snd : [DecidableEq Info] → ∀ e,
    (toMultiset star[fst e]).count e = (toMultiset costar[snd e]).count e
  -- nodup_star' (v : V) : star'[v].Nodup
  -- nodup_costar' (v : V) : costar'[v].Nodup
  -- mem_star'_iff_mem_costar' e : e ∈ star'[fst' e] ↔ e ∈ costar'[snd' e]

class AdjListClass (G : Type*)
    (V : outParam <| Type*) (Info : outParam <| Type*)
    (EColl : outParam <| Type*) [ToMultiset EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    (StarColl : outParam <| Type*) [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅] where
  snd : G → Info → V
  star : G → StarColl

namespace AdjListClass

section ToMultiset
variable
  {V : Type*} {Info : Type*}
  {EColl : Type*} [ToMultiset EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]

instance : AdjListClass (AdjList V Info EColl StarColl) V Info EColl StarColl where
  snd := AdjList.snd
  star := AdjList.star

instance : AdjListClass (AdjList₂ V Info EColl StarColl) V Info EColl StarColl where
  snd g := g.snd
  star g := g.star

variable {G : Type*} [AdjListClass G V Info EColl StarColl] {g : G}

instance : GetElem G V EColl (fun _ _ ↦ True) where
  getElem g v _ := (star g)[v]

variable (g) in
@[ext]
structure E where ofStar ::
  fst : V
  info : Info
  mem_star : info ∈ g[fst]

attribute [simp] E.mem_star

@[simp]
protected lemma E.eta (e : E g) (he : e.info ∈ g[e.fst]) :
    ⟨e.fst, e.info, he⟩ = e :=
  rfl

instance E.instDecidableEq [DecidableEq V] [DecidableEq Info] : DecidableEq (E g) :=
  fun _ _ ↦ decidable_of_iff _ E.ext_iff.symm

protected def E.snd (e : E g) : V := snd g e.info

@[simp]
lemma E.info_snd (e : E g) :
    snd g e.info = e.snd :=
  rfl

lemma E.ofStar_fst (v : V) (x : Info) (hx : x ∈ g[v]) :
    (E.ofStar v x hx).fst = v :=
  rfl

lemma E.ofStar_snd (v : V) (x : Info) (hx : x ∈ g[v]) :
    (E.ofStar v x hx).snd = snd g x :=
  rfl

/-- The vertices of `g`, equipped with its quiver structure. -/
structure ToQuiver (g : G) [AdjListClass G V Info EColl StarColl] where
  /-- Wrap a vertex of `g` as a vertex of its quiver. -/
  mk (g) ::
  /-- The underlying vertex. -/
  val : V

open Lean.PrettyPrinter.Delaborator in
/-- Print `ToQuiver.mk g v` by name instead of as a structure literal. -/
@[app_delab ToQuiver.mk]
meta def ToQuiver.delabMk : Delab := delabApp

attribute [coe] ToQuiver.val

instance : CoeOut (ToQuiver g) V := ⟨ToQuiver.val⟩

section ToQuiver

@[simp]
lemma ToQuiver.mk_coe (v : ToQuiver g) :
    ToQuiver.mk g (v : V) = v :=
  rfl

instance : Quiver (ToQuiver g) where
  Hom v w := {e : E g // ToQuiver.mk g e.fst = v ∧ ToQuiver.mk g e.snd = w}

@[coe]
def ofHom {v w : ToQuiver g} (e : v ⟶ w) :
    E g :=
  e.1

instance {v w : ToQuiver g} : CoeOut (v ⟶ w) (E g) := ⟨ofHom⟩

@[simp, norm_cast]
theorem coe_inj {v w : ToQuiver g} {e₁ e₂ : v ⟶ w} :
    (e₁ : E g) = e₂ ↔ e₁ = e₂ :=
  Subtype.coe_inj

instance [DecidableEq V] [DecidableEq Info] {v w : ToQuiver g} :
    DecidableEq (v ⟶ w) := fun e₁ e₂ ↦ by
  convert decEq (ofHom e₁) (ofHom e₂)
  simp

lemma coe_mk {v w : ToQuiver g} (e : E g) (he) :
    (⟨e, he⟩ : v ⟶ w) = e :=
  rfl

@[simp]
lemma coe_fst {v w : ToQuiver g} (e : v ⟶ w) :
    (e : E g).fst = ↑v :=
  congr_arg ToQuiver.val e.2.1

@[simp]
lemma coe_snd {v w : ToQuiver g} (e : v ⟶ w) :
    (e : E g).snd = ↑w :=
  congr_arg ToQuiver.val e.2.2

@[simp]
lemma coe_info_mem_star {v w : ToQuiver g} (e : v ⟶ w) :
    (e : E g).info ∈ g[(v : V)] :=
  coe_fst e ▸ (e : E g).mem_star

def homOfStar {v : V} (x : Info) (hx : x ∈ g[v]) :
    ToQuiver.mk g v ⟶ ToQuiver.mk g (snd g x) :=
  ⟨.ofStar v x hx, rfl, rfl⟩

instance [DecidableEq V] [DecidableEq Info] {v w : ToQuiver g} : Fintype (v ⟶ w) where
  elems :=
    (((toMultiset g[(v : V)]).filter (fun e ↦ snd g e = (w : V))).pmap
      (fun x hx ↦ by
        simp only [Multiset.mem_filter, mem_toMultiset] at hx
        exact ⟨⟨v, x, hx.1⟩, ⟨rfl, by simp [E.ofStar_snd, hx.2]⟩⟩) (fun _ ↦ id)).toFinset
  complete := by
    rintro ⟨e, rfl, rfl⟩
    simp only [Multiset.mem_toFinset, Multiset.mem_pmap, Multiset.mem_filter,
      mem_toMultiset]
    refine ⟨e.info, ⟨e.mem_star, rfl⟩, rfl⟩

end ToQuiver

variable (g) in
def Adj (v w : V) : Prop := Nonempty (ToQuiver.mk g v ⟶ ToQuiver.mk g w)

variable (g) in
def Reachable (v w : V) : Prop := Nonempty (Quiver.Path (ToQuiver.mk g v) (ToQuiver.mk g w))

namespace Adj

lemma of_star {v : V} (e : Info) (he : e ∈ g[v]) :
    Adj g v (snd g e) :=
  ⟨homOfStar e he⟩

lemma to_reachable {v w : V} (h : Adj g v w) :
    Reachable g v w :=
  h.map (·.toPath)

end Adj

lemma adj_iff_star {v w : V} :
    Adj g v w ↔ ∃ x ∈ g[v], snd g x = w :=
  ⟨fun ⟨e⟩ ↦ ⟨(e : E g).info, coe_info_mem_star _, coe_snd e⟩, fun ⟨e, he, h⟩ ↦ h ▸ .of_star e he⟩

lemma Adj.star_ne_empty {v w : V} (h : Adj g v w) : g[v] ≠ ∅ := by
  obtain ⟨e, he, -⟩ := adj_iff_star.mp h
  intro hv
  exact not_mem_empty e (hv ▸ he)

variable (g) in
/-- The vertices incident to an edge of `g`, including both sources and targets. -/
noncomputable def support : Finset V := by
  classical
  exact (toDFinsupp' (star g)).support.biUnion fun v ↦
    (toMultiset g[v]).toFinset.biUnion fun e ↦ {v, snd g e}

@[simp]
lemma mem_support {v : V} :
    v ∈ support g ↔ ∃ w, Adj g v w ∨ Adj g w v := by
  classical
  simp only [support, Finset.mem_biUnion, DFinsupp'.mem_support_toFun,
    coe_toDFinsupp'_eq_getElem, Multiset.mem_toFinset, mem_toMultiset,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨u, _, e, he, rfl | rfl⟩
    · exact ⟨snd g e, .inl (.of_star e he)⟩
    · exact ⟨u, .inr (.of_star e he)⟩
  · rintro ⟨w, h | h⟩
    · obtain ⟨e, he, rfl⟩ := adj_iff_star.mp h
      exact ⟨v, h.star_ne_empty, e, he, .inl rfl⟩
    · obtain ⟨e, he, rfl⟩ := adj_iff_star.mp h
      exact ⟨w, h.star_ne_empty, e, he, .inr rfl⟩

lemma mem_support_iff_exists_mem_star {v : V} :
    v ∈ support g ↔ (∃ e, e ∈ g[v]) ∨ ∃ w : V, ∃ e ∈ g[w], snd g e = v := by
  simp only [mem_support, adj_iff_star]
  aesop

lemma Adj.fst_mem_support {v w : V} (h : Adj g v w) : v ∈ support g :=
  mem_support.mpr ⟨w, .inl h⟩

lemma Adj.snd_mem_support {v w : V} (h : Adj g v w) : w ∈ support g :=
  mem_support.mpr ⟨v, .inr h⟩

lemma E.fst_mem_support (e : E g) : e.fst ∈ support g :=
  (Adj.of_star e.info e.mem_star).fst_mem_support

lemma E.snd_mem_support (e : E g) : e.snd ∈ support g :=
  (Adj.of_star e.info e.mem_star).snd_mem_support

namespace Reachable

lemma rfl {v : V} : Reachable g v v := ⟨.nil⟩

variable (g) in
@[refl]
lemma refl (v : V) : Reachable g v v := ⟨.nil⟩

instance : Std.Refl (Reachable g) := ⟨refl g⟩

@[trans]
lemma trans {u v w : V} (huv : Reachable g u v) (hvw : Reachable g v w) :
    Reachable g u w :=
  Nonempty.map2 .comp huv hvw

instance : IsTrans V (Reachable g) := ⟨fun _ _ _ ↦ trans⟩

end Reachable

variable (g) in
lemma reachable_eq_reflTransGen : Reachable g = Relation.ReflTransGen (Adj g) := by
  ext v w
  constructor
  · intro ⟨h⟩
    change Relation.ReflTransGen (Adj g) v (ToQuiver.mk g w : V)
    generalize ToQuiver.mk g w = w' at *
    induction h with
    | nil => rfl
    | cons _ h ih => exact ih.tail ⟨h⟩
  · intro h
    induction h with
    | refl => rfl
    | tail _ h ih => exact ih.trans h.to_reachable

lemma Reachable.cases_head {v w : V} (hvw : Reachable g v w) :
    v = w ∨ ∃ x, Adj g v x ∧ Reachable g x w := by
  rw [reachable_eq_reflTransGen] at hvw ⊢
  exact hvw.cases_head

variable (g) in
def ReachableWithin (s : Set V) (v w : V) : Prop :=
  Relation.ReflTransGen (fun v w ↦ Adj g v w ∧ w ∈ s) v w

lemma ReachableWithin.mono {s t : Set V} {v w : V} (hst : s ⊆ t) (h : ReachableWithin g s v w) :
    ReachableWithin g t v w :=
  Relation.ReflTransGen.mono (fun _ _ ↦ And.imp_right (hst ·)) v w h

@[simp]
lemma reachableWithin_univ {v w : V} :
    ReachableWithin g Set.univ v w ↔ Reachable g v w := by
  simp only [ReachableWithin, Set.mem_univ, and_true, reachable_eq_reflTransGen]

lemma ReachableWithin.cases_head {s : Set V} {v w : V} (h : ReachableWithin g s v w) :
    v = w ∨ ∃ x, (Adj g v x ∧ x ∈ s) ∧ ReachableWithin g s x w :=
  Relation.ReflTransGen.cases_head h

lemma ReachableWithin.find {s : Set V} {v w : V}
    (h : ReachableWithin g s v w) (t : Set V) :
    v ∉ s \ t ∧ ReachableWithin g (s ∩ t) v w ∨ ∃ x ∈ s \ t, ReachableWithin g (s ∩ t) x w := by
  induction h with
  | refl => if hv : v ∈ s \ t then exact .inr <| ⟨v, hv, .refl⟩ else exact .inl <| ⟨hv, .refl⟩
  | tail _p e ih =>
    rename_i w
    if hw : w ∈ t then
      obtain (⟨hv, p⟩ | ⟨x, hx, p⟩) := ih
      · exact .inl <| ⟨hv, p.tail ⟨e.1, e.2, hw⟩⟩
      · exact .inr <| ⟨x, hx, p.tail ⟨e.1, e.2, hw⟩⟩
    else
      exact .inr ⟨w, ⟨e.2, hw⟩, .refl⟩

lemma ReachableWithin.inter_compl_singleton_self {s : Set V} {v w : V}
    (h : ReachableWithin g s v w) :
    ReachableWithin g (s ∩ {v}ᶜ) v w := by
  obtain (⟨-, h⟩ | ⟨x, hx, h⟩) := h.find {v}ᶜ
  · exact h
  · simp only [sdiff_compl, Set.inf_eq_inter, Set.mem_inter_iff,
      Set.mem_singleton_iff] at hx
    exact hx.2 ▸ h

lemma reachableWithin_iff_inter_compl_singleton_self {s : Set V} {v w : V} :
    ReachableWithin g s v w ↔ ReachableWithin g (s ∩ {v}ᶜ) v w :=
  ⟨.inter_compl_singleton_self, .mono Set.inter_subset_left⟩

variable (g) in
def succSet (s : Set V) : Set V := {w | ∃ v ∈ s, Adj g v w} -- ⋃ v ∈ s, {w | Adj g v w}

section lemmas

@[simp]
lemma mem_succSet_iff {s : Set V} {w : V} :
    w ∈ succSet g s ↔ ∃ v ∈ s, Adj g v w :=
  Iff.rfl

lemma mem_succSet_singleton_iff {v w : V} :
    w ∈ succSet g {v} ↔ Adj g v w := by
  simp

lemma succSet_subset_support (s : Set V) : succSet g s ⊆ (support g : Set V) :=
  fun _ ⟨_, _, h⟩ ↦ h.snd_mem_support

lemma succSet_singleton_eq_empty_of_notMem_support {v : V} (hv : v ∉ support g) :
    succSet g {v} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro w hw
  exact hv ((mem_succSet_singleton_iff.mp hw).fst_mem_support)

@[simp]
lemma succSet_empty :
    succSet g ∅ = ∅ := by
  simp [succSet]

@[simp]
lemma succSet_union {s t : Set V} :
    succSet g (s ∪ t) = succSet g s ∪ succSet g t := by
  simp [succSet, or_and_right, exists_or, Set.ofPred_or]

variable (g) in
def traversal (s t : Set V) : Set V :=
  s ∪ {w | ∃ v ∈ t, ReachableWithin g sᶜ v w}

@[simp]
lemma traversal_empty_right (s : Set V) : traversal g s ∅ = s := by
  simp [traversal]

lemma traversal_insert (s t : Set V) (v : V) (hv : v ∈ t) (t' : Set V)
    (hst : s ∩ t = ∅) (h : t' = (t ∪ succSet g {v}) \ insert v s) :
    traversal g (insert v s) t' = traversal g s t := by
  ext w
  subst h
  constructor
  · rintro ((rfl | h) | h)
    · exact .inr ⟨w, hv, .refl⟩
    · exact .inl h
    · simp only [Set.mem_sdiff, Set.mem_union, mem_succSet_iff, Set.mem_singleton_iff,
        exists_eq_left, Set.mem_insert_iff, not_or, Set.mem_ofPred_eq] at h
      obtain ⟨x, ⟨(hx | hx), hx'⟩, hxw⟩ := h
      · exact .inr ⟨x, hx, hxw.mono (Set.compl_subset_compl.mpr (Set.subset_insert _ _))⟩
      refine .inr ⟨v, hv, ?_⟩
      exact (hxw.mono (Set.compl_subset_compl.mpr (Set.subset_insert _ _))).head ⟨hx, hx'.2⟩
  · rintro (h | ⟨x, hx, h⟩)
    · exact .inl <| .inr h
    · obtain (⟨hxv, h⟩ | ⟨x, hxv, h⟩) := h.find {v}ᶜ
      · simp only [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and'] at hst
        specialize hst _ hx
        simp only [sdiff_compl, Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_compl_iff, hst,
          not_false_eq_true, Set.mem_singleton_iff, true_and] at hxv
        right
        simp only [← Set.union_singleton, Set.mem_sdiff, Set.mem_union, mem_succSet_iff,
          Set.mem_singleton_iff, exists_eq_left, not_or, Set.compl_union, Set.mem_ofPred_eq]
        exact ⟨x, ⟨.inl hx, hst, hxv⟩, h⟩
      · simp only [sdiff_compl, Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_compl_iff,
          Set.mem_singleton_iff] at hxv
        replace hxv := hxv.2; subst hxv
        obtain (rfl | ⟨y, hy, h⟩) := h.cases_head
        · exact Or.inl <| .inl rfl
        · simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff] at hy
          exact Or.inr ⟨y, ⟨.inr (by simp [hy]), by simp [hy]⟩, h.mono (fun _ h ↦ Or.rec h.2 h.1)⟩

end lemmas

end ToMultiset

section ToList
variable
  {V : Type*} {Info : Type*}
  {EColl : Type*} [ToList EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl] (g : G)

def succList (v : V) : List V := (toList g[v]).map (snd g)

@[simp]
lemma mem_succList_iff {v w : V} : w ∈ succList g v ↔ Adj g v w := by
  simp [succList, ← adj_iff_star]

lemma succList_subset_support (v : V) : {w | w ∈ succList g v} ⊆ (support g : Set V) :=
  fun _ hw ↦ ((mem_succList_iff g).mp hw).snd_mem_support

lemma succList_eq_nil_of_notMem_support {v : V} (hv : v ∉ support g) :
    succList g v = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro w hw
  exact hv (((mem_succList_iff g).mp hw).fst_mem_support)

@[simp]
lemma succSet_singleton (v : V) : succSet g {v} = {w | Adj g v w} := by
  ext; simp

lemma succList_eq_succSet (v : V) : {w | w ∈ succList g v} = succSet g {v} := by
  simp

-- @[simp]
-- lemma mem_succSet_iff {s : Set V} {w : V} :
--     w ∈ g.succSet s ↔ ∃ v ∈ s, ∃ e ∈ g.star[v], g.snd e = w := by
--   simp [succSet]

-- lemma mem_succSet_singleton_iff {v w : V} :
--     w ∈ g.succSet {v} ↔ ∃ e ∈ g.star[v], g.snd e = w := by
--   simp

-- end lemmas

end ToList

end AdjListClass
