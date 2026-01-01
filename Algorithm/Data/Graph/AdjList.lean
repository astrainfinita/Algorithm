/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.DefaultDict
import Algorithm.Data.Classes.ToList
-- import Mathlib.Data.List.Nodup
import Mathlib.Combinatorics.Quiver.Path

structure AdjList
    (V : Type*) (Info : Type*)
    (EColl : Type*) [ToMultiset EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    (StarColl : Type*) [DefaultDict.ReadOnly StarColl V EColl ∅] where
  protected snd : Info → V
  protected star : StarColl

structure AdjList₂
    (V : Type*) (Info : Type*)
    (EColl : Type*) [ToMultiset EColl Info] [EmptyCollection EColl]
    [LawfulEmptyCollection EColl Info]
    (StarColl : Type*) [DefaultDict.ReadOnly StarColl V EColl ∅] extends
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
    (StarColl : outParam <| Type*) [DefaultDict.ReadOnly StarColl V EColl ∅] where
  snd : G → Info → V
  star : G → StarColl

namespace AdjListClass

-- 一个邪恶的语法，用来假装我还能使用点记号
scoped syntax:max term noWs ".." noWs ident : term
macro_rules
  |`($g..$name) => do
    match name.raw with
    | .ident _ _ name _ =>
      `($(Lean.mkIdent (Lean.Name.mkStr1 "AdjListClass" ++ name)) $g)
    | _ => `($g..$name)

section ToMultiset
variable
  {V : Type*} {Info : Type*}
  {EColl : Type*} [ToMultiset EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl ∅]

instance : AdjListClass (AdjList V Info EColl StarColl) V Info EColl StarColl where
  snd := AdjList.snd
  star := AdjList.star

instance : AdjListClass (AdjList₂ V Info EColl StarColl) V Info EColl StarColl where
  snd g := g.snd
  star g := g.star

variable {G : Type*} [AdjListClass G V Info EColl StarColl] {g : G}

instance : GetElem G V EColl (fun _ _ ↦ True) where
  getElem g v _ := g..star[v]

variable (g) in
@[ext, pp_using_anonymous_constructor]
structure E where ofStar ::
  fst : V
  info : Info
  mem_star : info ∈ g[fst]

attribute [simp] E.mem_star

@[simp]
protected lemma E.eta (e : g..E) (he : e.info ∈ g[e.fst]) :
    ⟨e.fst, e.info, he⟩ = e :=
  rfl

instance E.instDecidableEq [DecidableEq V] [DecidableEq Info] : DecidableEq g..E :=
  fun _ _ ↦ decidable_of_iff _ E.ext_iff.symm

protected def E.snd (e : g..E) : V := g..snd e.info

@[simp]
lemma E.info_snd (e : g..E) :
    g..snd e.info = e.snd :=
  rfl

lemma E.ofStar_fst (v : V) (x : Info) (hx : x ∈ g[v]) :
    (E.ofStar v x hx).fst = v :=
  rfl

lemma E.ofStar_snd (v : V) (x : Info) (hx : x ∈ g[v]) :
    (E.ofStar v x hx).snd = g..snd x :=
  rfl

protected structure Quiver (g : G) [AdjListClass G V Info EColl StarColl] where
  _intro ::
  val : V

attribute [coe] Quiver.val

instance : CoeOut g..Quiver V := ⟨Quiver.val⟩

section Quiver

variable (g) in
def toQuiver : V ≃ g..Quiver := ⟨Quiver._intro, (↑), fun _ ↦ rfl, fun _ ↦ rfl⟩

@[simp]
lemma toQuiver_coe (v : g..Quiver) :
    g..toQuiver ↑v = v :=
  rfl

variable (g) in
@[simp]
lemma coe_toQuiver (v : V) :
    ↑(g..toQuiver v) = v :=
  rfl

instance : Quiver g..Quiver where
  Hom v w := {e : g..E // g..toQuiver e.fst = v ∧ g..toQuiver e.snd = w}

@[coe]
def ofHom {v w : g..Quiver} (e : v ⟶ w) :
    g..E :=
  e.1

instance {v w : g..Quiver} : CoeOut (v ⟶ w) (E g) := ⟨ofHom⟩

@[simp, norm_cast]
theorem coe_inj {v w : g..Quiver} {e₁ e₂ : v ⟶ w} :
    (e₁ : g..E) = e₂ ↔ e₁ = e₂ :=
  Subtype.coe_inj

instance [DecidableEq V] [DecidableEq Info] {v w : g..Quiver} :
    DecidableEq (v ⟶ w) := fun e₁ e₂ ↦ by
  convert decEq (ofHom e₁) (ofHom e₂)
  simp

lemma coe_mk {v w : g..Quiver} (e : g..E) (he) :
    (⟨e, he⟩ : v ⟶ w) = e :=
  rfl

@[simp]
lemma coe_fst {v w : g..Quiver} (e : v ⟶ w) :
    (e : g..E).fst = ↑v :=
  congr_arg Quiver.val e.2.1

@[simp]
lemma coe_snd {v w : g..Quiver} (e : v ⟶ w) :
    (e : g..E).snd = ↑w :=
  congr_arg Quiver.val e.2.2

@[simp]
lemma coe_info_mem_star {v w : g..Quiver} (e : v ⟶ w) :
    (e : g..E).info ∈ g[(v : V)] :=
  coe_fst e ▸ (e : E g).mem_star

def homOfStar {v : V} (x : Info) (hx : x ∈ g[v]) :
    g..toQuiver v ⟶ g..toQuiver (g..snd x) :=
  ⟨.ofStar v x hx, ⟨congr_arg g..toQuiver (E.ofStar_fst v x hx), rfl⟩⟩

instance [DecidableEq V] [DecidableEq Info] {v w : g..Quiver} : Fintype (v ⟶ w) where
  elems :=
    (((toMultiset g[(v : V)]).filter (fun e ↦ g..snd e = (w : V))).pmap
      (fun x hx ↦ by
        simp only [Multiset.mem_filter, mem_toMultiset] at hx
        exact ⟨⟨v, x, hx.1⟩, ⟨rfl, by simp [E.ofStar_snd, hx.2]⟩⟩) (fun _ ↦ id)).toFinset
  complete := by
    rintro ⟨e, rfl, rfl⟩
    simp only [coe_toQuiver, Multiset.mem_toFinset, Multiset.mem_pmap, Multiset.mem_filter,
      mem_toMultiset]
    refine ⟨e.info, ⟨e.mem_star, rfl⟩, rfl⟩

end Quiver

variable (g) in
def Adj (v w : V) : Prop := Nonempty (g..toQuiver v ⟶ g..toQuiver w)

variable (g) in
def Reachable (v w : V) : Prop := Nonempty (Quiver.Path (g..toQuiver v) (g..toQuiver w))

namespace Adj

lemma of_star {v : V} (e : Info) (he : e ∈ g[v]) :
    g..Adj v (g..snd e) :=
  ⟨homOfStar e he⟩

lemma to_reachable {v w : V} (h : g..Adj v w) :
    g..Reachable v w :=
  h.map (·.toPath)

end Adj

lemma adj_iff_star {v w : V} :
    g..Adj v w ↔ ∃ x ∈ g[v], g..snd x = w :=
  ⟨fun ⟨e⟩ ↦ ⟨(e : g..E).info, coe_info_mem_star _, coe_snd e⟩, fun ⟨e, he, h⟩ ↦ h ▸ .of_star e he⟩

namespace Reachable

lemma rfl {v : V} : g..Reachable v v := ⟨.nil⟩

variable (g) in
@[refl]
lemma refl (v : V) : g..Reachable v v := ⟨.nil⟩

instance : IsRefl V g..Reachable := ⟨refl g⟩

@[trans]
lemma trans {u v w : V} (huv : g..Reachable u v) (hvw : g..Reachable v w) :
    g..Reachable u w :=
  Nonempty.map2 .comp huv hvw

instance : IsTrans V g..Reachable := ⟨fun _ _ _ ↦ trans⟩

end Reachable

variable (g) in
lemma reachable_eq_reflTransGen : g..Reachable = Relation.ReflTransGen g..Adj := by
  ext v w
  constructor
  · intro ⟨h⟩
    rw [← g..coe_toQuiver w]
    generalize g..toQuiver w = w' at *
    induction h with
    | nil => rfl
    | cons _ h ih => exact ih.tail ⟨h⟩
  · intro h
    induction h with
    | refl => rfl
    | tail _ h ih => exact ih.trans h.to_reachable

lemma Reachable.cases_head {v w : V} (hvw : g..Reachable v w) :
    v = w ∨ ∃ x, g..Adj v x ∧ g..Reachable x w := by
  rw [reachable_eq_reflTransGen] at hvw ⊢
  exact hvw.cases_head

variable (g) in
def ReachableWithin (s : Set V) (v w : V) : Prop :=
  Relation.ReflTransGen (fun v w ↦ g..Adj v w ∧ w ∈ s) v w

lemma ReachableWithin.mono {s t : Set V} {v w : V} (hst : s ⊆ t) (h : g..ReachableWithin s v w) :
    g..ReachableWithin t v w :=
  Relation.ReflTransGen.mono (fun _ _ ↦ And.imp_right (hst ·)) h

@[simp]
lemma reachableWithin_univ {v w : V} :
    g..ReachableWithin Set.univ v w ↔ g..Reachable v w := by
  rw [reachable_eq_reflTransGen]
  exact ⟨Relation.ReflTransGen.mono (by simp), Relation.ReflTransGen.mono (by simp)⟩

lemma ReachableWithin.cases_head {s : Set V} {v w : V} (h : g..ReachableWithin s v w) :
    v = w ∨ ∃ x, (g..Adj v x ∧ x ∈ s) ∧ g..ReachableWithin s x w :=
  Relation.ReflTransGen.cases_head h

lemma ReachableWithin.find {s : Set V} {v w : V}
    (h : g..ReachableWithin s v w) (t : Set V) :
    v ∉ s \ t ∧ g..ReachableWithin (s ∩ t) v w ∨ ∃ x ∈ s \ t, g..ReachableWithin (s ∩ t) x w := by
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
    (h : g..ReachableWithin s v w) :
    g..ReachableWithin (s ∩ {v}ᶜ) v w := by
  obtain (⟨-, h⟩ | ⟨x, hx, h⟩) := h.find {v}ᶜ
  · exact h
  · simp only [sdiff_compl, Set.inf_eq_inter, Set.mem_inter_iff,
      Set.mem_singleton_iff] at hx
    exact hx.2 ▸ h

lemma reachableWithin_iff_inter_compl_singleton_self {s : Set V} {v w : V} :
    g..ReachableWithin s v w ↔ g..ReachableWithin (s ∩ {v}ᶜ) v w :=
  ⟨.inter_compl_singleton_self, .mono Set.inter_subset_left⟩

variable (g) in
def succSet (s : Set V) : Set V := {w | ∃ v ∈ s, g..Adj v w} -- ⋃ v ∈ s, {w | g..Adj v w}

section lemmas

@[simp]
lemma mem_succSet_iff {s : Set V} {w : V} :
    w ∈ g..succSet s ↔ ∃ v ∈ s, g..Adj v w :=
  Iff.rfl

lemma mem_succSet_singleton_iff {v w : V} :
    w ∈ g..succSet {v} ↔ g..Adj v w := by
  simp

@[simp]
lemma succSet_empty :
    g..succSet ∅ = ∅ := by
  simp [succSet]

@[simp]
lemma succSet_union {s t : Set V} :
    g..succSet (s ∪ t) = g..succSet s ∪ g..succSet t := by
  simp [succSet, or_and_right, exists_or, Set.setOf_or]

variable (g) in
def traversal (s t : Set V) : Set V :=
  s ∪ {w | ∃ v ∈ t, g..ReachableWithin sᶜ v w}

@[simp]
lemma traversal_empty_right (s : Set V) : g..traversal s ∅ = s := by
  simp [traversal]

lemma traversal_insert (s t : Set V) (v : V) (hv : v ∈ t) (t' : Set V)
    (hst : s ∩ t = ∅) (h : t' = (t ∪ g..succSet {v}) \ insert v s) :
    g..traversal (insert v s) t' = g..traversal s t := by
  ext w
  subst h
  constructor
  · rintro ((rfl | h) | h)
    · exact .inr ⟨w, hv, .refl⟩
    · exact .inl h
    · simp only [Set.mem_diff, Set.mem_union, mem_succSet_iff, Set.mem_singleton_iff,
        exists_eq_left, Set.mem_insert_iff, not_or, Set.mem_setOf_eq] at h
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
        simp only [← Set.union_singleton, Set.mem_diff, Set.mem_union, mem_succSet_iff,
          Set.mem_singleton_iff, exists_eq_left, not_or, Set.compl_union, Set.mem_setOf_eq]
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
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl] (g : G)

def succList (v : V) : List V := (toList g[v]).map g..snd

@[simp]
lemma mem_succList_iff {v w : V} : w ∈ g..succList v ↔ g..Adj v w := by
  simp [succList, ← adj_iff_star]

@[simp]
lemma succSet_singleton (v : V) : g..succSet {v} = {w | g..Adj v w} := by
  ext; simp

lemma succList_eq_succSet (v : V) : {w | w ∈ g..succList v} = g..succSet {v} := by
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
