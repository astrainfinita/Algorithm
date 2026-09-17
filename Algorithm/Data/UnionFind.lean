/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Algorithm.Data.Classes.GetElem
public import Mathlib.Data.Set.Card

/-!
# Union-find

Union-find with path compression, union by size, and a quotient interface.
-/

@[expose] public section

namespace UnionFindImpl

structure UnionFind (ι : Type*) [DecidableEq ι]
    (P : Type*) [GetSetElemAllValid P ι ι]
    (S : Type*) [GetSetElemAllValid S ι ℕ] where
  parent : P
  size : S
  wf : WellFounded fun i j : ι ↦ i ≠ j ∧ i = parent[j]

namespace UnionFind

variable {ι : Type*} [DecidableEq ι]
    {P : Type*} [GetSetElemAllValid P ι ι]
    {S : Type*} [GetSetElemAllValid S ι ℕ]

def rootCore (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k]) (i : ι) : ι :=
  let p := parent[i]
  if p = i then
    i
  else
    rootCore parent wf p
termination_by wf.wrap i

lemma rootCore_of_eq (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k]) (i : ι)
    (hi : parent[i] = i) : rootCore parent wf i = i := by
  rw [rootCore, if_pos hi]

@[simp]
lemma rootCore_parent (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k]) (i : ι) :
    rootCore parent wf parent[i] = rootCore parent wf i := by
  conv_rhs => rw [rootCore]
  split_ifs with h
  · rw [rootCore, h, if_pos h]
  · rfl

@[simp]
lemma parent_rootCore (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k]) (i : ι) :
    parent[rootCore parent wf i] = rootCore parent wf i := by
  rw [rootCore]
  split_ifs with h
  · exact h
  · exact parent_rootCore parent wf parent[i]
termination_by wf.wrap i

lemma transGen_rootCore (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k])
    (i : ι) (hi : parent[i] ≠ i) :
    Relation.TransGen (fun i j ↦ i ≠ j ∧ i = parent[j]) (rootCore parent wf i) i := by
  rw [rootCore, if_neg hi, rootCore]
  split_ifs with h
  · exact .single ⟨hi, rfl⟩
  · rw [rootCore_parent]
    exact .tail (b := parent[i]) (transGen_rootCore parent wf parent[i] h) ⟨hi, rfl⟩
termination_by wf.wrap i

@[simp]
lemma rootCore_eq_self (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k])
    (i : ι) : rootCore parent wf i = i ↔ parent[i] = i := by
  constructor
  · contrapose
    exact fun hi ↦ @ne_of_irrefl _ _ wf.transGen.irrefl _ _ (transGen_rootCore parent wf i hi)
  · exact rootCore_of_eq parent wf i

def findAux (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k]) (i : ι) :
    ι × P :=
  let p := parent[i]
  if p = i then
    ⟨i, parent⟩
  else
    let ⟨r, ps⟩ := findAux parent wf p
    ⟨r, ps[i ↦ r]⟩
termination_by wf.wrap i

@[simp]
lemma findAux_fst (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k])
    (i : ι) : (findAux parent wf i).fst = rootCore parent wf i := by
  unfold findAux rootCore; dsimp
  split_ifs with hi
  · rfl
  · exact findAux_fst parent wf _
termination_by wf.wrap i

lemma findAux_snd_getElem (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k])
    (i j : ι) : (findAux parent wf i).snd[j] = parent[j] ∨
      (findAux parent wf i).snd[j] = rootCore parent wf j := by
  unfold findAux rootCore; dsimp
  split_ifs with hi
  · exact .inl rfl
  · obtain (hj | rfl) := decEq i j
    · simp? [hj, - rootCore_parent] says
        simp only [findAux_fst, ne_eq, hj, not_false_eq_true, all_valid,
          getElem_setElem_of_ne]
      exact (findAux_snd_getElem parent wf parent[i] j).imp_right (by rw [·, rootCore])
    · simp [hi]
termination_by wf.wrap i

lemma wellFounded_findAux (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k])
    (i : ι) : WellFounded (fun j k : ι ↦ j ≠ k ∧ j = (findAux parent wf i).snd[k]) := by
  refine Subrelation.wf (r := Relation.TransGen fun i j ↦ i ≠ j ∧ i = parent[j]) ?_ wf.transGen
  rintro j k ⟨hj, rfl⟩
  obtain (hk | hk) := findAux_snd_getElem parent wf i k
  · exact .single ⟨hj, hk⟩
  · rw [hk] at hj ⊢
    exact transGen_rootCore parent wf k <| mt (rootCore_of_eq _ _ _) hj

lemma rootCore_findAux_snd_apply (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k])
    (i : ι) (h) (j : ι) :
    rootCore (findAux parent wf i).snd h j = rootCore parent wf j := by
  unfold rootCore; dsimp
  obtain (H | H) := findAux_snd_getElem parent wf i j <;> rw [H]
  · split_ifs with hj
    · rfl
    · exact rootCore_findAux_snd_apply parent wf i h parent[j]
  · simp only [rootCore_eq_self, rootCore_parent]
    split_ifs with hj
    · rfl
    · rw [rootCore_eq_self]
      obtain (H | H) := findAux_snd_getElem parent wf i (rootCore parent wf j) <;> rw [H]
      · exact parent_rootCore parent wf j
      · rw [rootCore_eq_self, parent_rootCore]
termination_by wf.wrap j

@[simp]
lemma rootCore_findAux_snd (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k])
    (i : ι) (h) :
    rootCore (findAux parent wf i).snd h = rootCore parent wf := by
  ext j; exact rootCore_findAux_snd_apply ..

abbrev root (self : UnionFind ι P S) (i : ι) : ι :=
  rootCore self.parent self.wf i

lemma parent_root (self : UnionFind ι P S) (i : ι) :
    self.parent[self.root i] = self.root i :=
  parent_rootCore ..

lemma root_eq_self (self : UnionFind ι P S) (i : ι) :
    self.root i = i ↔ self.parent[i] = i :=
  rootCore_eq_self self.parent self.wf i

lemma root_of_parent_eq (self : UnionFind ι P S) (i : ι) (hi : self.parent[i] = i) :
    self.root i = i :=
  rootCore_of_eq self.parent self.wf i hi

def find (self : UnionFind ι P S) (i : ι) :
    ι × UnionFind ι P S :=
  let ⟨parent, size, wf⟩ := self
  let f := findAux parent wf i
  ⟨f.1, ⟨f.2, size, wellFounded_findAux _ _ _⟩⟩

@[simp]
lemma find_fst (self : UnionFind ι P S) (i : ι) :
    (self.find i).fst = self.root i :=
  findAux_fst self.parent self.wf i

@[simp]
lemma find_snd_root (self : UnionFind ι P S) (i : ι) :
    (self.find i).snd.root = self.root :=
  rootCore_findAux_snd self.parent self.wf i _

@[simp]
lemma find_snd_size (self : UnionFind ι P S) (i : ι) :
    (self.find i).snd.size = self.size :=
  rfl

omit [DecidableEq ι] in
lemma wellFounded_defaultDictSet (parent : P) (wf : WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[k])
    (i r : ι) (hr : parent[r] = r) :
    WellFounded fun j k : ι ↦ j ≠ k ∧ j = parent[i ↦ r][k] := by
  refine ⟨fun x ↦ ?_⟩
  induction x using wf.induction with
  | h x ih =>
    refine ⟨x, fun p ⟨hpx, h⟩ ↦ ?_⟩
    classical
    simp only [all_valid, getElem_setElem] at h
    split_ifs at h with hx
    · subst hx h
      refine ⟨p, fun f hf ↦ ?_⟩
      simp only [ne_eq, all_valid, getElem_setElem, hr, ite_self, not_and_self] at hf
    · exact ih p ⟨hpx, h⟩

set_option linter.unusedVariables false in -- easier to `rw` and `simp`
@[inline, nolint unusedArguments]
def setParent (parent : P) (size : S) (wf : WellFounded fun i j : ι ↦ i ≠ j ∧ i = parent[j])
    (i j : ι) (hi : parent[i] = i) (hj : parent[j] = j) (s : ℕ) :
    UnionFind ι P S :=
  ⟨parent[i ↦ j], size[j ↦ s], wellFounded_defaultDictSet parent wf i j hj⟩

@[simp]
lemma setParent_parent_eq_parent (parent : P) (size : S)
    (wf : WellFounded fun i j : ι ↦ i ≠ j ∧ i = parent[j])
    (i j : ι) (hi : parent[i] = i) (hj : parent[j] = j) (s : ℕ) (k : ι) :
    (setParent parent size wf i j hi hj s).parent[k] = parent[k] ↔ i = k → j = parent[k] := by
  simp [setParent]

@[simp]
lemma setParent_parent_eq_self (parent : P) (size : S)
    (wf : WellFounded fun i j : ι ↦ i ≠ j ∧ i = parent[j])
    (i j : ι) (hi : parent[i] = i) (hj : parent[j] = j) (s : ℕ) (k : ι) :
    (setParent parent size wf i j hi hj s).parent[k] = k ↔
      (if i = k then j else parent[k]) = k := by
  simp [setParent]

@[simp]
lemma setParent_root (parent : P) (size : S) (wf : WellFounded fun i j : ι ↦ i ≠ j ∧ i = parent[j])
    (i j : ι) (hi : parent[i] = i) (hj : parent[j] = j) (s : ℕ) (k : ι) :
    (setParent parent size wf i j hi hj s).root k =
      if rootCore parent wf k = i then j else rootCore parent wf k := by
  unfold root rootCore; dsimp
  obtain (hk | hk) := decEq parent[k] k <;> simp only [rootCore_parent, hk, ↓reduceIte]
  · have hik : i ≠ k := by aesop
    have : (setParent parent size wf i j hi hj s).parent[k] ≠ k := by
      simp [hik, hk]
    simp only [this, ↓reduceIte]
    convert setParent_root parent size wf i j hi hj s parent[k] using 1
    · simp [← (setParent_parent_eq_parent parent size wf i j hi hj s k).mpr (absurd · hik)]
    · simp
  · simp only [setParent]
    unfold rootCore
    dsimp
    split_ifs <;> aesop
termination_by wf.wrap k

def link (self : UnionFind ι P S) (i j : ι) (hi : self.parent[i] = i) (hj : self.parent[j] = j) :
    UnionFind ι P S :=
  if i = j then
    self
  else
    let ⟨parent, size, wf⟩ := self
    let si := size[i]
    let sj := size[j]
    if si ≤ sj then
      setParent parent size wf i j hi hj (si + sj)
    else
      setParent parent size wf j i hj hi (si + sj)

@[simp]
lemma link_root (self : UnionFind ι P S) (i j : ι) (hi : self.parent[i] = i)
    (hj : self.parent[j] = j) :
    (self.link i j hi hj).root = fun k ↦
      if self.root k = i ∨ self.root k = j then
        if self.size[i] ≤ self.size[j] then j else i
      else
        self.root k := by
  ext k; unfold link; dsimp
  obtain (hij | rfl) := decEq i j
  · rw [if_neg hij]
    split_ifs with hk hs <;> aesop
  · aesop

def union (self : UnionFind ι P S) (i j : ι) : UnionFind ι P S :=
  let fi := self.find i
  let fj := fi.snd.find j
  link fj.snd fi.fst fj.fst
    (by rw [← root_eq_self]; simp [fi, fj])
    (by rw [← root_eq_self]; simp [fi, fj])

@[simp]
lemma union_root (self : UnionFind ι P S) (i j : ι) :
    (self.union i j).root = fun k ↦
      if self.root k = self.root i ∨ self.root k = self.root j then
        if self.size[self.root i] ≤ self.size[self.root j] then self.root j else self.root i
      else
        self.root k := by
  simp [union]; rfl

def WF (self : UnionFind ι P S) : Prop :=
  ∀ i : ι, self.parent[i] = i → self.size[i] = {j : ι | self.root j = i}.encard

lemma wf_congr {x y : UnionFind ι P S}
    (hs : x.size = y.size) (hr : x.root = y.root) : x.WF ↔ y.WF := by
  simp_rw [WF, ← root_eq_self, hs]; rw [hr]

lemma find_snd_wf (self : UnionFind ι P S) (i : ι) (h : self.WF) :
    (self.find i).snd.WF :=
  (wf_congr (self.find_snd_size i) (self.find_snd_root i)).mpr h

lemma wf_iff_size_root {self : UnionFind ι P S} :
    self.WF ↔ ∀ i, self.size[self.root i] = {j : ι | self.root j = self.root i}.encard :=
  ⟨fun wf i ↦ wf (self.root i) (self.parent_root i),
    fun h i hi ↦ self.root_of_parent_eq i hi ▸ h i⟩

lemma setParent_wf (self : UnionFind ι P S)
    (i j : ι) (hi : self.parent[i] = i) (hj : self.parent[j] = j) (hij : i ≠ j) (h : self.WF) :
    (setParent self.parent self.size self.wf i j hi hj (self.size[i] + self.size[j])).WF := by
  intro k hk
  rw [setParent_parent_eq_self] at hk
  conv_lhs => simp only [setParent, all_valid, getElem_setElem]
  split_ifs at hk ⊢ with hjk hik hij
  · simp [hik, hjk] at hij
  · subst hjk
    · rw [ENat.natCast_add, h i hi, h j hk,
        ← Set.encard_union_eq (by rw [Set.disjoint_iff]; intro; aesop)]
      congr
      ext x
      simp? [setParent_root] says
        simp only [Set.mem_union, Set.mem_ofPred_eq, setParent_root, ite_eq_left_iff]
      rw [rootCore]
      split_ifs with h
      · rw [root_of_parent_eq _ _ h]; tauto
      · rw [root, rootCore, if_neg h]; tauto
  · simp [hk] at hjk
  · rw [h k hk]
    congr! 3
    aesop

lemma link_wf (self : UnionFind ι P S) (i j : ι) (hi : self.parent[i] = i) (hj : self.parent[j] = j)
    (h : self.WF) : (self.link i j hi hj).WF := by
  unfold link; dsimp
  split_ifs with hij
  · exact h
  · exact setParent_wf _ _ _ _ _ hij h
  · exact Nat.add_comm _ _ ▸ setParent_wf _ _ _ _ _ (Ne.symm hij) h

lemma union_wf (self : UnionFind ι P S) (i j : ι) (h : self.WF) : (self.union i j).WF := by
  unfold union; dsimp
  exact link_wf _ _ _ _ _ (find_snd_wf _ j (self.find_snd_wf i h))

section default

variable [OfFn P ι ι id] [OfFn S ι ℕ (fun _ ↦ 1)]

instance : Inhabited (UnionFind ι P S) where
  default := ⟨ofFn (id : ι → ι), ofFn (fun _ : ι ↦ 1), ⟨fun i ↦ ⟨i, by simp⟩⟩⟩

@[simp]
lemma default_parent : (default : UnionFind ι P S).parent = ofFn (id : ι → ι) :=
  rfl

@[simp]
lemma default_size : (default : UnionFind ι P S).size = ofFn (fun _ : ι ↦ 1) :=
  rfl

@[simp]
lemma default_root : (default : UnionFind ι P S).root = id := by
  ext; simp

lemma default_wf : (default : UnionFind ι P S).WF :=
  fun i ↦ by rw [default_root]; simp

end default

-- def finsetOfRoot (self : UnionFind ι P S) (r : ι) : Finset ι :=
--   ((insert r (toDFinsupp' self.parent).support).filter (self.root · = r))

-- lemma mem_finsetOfRoot_iff (self : UnionFind ι P S) (r i : ι) :
--     i ∈ self.finsetOfRoot r ↔ self.root i = r := by
--   simp? [finsetOfRoot] says
--     simp only [finsetOfRoot, Finset.mem_filter, Finset.mem_insert, DFinsupp'.mem_support_toFun,
--       id_eq, coe_toDFinsupp'_eq_get, Get.get_eq_getElem, ne_eq, and_iff_right_iff_imp]
--   obtain (hr | hr) := decEq self.parent[i] i
--   · simp [hr]
--   · simp [hr, root, rootCore]

-- instance (self : UnionFind ι P S) (r : ι) : Finite {i | self.root i = r} :=
--   Set.Finite.ofFinset (self.finsetOfRoot r) (self.mem_finsetOfRoot_iff r)

end UnionFind

def UnionFindWF (ι : Type*) [DecidableEq ι]
    (P : Type*) [GetSetElemAllValid P ι ι]
    (S : Type*) [GetSetElemAllValid S ι ℕ] :=
  { x : UnionFindImpl.UnionFind ι P S // x.WF }

namespace UnionFindWF

variable {ι : Type*} [DecidableEq ι]
    {P : Type*} [GetSetElemAllValid P ι ι]
    {S : Type*} [GetSetElemAllValid S ι ℕ]

def IsRoot (self : UnionFindWF ι P S) (i : ι) : Prop := self.val.parent[i] = i

abbrev root (self : UnionFindWF ι P S) (i : ι) : ι := self.val.root i

lemma isRoot_iff_root {self : UnionFindWF ι P S} {i : ι} :
    self.IsRoot i ↔ self.root i = i := by
  simp [IsRoot]

alias ⟨IsRoot.root_eq, _⟩ := isRoot_iff_root

lemma IsRoot.root (self : UnionFindWF ι P S) (i : ι) :
    self.IsRoot (self.root i) :=
  isRoot_iff_root.mpr (by simp)

abbrev find (self : UnionFindWF ι P S) (i : ι) :
    ι × UnionFindWF ι P S :=
  let ⟨x, hx⟩ := self
  let f := x.find i
  ⟨f.1, ⟨f.2, x.find_snd_wf i hx⟩⟩

@[simp]
lemma find_fst (self : UnionFindWF ι P S) (i : ι) :
    (self.find i).fst = self.root i :=
  self.val.find_fst i

@[simp]
lemma find_snd_root (self : UnionFindWF ι P S) (i : ι) :
    (self.find i).snd.root = self.root :=
  self.val.find_snd_root i

lemma isRoot_iff_find {self : UnionFindWF ι P S} {i : ι} :
    self.IsRoot i ↔ (self.find i).fst = i := by
  simp [IsRoot]

abbrev union (self : UnionFindWF ι P S) (i j : ι) : UnionFindWF ι P S :=
  ⟨self.val.union i j, self.val.union_wf i j self.prop⟩

set_option linter.unusedVariables false in -- easier to `rw` and `simp`
@[nolint unusedArguments]
abbrev size (self : UnionFindWF ι P S) (i : ι) (hi : self.IsRoot i) : ℕ :=
  self.val.size[i]

lemma size_eq_ncard (x : UnionFindWF ι P S) (i : ι) (hxi : x.IsRoot i) :
    x.size i hxi = {j | x.root j = i}.ncard := by
  simp [size, Set.ncard, ← x.prop i hxi]

lemma size_eq_of_root_eq (x y : UnionFindWF ι P S) (i : ι) (hxi : x.IsRoot i) (hyi : y.IsRoot i)
    (h : x.root = y.root) : x.size i hxi = y.size i hyi := by
  simp [size, x.size_eq_ncard i hxi, y.size_eq_ncard i hyi, h]

@[simp]
lemma union_root (self : UnionFindWF ι P S) (i j : ι) :
    (self.union i j).root = fun k ↦
      if self.root k = self.root i ∨ self.root k = self.root j then
        if self.size (self.root i) (.root _ _) ≤ self.size (self.root j) (.root _ _) then
          self.root j
        else
          self.root i
      else
        self.root k :=
  self.val.union_root i j

end UnionFindWF

end UnionFindImpl

def UnionFind (ι : Type*) [DecidableEq ι]
    (P : Type*) [GetSetElemAllValid P ι ι]
    (S : Type*) [GetSetElemAllValid S ι ℕ] :=
  Quotient <| .ker fun x : UnionFindImpl.UnionFindWF ι P S ↦ x.root

namespace UnionFind

variable {ι : Type*} [DecidableEq ι]
    {P : Type*} [GetSetElemAllValid P ι ι]
    {S : Type*} [GetSetElemAllValid S ι ℕ]

instance [OfFn P ι ι id] [OfFn S ι ℕ (fun _ ↦ 1)] : Inhabited (UnionFind ι P S) where
  default := ⟦⟨default, UnionFindImpl.UnionFind.default_wf⟩⟧

@[inline]
def find (self : UnionFind ι P S) (i : ι) : ι × UnionFind ι P S :=
  Quotient.liftOn' self (fun x ↦ let f := x.find i; (f.1, ⟦f.2⟧)) fun x y h ↦ by
    rw [Setoid.ker_def] at h
    ext
    · simp [h]
    · apply Quot.sound
      simp [h]

@[simp]
lemma find_snd (self : UnionFind ι P S) (i : ι) : (self.find i).snd = self := by
  induction self using Quotient.inductionOn with
  | _ x => exact Quotient.sound (x.find_snd_root i)

def IsRoot (self : UnionFind ι P S) (i : ι) : Prop := (self.find i).fst = i

lemma find_isRoot (self : UnionFind ι P S) (i : ι) :
    (self.find i).snd.IsRoot (self.find i).fst := by
  induction self using Quotient.inductionOn
  simp [IsRoot, find]

@[inline]
def union (self : UnionFind ι P S) (i j : ι) : UnionFind ι P S :=
  self.map' (fun x ↦ x.union i j) fun x y h ↦ by
    simp only [Setoid.ker_def] at h ⊢
    simp only [UnionFindImpl.UnionFindWF.union_root,
      UnionFindImpl.UnionFindWF.size_eq_ncard]
    rw [h]

@[inline]
def size (self : UnionFind ι P S) (i : ι) (hi : self.IsRoot i) : ℕ :=
  self.hrecOn (fun x hx ↦ x.size i (UnionFindImpl.UnionFindWF.isRoot_iff_find.mpr hx))
    (fun x y h ↦ Function.hfunext
      (congrArg (fun self : UnionFind ι P S ↦ self.IsRoot i) (Quotient.sound h))
      fun _ _ _ ↦ heq_of_eq <| UnionFindImpl.UnionFindWF.size_eq_of_root_eq x y i _ _ h) hi

end UnionFind
