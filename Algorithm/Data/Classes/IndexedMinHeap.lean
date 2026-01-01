/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.DefaultDict
import Algorithm.Data.Classes.MinHeap
import Algorithm.Data.Classes.ToList
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Prod.Lex

class IndexedMinHeap (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) [Preorder α] [IsTotal α (· ≤ ·)] [OrderTop α] extends
    AssocDArray C ι α fun _ ↦ ⊤ where
  minIdx : C → ι
  getElem_minIdx_le c (i : ι) : c[minIdx c] ≤ c[i]
  decreaseKey (c : C) (i : ι) : ∀ v < c[i], C := fun v _ ↦ c[i ↦ v]
  decreaseKey_eq_set (c : C) (i : ι) v (h : v < c[i]) : decreaseKey c i v h = c[i ↦ v] := by
    intros; rfl
export IndexedMinHeap (minIdx getElem_minIdx_le decreaseKey decreaseKey_eq_set)

attribute [simp] decreaseKey_eq_set

section IndexedMinHeap
variable {C : Type*} [Inhabited C] {ι : Type*} {α : Type*} [LinearOrder α] [OrderTop α]
  [IndexedMinHeap C ι α]

def decreaseKeyD (c : C) (i : ι) (v : α) : C :=
  if c[i] ≤ v then c else c[i ↦ v]

@[simp]
lemma decreaseKeyD_getElem [DecidableEq ι]
    (c : C) (i : ι) (v : α) (j : ι) :
    (decreaseKeyD c i v)[j] = if i = j then min c[j] v else c[j] := by
  split_ifs with h <;> rw [decreaseKeyD, apply_ite (fun c : C ↦ c[j])]
  · simp [h, min_def]
  · simp [h]

def decreaseKeysD {ια : Type*} [ToList ια (ι × α)] (c : C) (iv : ια) : C :=
  (toList iv).foldl (fun c ⟨i, v⟩ ↦ decreaseKeyD c i v) c

@[simp]
lemma decreaseKeysD_getElem [DecidableEq ι] {ια : Type*} [ToList ια (ι × α)]
    (c : C) (iv : ια) (i : ι) :
    (decreaseKeysD c iv)[i] = min c[i] ((toMultiset iv).filterMap
      (fun iv ↦ if iv.1 = i then some iv.2 else none)).inf := by
  rw [← coe_toList, decreaseKeysD]
  generalize toList iv = l
  simp only [Multiset.filterMap_coe, Multiset.inf_coe]
  induction l generalizing c with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, ih, decreaseKeyD_getElem]
    split_ifs with h
    · simp only [List.filterMap_cons, h, min_assoc]
      congr
    · simp [h]

end IndexedMinHeap

namespace Vector
variable {α : Type*} [LinearOrder α] {n : ℕ} [NeZero n] {d : Fin n → α}

section ReadOnly

variable [AssocDArray.ReadOnly (Vector α n) (Fin n) α d]

abbrev minAux (a : Vector α n) : Lex (α × Fin n) :=
  (⊤ : Finset (Fin n)).inf' ⟨0, Finset.mem_univ 0⟩ (fun i ↦ toLex (a[i], i))

@[inline]
def minIdx (a : Vector α n) : Fin n :=
  a.minAux.2

lemma minIdx_spec (a : Vector α n) (i : Fin n) :
    a[a.minIdx] < a[i] ∨ a[a.minIdx] = a[i] ∧ a.minIdx ≤ i := by
  have : (ofLex a.minAux).1 = a[a.minIdx] := by
    unfold minIdx minAux
    obtain ⟨i, -, h⟩ := (⊤ : Finset (Fin n)).exists_mem_eq_inf'
      ⟨0, Finset.mem_univ 0⟩ (fun i ↦ toLex (a[i], i))
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    obtain ⟨h : _ = a[i], rfl : _ = i⟩ := h
    exact h
  rw [← this]
  apply (Prod.Lex.le_iff (y := (a[i], i))).mp
  exact Finset.inf'_le _ (Finset.mem_univ _)

lemma minIdx_le (a : Vector α n) (i : Fin n) :
    a[a.minIdx] ≤ a[i] :=
  (a.minIdx_spec i).elim LT.lt.le (fun ⟨h, _⟩ ↦ h.le)

end ReadOnly

instance WithDefault.instIndexedMinHeap [OrderTop α] :
    IndexedMinHeap (Vector.WithDefault α n fun _ ↦ ⊤) (Fin n) α where
  minIdx := minIdx
  getElem_minIdx_le a i := a.minIdx_le i

end Vector

namespace WithTop

instance (α) (x : WithTop α) : Decidable (x = ⊤) :=
  match x with
  | ⊤ => .isTrue rfl
  | (x : α) => .isFalse nofun

end WithTop

structure DefaultDictWithHeap.WithIdx (α ι : Type*) where
  val : α
  idx : ι

namespace DefaultDictWithHeap.WithIdx
variable {α ι : Type*}

instance [LE α] : LE (DefaultDictWithHeap.WithIdx α ι) where
  le x y := x.val ≤ y.val

lemma le_def [LE α] {x y : DefaultDictWithHeap.WithIdx α ι} :
    x ≤ y ↔ x.val ≤ y.val :=
  Iff.rfl

@[simp]
lemma mk_le_mk [LE α] {x y : α} {xi yi : ι} :
    mk x xi ≤ mk y yi ↔ x ≤ y :=
  Iff.rfl

instance [LT α] : LT (DefaultDictWithHeap.WithIdx α ι) where
  lt x y := x.val < y.val

@[simp]
lemma mk_lt_mk [LT α] {x y : α} {xi yi : ι} :
    mk x xi < mk y yi ↔ x < y :=
  Iff.rfl

instance [Preorder α] : Preorder (DefaultDictWithHeap.WithIdx α ι) where
  le_refl _ := le_refl _
  le_trans _ _ _ := le_trans
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge

instance [Preorder α] [IsTotal α (· ≤ ·)] :
    IsTotal (DefaultDictWithHeap.WithIdx α ι) (· ≤ ·) where
  total _ _ := total_of (α := α) (· ≤ ·) _ _

end DefaultDictWithHeap.WithIdx

structure DefaultDictWithHeap (C C' : Type*) {ι α : Type*} [Preorder α] [IsTotal α (· ≤ ·)]
    [Inhabited C] [DefaultDict C ι (WithTop α) ⊤]
    [MinHeap C' (DefaultDictWithHeap.WithIdx α ι)] where mk' ::
  defaultDict : C
  minHeap : C'
  mem_minHeap' : ∀ i : ι, (hi : defaultDict[i] ≠ ⊤) → ⟨defaultDict[i].untop hi, i⟩ ∈ minHeap
  getElem_minIdx' : (h : ¬isEmpty minHeap) →
    defaultDict[(MinHeap.head minHeap h).idx] = (MinHeap.head minHeap h).val

namespace DefaultDictWithHeap
variable {C C' : Type*} {ι α : Type*} [Preorder α] [IsTotal α (· ≤ ·)]
  [Inhabited C] [DefaultDict C ι (WithTop α) ⊤]
  [MinHeap C' (DefaultDictWithHeap.WithIdx α ι)]

instance : DefaultDict.ReadOnly (DefaultDictWithHeap C C') ι (WithTop α) ⊤ where
  getElem c i _ := c.defaultDict[i]
  toDFinsupp' c := toDFinsupp' c.defaultDict
  coe_toDFinsupp'_eq_getElem c := coe_toDFinsupp'_eq_getElem c.defaultDict

@[simp]
lemma defaultDict_getElem (c : DefaultDictWithHeap C C') (i : ι) :
    c.defaultDict[i] = c[i] :=
  rfl

lemma mem_minHeap (c : DefaultDictWithHeap C C') :
    ∀ i : ι, (hi : c[i] ≠ ⊤) → ⟨c[i].untop hi, i⟩ ∈ c.minHeap :=
  c.mem_minHeap'

lemma getElem_minIdx (c : DefaultDictWithHeap C C') (h : ¬isEmpty c.minHeap) :
    c[(MinHeap.head c.minHeap h).idx] = (MinHeap.head c.minHeap h).val :=
  c.getElem_minIdx' h

instance : Inhabited (DefaultDictWithHeap C C') where
  default := ⟨default, ∅, by simp, by simp [sizeTM_eq_card_toMultiset, isEmpty_iff_sizeTM_eq_zero]⟩

def mk [DecidableEq α] (defaultDict : C) (minHeap : C')
    (mem_minHeap : ∀ i : ι, (hi : defaultDict[i] ≠ ⊤) → ⟨(defaultDict[i]).untop hi, i⟩ ∈ minHeap) :
    DefaultDictWithHeap C C' :=
  if h : isEmpty minHeap then
    ⟨defaultDict, minHeap, mem_minHeap, (False.elim <| · h)⟩
  else if h' : defaultDict[(MinHeap.head minHeap h).idx] = (MinHeap.head minHeap h).val then
    ⟨defaultDict, minHeap, mem_minHeap, fun _ ↦ h'⟩
  else
    haveI : DecidableEq (WithIdx α ι) := by classical infer_instance
    have : sizeTM (MinHeap.tail minHeap) < sizeTM minHeap := by
      simpa [h, sizeTM_eq_card_toMultiset, Multiset.card_erase_lt_of_mem] using
        Multiset.card_erase_lt_of_mem (MinHeap.head_mem_toMultiset _ _)
    mk defaultDict (MinHeap.tail minHeap) fun i hi ↦ by
      simp only [← mem_toMultiset, MinHeap.toMultiset_tail, h, Bool.false_eq_true, ↓reduceDIte,
        MinHeap.head_def]
      rw [Multiset.mem_erase_of_ne, mem_toMultiset]
      · exact mem_minHeap _ _
      · intro h''
        apply h'
        simp [← h'', MinHeap.head_def]
termination_by sizeTM minHeap

@[simp, nolint unusedHavesSuffices] -- false positive
lemma mk_defaultDict [DecidableEq α] (defaultDict : C) (minHeap : C')
    (mem_minHeap : ∀ i : ι, (hi : defaultDict[i] ≠ ⊤) → ⟨(defaultDict[i]).untop hi, i⟩ ∈ minHeap) :
    (mk defaultDict minHeap mem_minHeap).defaultDict = defaultDict := by
  induction minHeap, mem_minHeap using mk.induct
  all_goals unfold mk; simp [*]

@[simp]
lemma default_defaultDict :
    (default : DefaultDictWithHeap C C').defaultDict = default :=
  rfl

@[simp]
lemma default_minHeap :
    (default : DefaultDictWithHeap C C').minHeap = ∅ :=
  rfl

instance [DecidableEq α] :
    DefaultDict (DefaultDictWithHeap C C') ι (WithTop α) ⊤ where
  setElem c i x :=
    mk
      c.defaultDict[i ↦ x]
      (if hx : x = ⊤ then c.minHeap else insert ⟨x.untop hx, i⟩ c.minHeap)
      fun j hj ↦ by
        haveI : DecidableEq ι := by classical infer_instance
        split_ifs with hx <;>
          simp? [Function.update_apply] at hj ⊢ says
            simp only [all_valid, getElem_setElem, defaultDict_getElem, ne_eq] at hj ⊢
        · subst hx
          rw [ite_eq_left_iff, Classical.not_imp] at hj
          simp only [hj.1, ↓reduceIte]
          exact c.mem_minHeap j hj.2
        · -- TODO: `mem_insert`
          rw [← mem_toMultiset, toMultiset_insert, Multiset.mem_cons, mem_toMultiset]
          split_ifs at hj ⊢ with hji
          · simp [hji]
          · exact .inr <| c.mem_minHeap j hj
  getElem_setElem_self _ _ _ := by simp [getElem]
  getElem_setElem_of_ne _ _ _ _ _ := by simp only [getElem]; simp [*]
  getElem_default := by simp [getElem]

@[simp]
lemma set_defaultDict [DecidableEq α] (c : DefaultDictWithHeap C C') (i : ι) (x) :
    c[i ↦ x].defaultDict = c.defaultDict[i ↦ x] := by
  unfold_projs; simp

instance [Inhabited ι] [DecidableEq α] :
    IndexedMinHeap (DefaultDictWithHeap C C') ι (WithTop α) where
  minIdx c := if h : isEmpty c.minHeap then default else (MinHeap.head c.minHeap h).idx
  getElem_minIdx_le c i := by
    split_ifs with h
    · suffices ∀ i : ι, c[i] = ⊤ by simp [this]
      intro i
      contrapose h with hi
      simpa [sizeTM_eq_card_toMultiset, Multiset.eq_zero_iff_forall_notMem,
        isEmpty_iff_sizeTM_eq_zero] using ⟨_, c.mem_minHeap i hi⟩
    · rw [getElem_minIdx c h, WithTop.coe_le_iff]
      intro x hx
      refine (WithIdx.le_def.mp <| MinHeap.head_le c.minHeap _ (c.mem_minHeap i ?_)).trans ?_ <;>
        simp [hx]

end DefaultDictWithHeap
