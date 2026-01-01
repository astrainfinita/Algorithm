/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.MinHeap
import Batteries.Data.PairingHeap
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Tactic.Abel

namespace Batteries

variable {α β : Type*} {le : α → α → Bool}

namespace PairingHeapImp

@[simp]
lemma Heap.size_nil :
    nil (α := α).size = 0 :=
  rfl

@[simp]
lemma Heap.size_node (a : α) (c s : Heap α) :
    (node a c s).size = c.size + 1 + s.size :=
  rfl

@[simp]
lemma Heap.foldTree_nil (nil : β) (join : α → β → β → β) :
    Heap.nil.foldTree nil join = nil :=
  rfl

@[simp]
lemma Heap.foldTree_node (nil : β) (join : α → β → β → β) (a : α) (c s : Heap α) :
    (node a c s).foldTree nil join = join a (c.foldTree nil join) (s.foldTree nil join) :=
  rfl

@[simp]
lemma Heap.toListUnordered_nil :
    nil.toListUnordered = ([] : List α) :=
  rfl

@[simp]
lemma Heap.toListUnordered_node (a : α) (c s : Heap α) :
    (node a c s).toListUnordered = a :: (c.toListUnordered ++ s.toListUnordered) := by
  unfold toListUnordered
  generalize hl : [] = l; nth_rw 2 [← hl]; clear hl
  induction c generalizing s l with
  | nil => rfl
  | node a c' s' ihc' ihs' =>
    simp? at * says simp only [foldTree_node, List.cons.injEq, true_and, List.cons_append] at *
    rw [ihc', ihc', ihs', List.append_assoc]

@[simp]
lemma Heap.length_toListUnordered (x : Heap α) :
    x.toListUnordered.length = x.size := by
  induction x with
  | nil => rfl
  | node _ _ _ _ _ => simp [*, Nat.add_right_comm]

attribute [simp] Heap.noSibling_merge

@[simp]
lemma Heap.merge_nil_right (x : Heap α) (hx : x.NoSibling) :
    x.merge le nil = x :=
  match x, hx with | nil, _ | node _ _ nil, _ => rfl

@[simp]
lemma Heap.coe_toListUnordered_merge_node_right
    (x : Heap α) (hx : x.NoSibling) (a : α) (c s : Heap α) :
    ((x.merge le (node a c s)).toListUnordered : Multiset α) =
      x.toListUnordered + (a ::ₘ c.toListUnordered : Multiset α) := by
  match x, hx with
  | nil, _ => rfl
  | node _ _ nil, _ =>
    simp_rw [merge]
    split_ifs <;> (
      simp_rw [toListUnordered_node, toListUnordered_nil, List.append_nil,
        ← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add]
      #adaptation_note /-- was `ac_rfl` before `v4.17.0` -/
      abel)

@[simp]
lemma Heap.coe_toListUnordered_merge_node (a₁ : α) (c₁ s₁ : Heap α) (a₂ : α) (c₂ s₂ : Heap α) :
    (((node a₁ c₁ s₁).merge le (node a₂ c₂ s₂)).toListUnordered : Multiset α) =
      a₁ ::ₘ a₂ ::ₘ c₁.toListUnordered + c₂.toListUnordered := by
  simp_rw [merge]
  split_ifs <;> (
    simp_rw [toListUnordered_node, toListUnordered_nil, List.append_nil,
      ← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add]
    #adaptation_note /-- was `ac_rfl` before `v4.17.0` -/
    abel)

lemma Heap.coe_toListUnordered_merge (x : Heap α) (y : Heap α)
    (hx : x.NoSibling) (hy : y.NoSibling) :
    ((x.merge le y).toListUnordered : Multiset α) = x.toListUnordered + y.toListUnordered := by
  match x, y, hx, hy with
  | nil, nil, _, _ => rfl
  | nil, node a c nil, _, _ =>
    rw [merge, toListUnordered_node, toListUnordered_nil, Multiset.coe_nil, zero_add]
  | node a c nil, nil, _, _ =>
    rw [merge, toListUnordered_node, toListUnordered_nil, Multiset.coe_nil, add_zero]
  | node a₁ c₁ nil, node a₂ c₂ nil, _, _ =>
    simp_rw [coe_toListUnordered_merge_node, toListUnordered_node, toListUnordered_nil,
      List.append_nil, ← Multiset.cons_coe, ← Multiset.singleton_add]
    #adaptation_note /-- was `ac_rfl` before `v4.17.0` -/
    abel

theorem Heap.WF.noSibling {x : Heap α} (hx : x.WF le) : x.NoSibling :=
  match x, hx with
  | .nil, _ => .nil
  | .node _ _ .nil, _ => .node _ _

lemma Heap.le_of_nodeWF [t : IsTrans α (le · ·)] [TotalBLE le]
    (a : α) (x : Heap α) (hx : x.NodeWF le a) :
    ∀ b ∈ x.toListUnordered, le a b := by
  intro b hb
  induction x generalizing a with
  | nil => nomatch hb
  | node xa xc xs hc hs =>
    simp? at hb says simp only [toListUnordered_node, List.mem_cons, List.mem_append] at hb
    obtain ⟨hx, hxc, hxs⟩ := hx
    obtain (rfl | hb | hb) := hb
    · exact hx
    · have := hc xa hxc hb
      exact t.trans _ _ _ hx this
    · exact hs a hxs hb

lemma Heap.le_of_wf [r : IsRefl α (le · ·)] [t : IsTrans α (le · ·)] [TotalBLE le]
    (a : α) (c s : Heap α) (hx : (node a c s).WF le) :
    ∀ b ∈ (node a c s).toListUnordered, le a b := by
  intro b hb
  simp? at hb says simp only [toListUnordered_node, List.mem_cons, List.mem_append] at hb
  cases hx with
  | node hx =>
    obtain (rfl | hb | hb) := hb
    · exact r.refl b
    · exact Heap.le_of_nodeWF a c hx b hb
    · nomatch hb

@[simp]
lemma Heap.coe_toListUnordered_combine (x : Heap α) :
    ((x.combine le).toListUnordered : Multiset α) = x.toListUnordered := by
  induction x using Heap.combine.induct with
  | case1 a₁ c₁ a₂ c₂ s ih =>
    match hc : combine le s, noSibling_combine le s with
    | .nil, _ =>
      simp? [combine, hc, - Multiset.coe_eq_coe, - Multiset.cons_coe, - Multiset.coe_add] says
        simp only [combine, hc, noSibling_merge, merge_nil_right, coe_toListUnordered_merge_node,
          Multiset.cons_add, toListUnordered_node]
      simp only [← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add, ← ih, hc]
      #adaptation_note /-- was `ac_rfl` before `v4.17.0` -/
      abel
    | .node sa sc .nil, _ =>
      simp? [combine, hc, toListUnordered_node, - Multiset.coe_eq_coe, - Multiset.cons_coe,
          - Multiset.coe_add] says
        simp only [combine, hc, noSibling_merge,
          coe_toListUnordered_merge_node_right, coe_toListUnordered_merge_node, Multiset.cons_add,
          Multiset.add_cons, toListUnordered_node]
      simp only [← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add, ← ih, hc,
        toListUnordered_node]
      #adaptation_note /-- was `ac_rfl` before `v4.17.0` -/
      abel
  | case2 x hx =>
    simp [combine]

end PairingHeapImp

namespace PairingHeap

@[simp]
lemma coe_toListUnordered_merge (x : PairingHeap α le) (y : PairingHeap α le) :
    ((x.merge y).toListUnordered : Multiset α) = x.toListUnordered + y.toListUnordered :=
  x.val.coe_toListUnordered_merge y.val x.prop.noSibling y.prop.noSibling

@[simp]
lemma coe_toListUnordered_singleton (a : α) :
    ((singleton a : PairingHeap α le).toListUnordered : Multiset α) = {a} :=
  rfl

instance : ToMultiset (PairingHeap α le) α where
  isEmpty x := x.isEmpty
  isEmpty_iff_forall_not_mem {x} :=
    match x with
    | ⟨.nil, _⟩ | ⟨.node _ _ _, _⟩ => by
      simp [isEmpty, PairingHeapImp.Heap.isEmpty, toListUnordered, - not_or]
  toMultiset x := x.toListUnordered

instance : Size (PairingHeap α le) where
  size x := x.size
  size_eq_sizeTM := by simp [size, toListUnordered, sizeTM, toMultiset]

instance : EmptyCollection (PairingHeap α le) where
  emptyCollection := empty

instance : LawfulEmptyCollection (PairingHeap α le) α :=
  .of_toMultiset rfl

@[simp]
lemma size_eq_zero_iff (x : PairingHeap α le) : x.size = 0 ↔ x = ∅ := by
  match x with
  | ⟨.nil, _⟩ => simpa [size] using by exact rfl
  | ⟨.node _ _ _, _⟩ => simpa [size] using nofun

instance : Insert α (PairingHeap α le) where
  insert := insert

instance : ToMultiset.LawfulInsert (PairingHeap α le) α where
  toMultiset_insert a x := by
    simp only [Insert.insert, insert, toMultiset]
    rw [coe_toListUnordered_merge, coe_toListUnordered_singleton]
    simp

instance : Mergeable (PairingHeap α le) α where
  merge := merge
  toMultiset_merge a x := by
    simp only [toMultiset, coe_toListUnordered_merge]

instance [Preorder α] [IsTotal α (· ≤ ·)] [DecidableRel (α := α) (· ≤ ·)] :
    MinHeap (PairingHeap α (· ≤ ·)) α where
  head? x := x.head?.rec ⊤ WithTop.some
  tail := tail
  deleteMin := deleteMin
  head?_eq_top x := by
    simpa only [isEmpty_iff_size_eq_zero, Size.size, size_eq_zero_iff] using by rintro rfl; rfl
  head?_mem_toMultiset_map x hx := by
    simp only [isEmpty_iff_size_eq_zero] at hx
    match x, hx with
    | ⟨.node a c .nil, _⟩, _ =>
      simpa [- mem_toMultiset] using ⟨a, by
        simp [toMultiset, toListUnordered, PairingHeapImp.Heap.toListUnordered_node], rfl⟩
  head?_le x b hb := by
    match x with
    | ⟨.node a c .nil, hwf⟩ =>
      simp_rw [← mem_toMultiset, toMultiset, toListUnordered,
        PairingHeapImp.Heap.toListUnordered_node, PairingHeapImp.Heap.toListUnordered_nil,
        List.append_nil, ← Multiset.cons_coe, Multiset.mem_cons] at hb
      obtain (rfl | hb) := hb; · rfl
      haveI : TotalBLE (α := α) (· ≤ ·) := ⟨by simp [total_of]⟩
      have := @PairingHeapImp.Heap.le_of_wf α (· ≤ ·) ⟨by simp⟩
        ⟨by simpa using fun _ _ _ ↦ le_trans⟩ _ a c .nil hwf
      simp? at this says
        simp only [PairingHeapImp.Heap.toListUnordered_node,
          PairingHeapImp.Heap.toListUnordered_nil, List.append_nil, List.mem_cons,
          decide_eq_true_eq, forall_eq_or_imp, le_refl, true_and] at this
      simpa [head?, PairingHeapImp.Heap.head?] using this b hb
  toMultiset_tail x h := by
    match x with
    | ⟨.nil, _⟩ => rfl
    | ⟨.node a c .nil, _⟩ =>
      simp? [Membership.IsEmpty.isEmpty, isEmpty, PairingHeapImp.Heap.isEmpty, tail,
          PairingHeapImp.Heap.tail, toMultiset, toListUnordered, PairingHeapImp.Heap.tail?,
          PairingHeapImp.Heap.deleteMin, - Multiset.coe_eq_coe, - Multiset.coe_erase] says
        simp only [toMultiset, toListUnordered, tail, PairingHeapImp.Heap.tail,
          PairingHeapImp.Heap.tail?, PairingHeapImp.Heap.deleteMin, Option.map_some,
          Option.getD_some, PairingHeapImp.Heap.coe_toListUnordered_combine,
          Membership.IsEmpty.isEmpty, isEmpty, PairingHeapImp.Heap.isEmpty, Bool.false_eq_true,
          ↓reduceDIte, PairingHeapImp.Heap.toListUnordered_node,
          PairingHeapImp.Heap.toListUnordered_nil, List.append_nil]
      change _ = Multiset.erase _ a
      simp
  deleteMin_def x := by match x with | ⟨.nil, _⟩ | ⟨.node _ _ _, _⟩ => rfl

end Batteries.PairingHeap
