/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Algorithm.Data.Classes.ToMultiset
public import Mathlib.Data.Multiset.Lattice
public import Mathlib.Order.WithBot

@[expose] public section

namespace Multiset -- should be in mathlb
variable {α : Type*} [SemilatticeInf α] [OrderTop α]

@[simp]
theorem inf_eq_top {m : Multiset α} : m.inf = ⊤ ↔ ∀ a ∈ m, a = ⊤ := by
  rw [le_antisymm_iff]
  simp

end Multiset

class MinHeap (C : Type*) (α : outParam Type*)
    [Preorder α] [IsTotal α (· ≤ ·)] extends
    ToMultiset C α,
    EmptyCollection C, LawfulEmptyCollection C α,
    Insert α C, ToMultiset.LawfulInsert C α where
  head? : C → WithTop α
  head?_eq_top c : isEmpty c → head? c = ⊤
  head?_mem_toMultiset_map c : ¬isEmpty c → (head? c) ∈ (toMultiset c).map (↑)
  head?_le (c : C) : ∀ x ∈ c, head? c ≤ x
  headD : C → α → α :=
    fun s d ↦ (head? s).getD d
  head (c : C) : ¬isEmpty c → α :=
    fun h ↦ (head? c).untop fun hc ↦ by
      have := hc ▸ (head?_mem_toMultiset_map c h)
      simp at this
  headD_def c d : headD c d = (head? c).getD d := by intros; rfl
  coe_head_eq_head? c h : head c h = head? c := by simp
  tail : C → C
  toMultiset_tail c : [DecidableEq α] → toMultiset (tail c) =
    if h : isEmpty c then 0 else (toMultiset c).erase (head c h)
  deleteMin : C → Option (α × C) := fun c ↦ if h : isEmpty c then none else
    some (head c h, tail c)
  deleteMin_def c : deleteMin c = if h : isEmpty c then none else
    some (head c h, tail c) := by rfl

namespace MinHeap

attribute [simp] headD_def toMultiset_tail deleteMin_def

section

variable {C α : Type*} [Preorder α] [IsTotal α (· ≤ ·)] [MinHeap C α] (c : C)

lemma head?_ne_top (h : ¬isEmpty c) :
    (MinHeap.head? c) ≠ ⊤ := by
  intro hc
  have := hc ▸ (head?_mem_toMultiset_map c h)
  simp at this

lemma head_def (h : ¬isEmpty c) :
    MinHeap.head c h = (head? c).untop (head?_ne_top c h) :=
  WithTop.coe_injective (by simpa using MinHeap.coe_head_eq_head? c h)

lemma head_mem_toMultiset (h : ¬isEmpty c) :
    head c h ∈ toMultiset c := by
  obtain ⟨x, hx₁, hx₂⟩ := Multiset.mem_map.mp (head?_mem_toMultiset_map c h)
  simp [hx₁, ← hx₂, head_def]

lemma head_mem (h : ¬isEmpty c) :
    head c h ∈ c := by
  exact mem_toMultiset.mp (head_mem_toMultiset c h)

lemma head_le (x) (hx : x ∈ c) :
    head c (ToMultiset.not_isEmpty_of_mem hx) ≤ x := by
  simpa [WithTop.untop_le_iff, head_def] using head?_le c x hx

lemma coe_eq_head?_of_forall_le (p : α → Prop) (hc : ¬isEmpty c) (pc : p (head c hc))
    (x : α) (hx : x ∈ c) (h : ∀ y ∈ c, p y → y ≠ x → x < y) :
    x = head? c := by
  contrapose! h
  exact ⟨head c (ToMultiset.not_isEmpty_of_mem hx), MinHeap.head_mem _ _, pc,
    by intro h'; simp [← h', head_def] at h, fun h' ↦ (h'.trans_le (head_le c _ hx)).ne rfl⟩

lemma eq_head_of_forall_le (p : α → Prop) (hc : ¬isEmpty c) (pc : p (head c hc))
    (x : α) (hx : x ∈ c) (h : ∀ y ∈ c, p y → y ≠ x → x < y) :
    x = head c hc := by
  apply WithTop.coe_injective
  simpa [head_def] using coe_eq_head?_of_forall_le c p hc pc x hx h

end

section LinearOrder

variable {C α : Type*} [LinearOrder α] [MinHeap C α] {c : C}

@[simp]
lemma head?_def : head? c = ((toMultiset c).map WithTop.some).inf := by
  by_cases hc : isEmpty c
  · simp [head?_eq_top c hc, hc]
  · apply le_antisymm
    · have := head?_le c
      aesop
    · have := head?_mem_toMultiset_map c hc
      apply Multiset.inf_le
      aesop

end LinearOrder

end MinHeap
