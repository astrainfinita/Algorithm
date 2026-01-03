/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Setoid.Basic
import Mutable.Mutable

/-!
# MutableQuotient

-/

universe u v w

namespace Quotient

def liftOnMkEq {α : Sort u} {β : Sort v} {s : Setoid α} (q : Quotient s)
    (f : ∀ a : α, ⟦a⟧ = q → β) (hf : ∀ a ha b hb, f a ha = f b hb) : β :=
  Equiv.subtypeQuotientEquivQuotientSubtype (fun a ↦ ⟦a⟧ = q) (· = q) (fun _ ↦ Iff.rfl)
    (fun _ _ ↦ Iff.rfl) ⟨q, rfl⟩ |>.lift
    (fun ⟨a, ha⟩ ↦ f a ha) (fun ⟨a, ha⟩ ⟨b, hb⟩ _ ↦ hf a ha b hb)

end Quotient

variable {M : Type u} {α : Type v} {β : Type w} {m : α → M}

def MutableQuotient (α : Type v) (m : α → M) :=
  Mutable (Quotient (Setoid.ker m))

namespace MutableQuotient

@[inline]
def mk (m : α → M) (a : α) : MutableQuotient α m := Mutable.mk ⟦a⟧

@[inline]
def get (x : MutableQuotient α m) (f : α → β) (hf : ∀ a₁ a₂, m a₁ = m a₂ → f a₁ = f a₂) : β :=
  (Mutable.get x).lift f fun _ _ h ↦ hf _ _ (by exact h)

@[simp]
lemma mk_get (m : α → M) (a : α) (f : α → β) (hf : ∀ a₁ a₂, m a₁ = m a₂ → f a₁ = f a₂) :
    (mk m a).get f hf = f a :=
  rfl

@[elab_as_elim, induction_eliminator]
lemma ind {motive : MutableQuotient α m → Prop} (h : ∀ (a : α), motive (mk m a)) (x) : motive x :=
  Quotient.ind (motive := fun x ↦ motive (Mutable.mk x)) h (Mutable.get x)

@[inline]
def liftOnMkEq (x : MutableQuotient α m) (f : ∀ a : α, m a = x.get m (fun _ _ ↦ id) → β)
    (hf : ∀ a₁ ha₁ a₂ ha₂, f a₁ ha₁ = f a₂ ha₂) : β :=
  (Mutable.get x).liftOnMkEq (fun a ha ↦ f a (congr_arg (Quotient.lift m _) ha))
    (fun _ _ _ _ ↦ hf _ _ _ _)

@[inline]
def map (x : MutableQuotient α m) (f : α → α) (hf : ∀ a₁ a₂, m a₁ = m a₂ → m (f a₁) = m (f a₂)) :
    MutableQuotient α m :=
  get x (fun a ↦ mk m (f a)) (Mutable.ext <| Quotient.sound <| hf · · ·)

-- def getModify (x : MutableQuotient α m) (f : α → β) (hf : ∀ a₁ a₂, m a₁ = m a₂ → f a₁ = f a₂)
--     (r : α → α) (hr : ∀ a, m (r a) = m a) : β :=
--   (Mutable.getModify x (Quotient.map' r (fun a₁ a₂ h ↦ (hr a₁).trans h |>.trans (hr a₂).symm))
--     (Quotient.ind fun a ↦ Quotient.sound (hr a))).lift f fun _ _ h ↦ hf _ _ (by exact h)

@[inline]
def liftModify (x : MutableQuotient α m) (fr : α → β × α)
    (hf : ∀ a₁ a₂, m a₁ = m a₂ → (fr a₁).fst = (fr a₂).fst) (hr : ∀ a, m (fr a).snd = m a) : β :=
  Mutable.getModify x (Quotient.lift (let ⟨x, y⟩ := fr ·; (x, ⟦y⟧)) (fun a₁ a₂ h ↦
      Prod.ext (hf a₁ a₂ h) <| Quotient.sound <| (hr a₁).trans <| h.trans (hr a₂).symm))
    (Quotient.ind fun a ↦ Quotient.sound (hr a))

@[simp]
lemma mk_liftModify (m : α → M) (a : α) (fr : α → β × α)
    (hf : ∀ a₁ a₂, m a₁ = m a₂ → (fr a₁).fst = (fr a₂).fst) (hr : ∀ a, m (fr a).snd = m a) :
    (mk m a).liftModify fr hf hr = (fr a).fst :=
  rfl

end MutableQuotient
