/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Set.Defs

import Mathlib.Data.Set.Insert

/-!
# Forests

Rooted forests with preorder and postorder traversals.
-/

@[expose] public section

inductive Forest (α : Type*)
  | nil : Forest α
  | node (a : α) (child sibling : Forest α) : Forest α
deriving Repr

namespace Forest
variable {α : Type*}

@[simp]
def roots : (f : Forest α) → Set α
  | .nil => ∅
  | .node a _ s => insert a s.roots

@[simp]
def support : (f : Forest α) → Set α
  | .nil => ∅
  | .node a c s => insert a (c.support ∪ s.support)

lemma roots_subset_support (f : Forest α) : f.roots ⊆ f.support := by
  induction f with
  | nil => rfl
  | node a c s _ ihs =>
    exact Set.insert_subset_insert (Set.subset_union_of_subset_right ihs _)

@[simp]
def pre : (f : Forest α) → List α
  | .nil => ∅
  | .node a c s => a :: c.pre ++ s.pre

@[simp]
def post : (f : Forest α) → List α
  | .nil => ∅
  | .node a c s => c.post ++ a :: s.post

@[simp]
protected def append (f g : Forest α) : Forest α :=
  match f with
  | .nil  => g
  | .node a c s => .node a c (s.append g)

instance : Append (Forest α) where
  append := Forest.append

end Forest
