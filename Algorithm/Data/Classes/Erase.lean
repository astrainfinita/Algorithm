/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

@[expose] public section

class Erase (C : Type _) (ι : Type _) where
  erase : C → ι → C
export Erase (erase)
