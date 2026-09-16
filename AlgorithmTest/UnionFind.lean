module

import Algorithm.Data.UnionFind

abbrev UF := UnionFind (Fin 10) (Vector (Fin 10) 10) (Vector Nat 10)

abbrev UFImpl := UnionFindImpl.UnionFindWF (Fin 10) (Vector (Fin 10) 10) (Vector Nat 10)

def initialUF : UFImpl := ⟨default, UnionFindImpl.UnionFind.default_wf⟩

/--
info: 1
4
4
4
1
-/
#guard_msgs in #eval show IO Unit from do
  let initial : UF := default
  IO.println (initial.find 1).fst
  let uf := ((initial.union 1 2).union 3 4).union 2 4
  let result := uf.find 1
  IO.println result.fst
  IO.println (result.snd.find 1).fst
  IO.println (result.snd.size result.fst (uf.find_isRoot 1))
  IO.println (initial.find 1).fst

-- The result/state convention can be used directly with `modifyGet`.
def findInState (i : Fin 10) : StateM UF (Fin 10) :=
  modifyGet (fun uf ↦ uf.find i)

example (uf : UF) (i : Fin 10) : (findInState i).run uf = uf.find i := rfl

example (x : UFImpl) (i : Fin 10) :
    (⟦(x.find i).snd⟧ : UF) = ⟦x⟧ :=
  Quotient.sound (x.find_snd_root i)

-- Inspect representatives in this runtime test to check that compression is retained.
/--
info: 2
4
4
2
-/
#guard_msgs in #eval show IO Unit from do
  let initial : UF := default
  let uf := ((initial.union 1 2).union 3 4).union 2 4
  IO.println ((Quot.unquot uf).val.parent[(1 : Fin 10)])
  let (r, compressed) := uf.find 1
  IO.println r
  IO.println ((Quot.unquot compressed).val.parent[(1 : Fin 10)])
  IO.println ((Quot.unquot uf).val.parent[(1 : Fin 10)])

/--
info: 1
2
-/
#guard_msgs in #eval show IO Unit from do
  let mut uf := initialUF
  IO.println (uf.find 1).fst
  uf := uf.union 1 2
  uf := uf.union 3 4
  uf := uf.union 2 4
  IO.println (uf.val.parent[(1 : Fin 10)])

/--
info: 1
4
4
2
4
1
-/
#guard_msgs in #eval show IO Unit from do
  let mut uf := initialUF
  IO.println (uf.find 1).fst
  uf := uf.union 1 2
  uf := uf.union 3 4
  uf := uf.union 2 4
  let (r, compressed) := uf.find 1
  IO.println r
  IO.println (compressed.val.parent[(1 : Fin 10)])
  -- Path compression affects only the returned forest.
  IO.println (uf.val.parent[(1 : Fin 10)])
  IO.println (compressed.size (compressed.root 1) (.root _ _))
  -- Unions also preserve the original forest.
  IO.println (initialUF.find 1).fst

-- Merging already connected nodes must retain compression from both searches.
/--
info: 8
8
2
6
8
-/
#guard_msgs in #eval show IO Unit from do
  let uf := ((((((initialUF.union 1 2).union 3 4).union 2 4).union 5 6).union 7 8).union 6 8).union 4 8
  let compressed := uf.union 1 5
  IO.println (compressed.val.parent[(1 : Fin 10)])
  IO.println (compressed.val.parent[(5 : Fin 10)])
  IO.println (uf.val.parent[(1 : Fin 10)])
  IO.println (uf.val.parent[(5 : Fin 10)])
  IO.println (compressed.size (compressed.root 1) (.root _ _))
