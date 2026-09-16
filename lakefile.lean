import Lake

open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.27.0-rc1"

abbrev algorithmOnlyLinters : Array LeanOption := #[
  ⟨`linter.mathlibStandardSet, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
]

abbrev algorithmLeanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ] ++ -- options that are used in `lake build`
    algorithmOnlyLinters.map fun s ↦ { s with name := `weak ++ s.name }

package algorithm where
  testDriver := "AlgorithmTest"
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["Algorithm"]

@[default_target]
lean_lib Algorithm where
  leanOptions := algorithmLeanOptions

lean_lib AlgorithmTest where
  globs := #[.submodules `AlgorithmTest]
