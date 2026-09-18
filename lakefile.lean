import Lake

open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.35.0-rc1"

abbrev algorithmOnlyLinters : Array LeanOption := #[
  ⟨`linter.mathlibStandardSet, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
  ⟨`linter.unicodeLinter, false⟩, -- Allow multilingual text.
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
  -- Run the builtin linting steps in addition to the `lintDriver` set above.
  builtinLint := true
  -- A version of Algorithm only supports the toolchain it is built with.
  fixedToolchain := true
  -- Allow oleans built on Linux CI to be used across platforms.
  platformIndependent := true
  -- Algorithm currently expects artifacts to be in the build directory.
  restoreAllArtifacts := true

@[default_target]
lean_lib Algorithm where
  leanOptions := algorithmLeanOptions

lean_lib AlgorithmTest where
  globs := #[`AlgorithmTest.+]
  leanOptions := #[⟨`pp.mvars.anonymous, false⟩] -- Test stability: print `?m.37` as `?_`.
