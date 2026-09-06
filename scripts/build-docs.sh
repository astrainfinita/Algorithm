#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# doc-gen4's release process uses matching Lean tags, including patch releases.
# For a nightly/custom toolchain or an exceptional missing tag, set DOC_GEN_REV
# to a compatible revision and check it again when upgrading Lean.
toolchain="$(< lean-toolchain)"
doc_gen_rev="${DOC_GEN_REV:-}"
if [[ -z "$doc_gen_rev" ]]; then
  if [[ "$toolchain" =~ ^leanprover/lean4:(v4\.[0-9]+\.[0-9]+(-rc[0-9]+)?)$ ]]; then
    doc_gen_rev="${BASH_REMATCH[1]}"
  else
    printf 'Set DOC_GEN_REV to a doc-gen4 revision compatible with %s.\n' "$toolchain" >&2
    exit 1
  fi
fi
if [[ ! "$doc_gen_rev" =~ ^[a-zA-Z0-9._/-]+$ ]]; then
  printf 'Invalid doc-gen4 revision: %s\n' "$doc_gen_rev" >&2
  exit 1
fi

printf 'Building documentation with %s and doc-gen4 %s.\n' "$toolchain" "$doc_gen_rev"
mkdir -p .lake/docbuild
cat > .lake/docbuild/lakefile.toml <<EOF
name = "docbuild"
reservoir = false
packagesDir = "../packages"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "$doc_gen_rev"

# Lake gives later dependencies' manifests priority for shared dependencies.
[[require]]
name = "algorithm"
path = "../.."
EOF

# Elan inherits the root lean-toolchain; keep Lake from creating a second one.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d .lake/docbuild update --keep-toolchain
lake -d .lake/docbuild build --keep-toolchain Algorithm:docs
lake exe graph .lake/docbuild/.lake/build/doc/algorithm.html
test -s .lake/docbuild/.lake/build/doc/index.html
