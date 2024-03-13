import Lake
open Lake DSL

package «lean4-showcase» {
  moreServerOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Limits {
  -- add any library configuration options here
}
