import Lake
open Lake DSL

package «proof-library» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.6.1"

@[default_target]
lean_lib «ProofLibrary» {
  -- add any library configuration options here
}
