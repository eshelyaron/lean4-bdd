import Lake
open Lake DSL

package "bdd" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"
require "leanprover-community" / "batteries"

@[default_target]
lean_lib «Bdd» where
  -- add any library configuration options here

lean_exe SatSolver
