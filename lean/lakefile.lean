import Lake
open System Lake DSL

package OAIDFT where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target]
lean_lib OAI where
  globs := #[.submodules `OAI.Computability.FourierTransform, .submodules `OAI.Computability.FourierCircuit]

lean_lib ComparatorChallenges where
