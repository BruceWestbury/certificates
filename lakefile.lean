import Lake
open Lake DSL

package «certificates» where
  name := "certificates"

-- Mathlib provides Fintype, Finset, DecidableEq, and related infrastructure.
-- Run `lake update` once after cloning to download the correct Mathlib version.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «Certificates» where
  roots := #[`Main, `Graphs]
