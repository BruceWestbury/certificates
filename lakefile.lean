import Lake
open Lake DSL

package «certificates» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

lean_lib «Certificates» where

lean_exe «certificates» where
  root := `Main

lean_exe «polynomial_tests» where
  root := `Certificates.PolynomialTests

lean_exe cert_check where
  root := `Certificates.CertCheck
