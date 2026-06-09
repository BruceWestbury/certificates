import Mathlib

namespace Certificates

open scoped BigOperators

/-- Finite-support linear combinations. -/
abbrev LC (R : Type _) (α : Type _) [Semiring R] :=
  α →₀ R

namespace LC

variable {R : Type _} {α : Type _}
variable [Semiring R]

/-- A single basis element. -/
def single (a : α) (r : R) : LC R α :=
  Finsupp.single a r

@[simp]
theorem single_apply_same [DecidableEq α]
    (a : α) (r : R) :
    single a r a = r := by
  simp [single]

@[simp]
theorem single_apply_ne [DecidableEq α]
    {a b : α} (h : b ≠ a) (r : R) :
    single a r b = 0 := by
  simp [single, h]

def singleton (a : α) (r : R) : LC R α :=
  Finsupp.single a r

end LC

end Certificates
