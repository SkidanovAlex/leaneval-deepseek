import ChallengeDeps

open LinearSubspaces
open ENNReal Real Module exteriorPower InnerProductGeometry
open scoped LinearAlgebra.Projectivization

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

namespace Submission.Helpers

/-- A sufficient criterion for a lower bound on `diophantineExponent`:
it is enough to know the lower bound for every real `β` that actually appears
in the defining set. -/
lemma diophantineExponent_ge_of_forall_mem (k : ℕ) (x : Submodule ℝ ℝᵈ) (a : ℝ≥0∞)
    (h : ∀ β : ℝ, β > 0 → (∃ c > 0, ∀ v : Submodule ℝ ℝᵈ, finrank ℝ v = k →
      (hv : IsRational v) → distSubspaces v x ≥ c * height v hv ^ (-β)) → a ≤ ENNReal.ofReal β) :
    a ≤ diophantineExponent k x := by
  unfold diophantineExponent
  apply le_sInf
  rintro b ⟨β, hβ, rfl⟩
  exact h β hβ.1 hβ.2

end Submission.Helpers
