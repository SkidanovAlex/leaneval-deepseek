import Submission.Work.CLift.defs

namespace Work.CLift

open Submission.CDTPlan Metric
open scoped BigOperators

noncomputable section

/-- The lift `Φ` never takes the value `1` on the disc: `Φ z = 1` would force
`Φ (-z) = phiC (z²)` and then `1 + Φ (-z) = Φ (-z)`. -/
theorem Phi_ne_one (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) ∧ Φ z * Φ (-z) = phiC (z ^ 2)) :
    ∀ z ∈ ball (0 : ℂ) 1, Φ z ≠ 1 := by
  intro z hz h
  have h1 := (hΦ z hz).1
  have h2 := (hΦ z hz).2
  rw [h] at h1 h2
  rw [one_mul] at h2
  rw [h2] at h1
  have : (1 : ℂ) = 0 := by linear_combination h1
  exact one_ne_zero this

/-- Feeding `Φ z` and `Φ (-z)` into `x² - yx + y`: if `Φ z ≠ 1` then `phiC (z²) = (Φ z)²/(Φ z - 1)`. -/
theorem phiC_sq_eq (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) ∧ Φ z * Φ (-z) = phiC (z ^ 2))
    (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (h1 : Φ z ≠ 1) :
    phiC (z ^ 2) = (Φ z) ^ 2 / (Φ z - 1) := by
  have hA := (hΦ z hz).1
  have hB := (hΦ z hz).2
  have hsub : Φ (-z) = phiC (z ^ 2) - Φ z := by linear_combination hA
  rw [hsub] at hB
  have hB' : Φ z * phiC (z ^ 2) - Φ z ^ 2 = phiC (z ^ 2) := by linear_combination hB
  rw [eq_div_iff (sub_ne_zero.mpr h1)]
  linear_combination hB'

end
end Work.CLift
