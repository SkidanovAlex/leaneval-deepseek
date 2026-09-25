import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs

namespace Work.BourgainPlan.Maximal

set_option linter.unusedVariables false

/-- The trivial (`L¹`-of-the-modulus) bound for the bump transform: the phase factor has modulus
one, so `‖mstHat η t‖ ≤ M · |1/2 - (−1/2)| = M` whenever `‖η‖ ≤ M` pointwise.  No measurability,
integrability or support hypothesis on `η` is needed: if `η` is not integrable the integral is `0`
by the Bochner convention, and the bound holds anyway. -/
theorem mstHat_bound {η : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) :
    ∀ t : ℝ, ‖mstHat η t‖ ≤ M := by
  intro t
  rw [mstHat_apply]
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1/2)) (b := 1/2) (C := M)
    (f := fun u => η u * Complex.exp ((((-(2 * Real.pi * t * u)) : ℝ) : ℂ) * Complex.I))
    (fun u _ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hηbd u)
  rwa [show |(1/2 : ℝ) - (-(1/2))| = 1 by norm_num, mul_one] at h2

end Work.BourgainPlan.Maximal
