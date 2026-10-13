import Mathlib
import Submission.Work.WilE9.All

namespace Work.WilE9.Sharp

/-- Recover the auxiliary `w`-coordinate from the circle relation `y² + w² = 1` with `w > 0`:
`w = psig (psiInv y)`.  This is exactly the tie `w = √(1 - (ψ x)²)` used by the ψ-transport:
by `psi_psig_algebra`, `psig (psiInv y) = √(1 - psi (psiInv y)²) = √(1 - y²)` for `|y| < 1`,
and `√(1 - y²) = w` because `1 - y² = w²` with `w > 0`. -/
theorem psig_psiInv_of_sq {y w : ℝ} (h : y ^ 2 + w ^ 2 = 1) (hw : 0 < w) :
    w = Work.WilE9.psig (Work.WilE9.psiInv y) := by
  -- `1 - y² = w² > 0`, hence `√(1 - y²) = w`.
  have hw2 : 1 - y ^ 2 = w ^ 2 := by linarith
  have hw_eq : Real.sqrt (1 - y ^ 2) = w := by
    rw [hw2, Real.sqrt_sq_eq_abs, abs_of_pos hw]
  -- `|y| < 1`, so `psi (psiInv y) = y`.
  have hy_abs : |y| < 1 := (sq_lt_one_iff_abs_lt_one y).mp (by nlinarith [sq_pos_of_pos hw])
  have hpsi : WilkiesDesign.E.psi (Work.WilE9.psiInv y) = y :=
    Work.WilE9.Psi.psi_psiInv y hy_abs
  -- `psig (psiInv y) = √(1 - psi (psiInv y)²) = √(1 - y²) = w`.
  have halg := (Work.WilE9.Psi.psi_psig_algebra (Work.WilE9.psiInv y)).2.2
  rw [halg, hpsi, hw_eq]

end Work.WilE9.Sharp
