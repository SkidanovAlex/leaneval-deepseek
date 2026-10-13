import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Psi.psiInv_psi
import Submission.Work.WilE9.Psi.psi_psiInv
import Submission.Work.WilE9.Psi.hasDerivAt_psi
import Submission.Work.WilE9.Psi.psig_pos

open Filter

namespace Work.WilE9.Psi

/-- The derivative of the inverse of `psi`, written with the auxiliary `w`-coordinate `psig`.
Note `(psiInv)' y = 1/psi'(psiInv y) = (psig (psiInv y))⁻³`: the *reciprocal* of `psig ^ 3`,
since `psig (psiInv y) = √(1-y²)`.  Together with `psi_sq_add_psig_sq` this makes every `psi`
factor of a transported derivative an algebraic function of `(psiInv y, psig (psiInv y))`. -/
theorem deriv_psiInv (y : ℝ) (hy : |y| < 1) :
    HasDerivAt Work.WilE9.psiInv ((Work.WilE9.psig (Work.WilE9.psiInv y) ^ 3)⁻¹) y := by
  have h1 : 0 < 1 - y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y, hy]
  -- `psiInv` is continuous at `y`: it is the quotient `t / √(1 - t²)`, a nonzero denominator.
  have hcont : ContinuousAt Work.WilE9.psiInv y := by
    unfold Work.WilE9.psiInv
    exact continuousAt_id.div
      (Real.continuous_sqrt.continuousAt.comp
        ((continuous_const.sub (continuous_id.pow 2)).continuousAt))
      (ne_of_gt (Real.sqrt_pos.mpr h1))
  -- the derivative of `psi` at `psiInv y` is `psig (psiInv y) ^ 3`, and it is nonzero.
  have hf : HasDerivAt WilkiesDesign.E.psi (Work.WilE9.psig (Work.WilE9.psiInv y) ^ 3)
      (Work.WilE9.psiInv y) := hasDerivAt_psi (Work.WilE9.psiInv y)
  have hf' : Work.WilE9.psig (Work.WilE9.psiInv y) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ne_of_gt (psig_pos _))
  -- `psi` is a left inverse of `psiInv` near `y`.
  have hfg : ∀ᶠ z in nhds y, WilkiesDesign.E.psi (Work.WilE9.psiInv z) = z := by
    have hy' : y ∈ Set.Ioo (-1 : ℝ) 1 := by simpa using abs_lt.mp hy
    filter_upwards [isOpen_Ioo.mem_nhds hy'] with z hz
    exact psi_psiInv z (abs_lt.mpr hz)
  exact HasDerivAt.of_local_left_inverse hcont hf hf' hfg

end Work.WilE9.Psi
