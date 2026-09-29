import Mathlib
import Submission.Work.Transform.Defs

namespace Work.Transform

/-- `‖ζ^c‖ = 1` for `ζ = e^{πi/r}` (paper Prop 3.5): the scaling factors of `T̃` and of `T̃⁻¹`
are unimodular, so these maps are isometries for the sup norm. -/
lemma norm_zeta (r c : ℕ) : ‖zeta r c‖ = 1 := by
  rw [zeta, Complex.norm_exp]
  have h : (Real.pi * Complex.I * (c : ℂ) / (r : ℂ)).re = 0 := by
    simp [Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im]
  rw [h, Real.exp_zero]

/-- `T̃⁻¹` (the flattening times the diagonal scaling by `ζ^{-c}`) does not increase the sup norm. -/
theorem psiFlatL_norm (r : ℕ) (ts' : List ℕ) (v : Fin ts'.prod → Fin r → ℂ) :
    ‖Work.Transform.psiFlatL r ts' v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 (fun i => ?_)
  have hz : ‖(zeta r ((i : ℕ) % r))⁻¹‖ = 1 := by
    rw [norm_inv, norm_zeta, inv_one]
  rw [psiFlatL, norm_mul, hz, one_mul]
  exact le_trans (norm_le_pi_norm _ _) (norm_le_pi_norm v _)

end Work.Transform
