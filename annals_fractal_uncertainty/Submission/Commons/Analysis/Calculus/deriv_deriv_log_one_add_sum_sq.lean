import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

/-- The derivative of a real quadratic polynomial `s ↦ a + b*s + c*s^2`. -/
lemma hasDerivAt_quadratic (a b c t : ℝ) :
    HasDerivAt (fun s : ℝ => a + b * s + c * s ^ 2) (b + 2 * c * t) t := by
  have h : HasDerivAt (fun s : ℝ => a + b * s + c * s ^ 2)
      (0 + b * 1 + c * (2 * t ^ (2 - 1) * 1)) t := by
    refine ((hasDerivAt_const (x := t) (c := a)).add ?_).add ?_
    · simpa using (hasDerivAt_id' t).const_mul b
    · simpa using ((hasDerivAt_id' t).pow 2).const_mul c
  convert h using 1
  ring

set_option maxHeartbeats 1000000 in
theorem deriv_deriv_log_one_add_sum_sq {d : ℕ} (z w : Fin d → ℂ) :
    deriv (deriv (fun t : ℝ => Real.log (1 + ∑ j, ‖z j + (t : ℂ) * w j‖ ^ 2))) 0
      = (2 * (∑ j, ‖w j‖ ^ 2) * (1 + ∑ j, ‖z j‖ ^ 2)
          - (2 * (∑ j, (z j * star (w j)).re)) ^ 2)
        / (1 + ∑ j, ‖z j‖ ^ 2) ^ 2 := by
  -- Expand the one-dimensional restriction of the squared norm as a quadratic in `t`.
  have hterm : ∀ j (t : ℝ), ‖z j + (t : ℂ) * w j‖ ^ 2
      = ‖z j‖ ^ 2 + 2 * t * (z j * star (w j)).re + t ^ 2 * ‖w j‖ ^ 2 := by
    intro j t
    rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul]
    rw [Complex.normSq_eq_norm_sq (z j), Complex.normSq_eq_norm_sq (w j)]
    simp only [Complex.normSq_ofReal]
    simp only [map_mul, Complex.conj_ofReal, Complex.star_def]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have hsum : ∀ t : ℝ, ∑ j, ‖z j + (t : ℂ) * w j‖ ^ 2
      = (∑ j, ‖z j‖ ^ 2) + 2 * t * (∑ j, (z j * star (w j)).re)
        + t ^ 2 * (∑ j, ‖w j‖ ^ 2) := by
    intro t
    rw [Finset.sum_congr rfl (fun j _ => hterm j t)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hqpos : ∀ t : ℝ, 0 < 1 + (∑ j, ‖z j + (t : ℂ) * w j‖ ^ 2) := by
    intro t
    positivity
  -- The quadratic is strictly positive (it is `1 + ∑ ‖z_j + t w_j‖²`), hence nonzero.
  have hqne : ∀ t : ℝ, 1 + (∑ j, ‖z j‖ ^ 2) + 2 * (∑ j, (z j * star (w j)).re) * t
      + (∑ j, ‖w j‖ ^ 2) * t ^ 2 ≠ 0 := by
    intro t
    have hp := hqpos t
    rw [hsum t] at hp
    intro hc
    linarith
  have hF : (fun t : ℝ => Real.log (1 + ∑ j, ‖z j + (t : ℂ) * w j‖ ^ 2))
      = fun t : ℝ => Real.log (1 + (∑ j, ‖z j‖ ^ 2)
          + 2 * (∑ j, (z j * star (w j)).re) * t + (∑ j, ‖w j‖ ^ 2) * t ^ 2) := by
    funext t
    rw [hsum t]
    congr 1
    ring
  have hderiv_eq : deriv (fun t : ℝ => Real.log (1 + (∑ j, ‖z j‖ ^ 2)
          + 2 * (∑ j, (z j * star (w j)).re) * t + (∑ j, ‖w j‖ ^ 2) * t ^ 2))
      = fun t : ℝ => (2 * (∑ j, (z j * star (w j)).re) + 2 * (∑ j, ‖w j‖ ^ 2) * t)
          / (1 + (∑ j, ‖z j‖ ^ 2) + 2 * (∑ j, (z j * star (w j)).re) * t
              + (∑ j, ‖w j‖ ^ 2) * t ^ 2) := by
    apply deriv_eq
    intro t
    exact (hasDerivAt_quadratic (1 + ∑ j, ‖z j‖ ^ 2) (2 * (∑ j, (z j * star (w j)).re))
      (∑ j, ‖w j‖ ^ 2) t).log (hqne t)
  rw [hF, hderiv_eq]
  -- Differentiate the logarithmic derivative of the quadratic at `0` by the quotient rule.
  have h2 : HasDerivAt (fun t : ℝ =>
        (2 * (∑ j, (z j * star (w j)).re) + 2 * (∑ j, ‖w j‖ ^ 2) * t)
          / (1 + (∑ j, ‖z j‖ ^ 2) + 2 * (∑ j, (z j * star (w j)).re) * t
              + (∑ j, ‖w j‖ ^ 2) * t ^ 2))
      (((2 * (∑ j, ‖w j‖ ^ 2)) * (1 + (∑ j, ‖z j‖ ^ 2)
            + 2 * (∑ j, (z j * star (w j)).re) * 0 + (∑ j, ‖w j‖ ^ 2) * 0 ^ 2)
          - (2 * (∑ j, (z j * star (w j)).re) + 2 * (∑ j, ‖w j‖ ^ 2) * 0)
            * (2 * (∑ j, (z j * star (w j)).re)))
        / (1 + (∑ j, ‖z j‖ ^ 2) + 2 * (∑ j, (z j * star (w j)).re) * 0
            + (∑ j, ‖w j‖ ^ 2) * 0 ^ 2) ^ 2) 0 := by
    have hnum : HasDerivAt (fun t : ℝ => 2 * (∑ j, (z j * star (w j)).re)
        + 2 * (∑ j, ‖w j‖ ^ 2) * t) (2 * (∑ j, ‖w j‖ ^ 2)) 0 := by
      simpa using hasDerivAt_quadratic (2 * (∑ j, (z j * star (w j)).re))
        (2 * (∑ j, ‖w j‖ ^ 2)) 0 0
    have hden : HasDerivAt (fun t : ℝ => 1 + (∑ j, ‖z j‖ ^ 2)
        + 2 * (∑ j, (z j * star (w j)).re) * t + (∑ j, ‖w j‖ ^ 2) * t ^ 2)
        (2 * (∑ j, (z j * star (w j)).re)) 0 := by
      simpa using hasDerivAt_quadratic (1 + (∑ j, ‖z j‖ ^ 2))
        (2 * (∑ j, (z j * star (w j)).re)) (∑ j, ‖w j‖ ^ 2) 0
    exact hnum.fun_div hden (hqne 0)
  rw [h2.deriv]
  ring_nf

end Commons.Analysis.Calculus