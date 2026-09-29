import Mathlib
import Submission.Work.DFT.dftDefs

/-!
# The normalised multidimensional DFT is a contraction for the sup norm

For positive `ts` (all `tᵢ > 0`) and any sign, the normalised multidimensional DFT
`HvdH.dftMulti ts sgn` has operator norm `≤ 1` with respect to the sup norm
`‖u‖ = sup_k ‖u k‖` on `Fin ts.prod → ℂ`:

  `(F u)_j = (1/T) Σ_k e^{sgn·2πi·Σ jᵢkᵢ/tᵢ} u_k`,  `T = ∏ tᵢ`,

each exponential factor has modulus `1`, so `‖(F u)_j‖ ≤ (1/T)·T·‖u‖ = ‖u‖`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.DFT

/-- The exponential factor `exp(sgn·2πi·Σᵢ jᵢkᵢ/tᵢ)` of the multidimensional DFT has modulus `1`. -/
lemma norm_phaseExp (ts : List ℕ) (sgn : ℤ) (j k : ℕ) :
    ‖Complex.exp ((sgn : ℂ) * 2 * (Real.pi : ℂ) * Complex.I *
      ((HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts k) : ℝ) : ℂ))‖ = 1 := by
  rw [show Complex.exp ((sgn : ℂ) * 2 * (Real.pi : ℂ) * Complex.I *
        ((HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts k) : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((((sgn : ℝ) * 2 * Real.pi *
        HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts k)) : ℝ) : ℂ)) from by
        congr 1
        push_cast
        ring_nf,
    Complex.norm_exp_I_mul_ofReal]

theorem dftNorm (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (sgn : ℤ) (u : Fin ts.prod → ℂ) :
    ‖HvdH.dftMulti ts sgn u‖ ≤ ‖u‖ := by
  have hTpos : 0 < ts.prod := List.prod_pos hpos
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 (fun j => ?_)
  rw [HvdH.dftMulti]
  have hine : ‖(1 / (ts.prod : ℂ))‖ = (ts.prod : ℝ)⁻¹ := by
    rw [one_div, norm_inv, Complex.norm_natCast]
  have hS : ‖∑ k : Fin ts.prod,
      Complex.exp ((sgn : ℂ) * 2 * (Real.pi : ℂ) * Complex.I *
        ((HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts k) : ℝ) : ℂ)) * u k‖
      ≤ (ts.prod : ℝ) * ‖u‖ := by
    calc _ ≤ ∑ k : Fin ts.prod, ‖Complex.exp ((sgn : ℂ) * 2 * (Real.pi : ℂ) * Complex.I *
        ((HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts k) : ℝ) : ℂ)) * u k‖ := norm_sum_le _ _
      _ = ∑ k : Fin ts.prod, ‖u k‖ := by
            apply Finset.sum_congr rfl; intro k _
            rw [norm_mul, norm_phaseExp, one_mul]
      _ ≤ ∑ _k : Fin ts.prod, ‖u‖ := by
            apply Finset.sum_le_sum; intro k _
            exact norm_le_pi_norm u k
      _ = (ts.prod : ℝ) * ‖u‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ‖(1 / (ts.prod : ℂ)) * (∑ k : Fin ts.prod,
        Complex.exp ((sgn : ℂ) * 2 * (Real.pi : ℂ) * Complex.I *
          ((HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts k) : ℝ) : ℂ)) * u k)‖
      = ‖(1 / (ts.prod : ℂ))‖ * ‖∑ k : Fin ts.prod,
        Complex.exp ((sgn : ℂ) * 2 * (Real.pi : ℂ) * Complex.I *
          ((HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts k) : ℝ) : ℂ)) * u k‖ := norm_mul _ _
    _ = (ts.prod : ℝ)⁻¹ * ‖∑ k : Fin ts.prod,
        Complex.exp ((sgn : ℂ) * 2 * (Real.pi : ℂ) * Complex.I *
          ((HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts k) : ℝ) : ℂ)) * u k‖ := by rw [hine]
    _ ≤ (ts.prod : ℝ)⁻¹ * ((ts.prod : ℝ) * ‖u‖) := by
          apply mul_le_mul_of_nonneg_left hS; positivity
    _ = ‖u‖ := by
          have hne : (ts.prod : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hTpos)
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Work.DFT
