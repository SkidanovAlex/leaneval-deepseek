import Mathlib
import Submission.Work.RHContract.B.PhiSecondDerivDefs

/-!
# `mellin ((log ·)² • phiIntegrandCut) (1 - s) = mellin psiSubIdLogCut (-s - 1)`

The Landau kernel is `k(t) = (log t + 1) / (t² log² t)`, so on `t > 2`

`t^{-s} (log t)² (ψ t − t) k(t) = t^{-s-2} (ψ t − t) (1 + log t)`.

Since both `phiIntegrandCut` and `psiSubIdLogCut` are supported on `(2, ∞)`, the two Mellin
integrands agree pointwise on `(0, ∞)`; the statement below is the resulting identity of the
Mellin transforms.  The only nontrivial ingredient is the algebraic cancellation
`t² (log t)² k(t) = 1 + log t`.
-/

namespace Work.RHContract.B

/-- The real–complex cancellation behind the identity: for `t > 2`,
`(log t)² · k(t) = (1 + log t) / t²`. -/
lemma sq_log_sq_mul_kW {t : ℝ} (ht : 2 < t) :
    (Real.log t) ^ 2 * kW t = (Real.log t + 1) / t ^ 2 := by
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  rw [kW]
  field_simp

/-- Complex form of `sq_log_sq_mul_kW`: `↑(log t)² · ↑(k t) = (↑(t²))⁻¹ · (1 + ↑log t)`. -/
lemma ofReal_sq_log_mul_kW {t : ℝ} (ht : 2 < t) :
    ((Real.log t ^ 2 : ℝ) : ℂ) * ((kW t : ℝ) : ℂ)
      = (((t ^ 2 : ℝ)) : ℂ)⁻¹ * (1 + (Real.log t : ℂ)) := by
  have hkey := sq_log_sq_mul_kW ht
  have h : ((Real.log t ^ 2 * kW t : ℝ) : ℂ)
      = (((t ^ 2 : ℝ)⁻¹ * (1 + Real.log t) : ℝ) : ℂ) := by
    rw [hkey]; congr 1; rw [div_eq_mul_inv]; ring
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one]
    using h

/-- Splitting off the two extra powers of `t` in the exponent: for `t > 0`,
`(t : ℂ) ^ (-s - 2) = (t : ℂ) ^ (-s) * (↑(t²))⁻¹`. -/
lemma cpow_neg_sub_two (s : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (-s - 2) = (t : ℂ) ^ (-s) * (((t ^ 2 : ℝ)) : ℂ)⁻¹ := by
  have hT : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  rw [show (-s - 2 : ℂ) = -s + (-2) by ring, Complex.cpow_add (-s) (-2) hT]
  congr 1
  rw [Complex.cpow_neg, Complex.cpow_ofNat, ← Complex.ofReal_pow]

theorem mellin_logSq_phiIntegrandCut (s : ℂ) :
    mellin (fun t : ℝ => (Real.log t) ^ 2 • Work.RHContract.B.phiIntegrandCut t) (1 - s)
      = mellin Work.RHContract.B.psiSubIdLogCut (-s - 1) := by
  rw [mellin, mellin]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  by_cases h2 : (2 : ℝ) < t
  · -- main range `t > 2`: the two Mellin integrands coincide by cancellation
    have ht0 : (0 : ℝ) < t := by linarith
    have hpc : phiIntegrandCut t
        = (↑(Chebyshev.psi t) - ↑t) * ↑(kW t) := by
      rw [phiIntegrandCut, Set.indicator_of_mem (Set.mem_Ioi.mpr h2), phiIntegrand]
    -- pointwise identity of the two scalar multiples of the cut functions
    have key : (Real.log t) ^ 2 • phiIntegrandCut t
        = ((((t ^ 2 : ℝ)) : ℂ)⁻¹) • psiSubIdLogCut t := by
      rw [hpc, psiSubIdLogCut_apply_of_gt h2, Complex.real_smul, smul_eq_mul]
      rw [Complex.ofReal_mul (Chebyshev.psi t - t) (1 + Real.log t), Complex.ofReal_sub]
      calc ((Real.log t ^ 2 : ℝ) : ℂ) * ((↑(Chebyshev.psi t) - ↑t) * ↑(kW t))
          = (((Real.log t ^ 2 : ℝ) : ℂ) * ↑(kW t)) * (↑(Chebyshev.psi t) - ↑t) := by ring
        _ = ((((t ^ 2 : ℝ)) : ℂ)⁻¹ * (1 + (Real.log t : ℂ))) * (↑(Chebyshev.psi t) - ↑t) := by
              rw [ofReal_sq_log_mul_kW h2]
        _ = (((t ^ 2 : ℝ)) : ℂ)⁻¹ * ((↑(Chebyshev.psi t) - ↑t) * (1 + (Real.log t : ℂ))) := by
              ring
        _ = (((t ^ 2 : ℝ)) : ℂ)⁻¹ * ((↑(Chebyshev.psi t) - ↑t) * ↑(1 + Real.log t)) := by
              rw [Complex.ofReal_add, Complex.ofReal_one]
    rw [show (1 : ℂ) - s - 1 = -s by ring, show (-s - 1 - 1 : ℂ) = -s - 2 by ring,
      cpow_neg_sub_two s ht0, mul_smul, ← key]
  · -- range `0 < t ≤ 2`: both cut functions vanish
    have h1 : phiIntegrandCut t = 0 := by
      rw [phiIntegrandCut, Set.indicator_of_notMem]
      simpa using h2
    have h1' : psiSubIdLogCut t = 0 := by
      rw [psiSubIdLogCut, Set.indicator_of_notMem]
      simpa using h2
    rw [h1, h1']
    simp

end Work.RHContract.B
