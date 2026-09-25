import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# The derivative of the kernel `kW`

For `t > 1`,

`k(t) = (log t + 1)/(t² log²t)`,  `k'(t) = -(2 log²t + 3 log t + 2)/(t³ log³t)`.

Indeed, writing `L = log t` and using `d/dt log t = 1/t`,

`(d/dt) (L+1)/(t²L²) = [L²/t - (L+1)·(2tL² + 2tL)]/(t⁴L⁴)
                    = (L - 2(L+1)²)/(t³L³) = -(2L² + 3L + 2)/(t³L³)`.
-/

namespace Work.RHContract.A

/-- The derivative computation, stated for the explicit function defining `kW`. -/
private lemma deriv_kW_aux {t : ℝ} (ht : 1 < t) :
    deriv (fun s : ℝ => (Real.log s + 1) / (s ^ 2 * (Real.log s) ^ 2)) t
      = -(2 * (Real.log t) ^ 2 + 3 * Real.log t + 2) / (t ^ 3 * (Real.log t) ^ 3) := by
  have ht0 : t ≠ 0 := by linarith
  -- numerator `log + 1`, derivative `1/t`
  have hnum : HasDerivAt (fun s : ℝ => Real.log s + 1) t⁻¹ t :=
    (Real.hasDerivAt_log ht0).add_const 1
  -- `s^2`, derivative `2t`
  have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hp2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * Real.log t) (Real.log t) := by
    simpa using hasDerivAt_pow 2 (Real.log t)
  -- `log²`, derivative `2 log t / t`
  have hl : HasDerivAt (fun s : ℝ => (Real.log s) ^ 2) (2 * Real.log t * t⁻¹) t :=
    hp2.comp t (Real.hasDerivAt_log ht0)
  -- denominator `t² log²t`
  have hden : HasDerivAt (fun s : ℝ => s ^ 2 * (Real.log s) ^ 2)
      (2 * t * (Real.log t) ^ 2 + t ^ 2 * (2 * Real.log t * t⁻¹)) t := hp.mul hl
  have hden_ne : t ^ 2 * (Real.log t) ^ 2 ≠ 0 := by
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
    exact ne_of_gt (mul_pos (pow_pos (by linarith) 2) (sq_pos_of_ne_zero hlog))
  have h : HasDerivAt (fun s : ℝ => (Real.log s + 1) / (s ^ 2 * (Real.log s) ^ 2))
      ((t⁻¹ * (t ^ 2 * (Real.log t) ^ 2) -
          (Real.log t + 1) * (2 * t * (Real.log t) ^ 2 + t ^ 2 * (2 * Real.log t * t⁻¹))) /
        (t ^ 2 * (Real.log t) ^ 2) ^ 2) t := hnum.div hden hden_ne
  rw [h.deriv]
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  field_simp
  ring

theorem deriv_kW_eq {t : ℝ} (ht : 1 < t) :
    deriv Work.RHContract.kW t
      = -(2 * (Real.log t) ^ 2 + 3 * Real.log t + 2) / (t ^ 3 * (Real.log t) ^ 3) := by
  unfold Work.RHContract.kW
  exact deriv_kW_aux ht

end Work.RHContract.A
