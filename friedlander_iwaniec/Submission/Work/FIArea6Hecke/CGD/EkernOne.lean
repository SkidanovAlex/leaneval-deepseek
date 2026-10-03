import Mathlib
import Submission.Work.FIArea6Hecke.ConductorGaussSumDefs

namespace Work.FIArea6Hecke.CGD

/-- The additive-character kernel `ekern M w s = e^{2πi·gdot s w/gnorm M}` equals `1` exactly when
`gnorm M` divides the integer `gdot s w`, i.e. when the exponent is an integral multiple of `2πi`
(after cancellation of the common factor `2πi`).  The hypothesis `M ≠ 0` guarantees
`gnorm M ≠ 0`, so that the division by `gnorm M` is legitimate. -/
theorem EkernOne (M : GaussianInt) (hM : M ≠ 0) (w s : GaussianInt) :
    Work.FIArea6Hecke.R.ekern M w s = 1 ↔
      (Work.FIPlan.gnorm M : ℤ) ∣ Work.FIArea6Hecke.R.gdot s w := by
  have hNn : Work.FIPlan.gnorm M ≠ 0 := by
    simp only [Work.FIPlan.gnorm, ne_eq, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero]
    exact hM
  have hNr : ((Work.FIPlan.gnorm M : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hNn
  constructor
  · -- `ekern M w s = 1` forces the exponent into `2πi·ℤ`
    intro h
    rw [Work.FIArea6Hecke.R.ekern] at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    -- cancel the common factor `I` and read off the real identity
    have key : ((2 * Real.pi * (Work.FIArea6Hecke.R.gdot s w : ℝ)
        / (Work.FIPlan.gnorm M : ℝ) : ℝ) : ℂ) = ((n : ℝ) * (2 * Real.pi) : ℝ) := by
      have hI : (↑(2 * Real.pi * ↑(R.gdot s w) / ↑(Work.FIPlan.gnorm M)) : ℂ) * Complex.I
          = (↑((n : ℝ) * (2 * Real.pi)) : ℂ) * Complex.I := by
        rw [show (↑((n : ℝ) * (2 * Real.pi)) : ℂ) * Complex.I
            = (↑n : ℂ) * (2 * ↑Real.pi * Complex.I) by push_cast; ring]
        exact hn
      exact mul_right_cancel₀ Complex.I_ne_zero hI
    have hr : 2 * Real.pi * (R.gdot s w : ℝ) / (Work.FIPlan.gnorm M : ℝ)
        = (n : ℝ) * (2 * Real.pi) := Complex.ofReal_injective key
    have hG : (R.gdot s w : ℝ) = (n : ℝ) * (Work.FIPlan.gnorm M : ℝ) := by
      field_simp at hr
      nlinarith [hr, Real.pi_pos]
    have hGi : R.gdot s w = n * (Work.FIPlan.gnorm M : ℤ) := by
      have h2 : ((R.gdot s w : ℤ) : ℝ) = ((n * (Work.FIPlan.gnorm M : ℤ) : ℤ) : ℝ) := by
        push_cast
        exact hG
      exact_mod_cast h2
    exact ⟨n, by rw [hGi]; ring⟩
  · -- divisibility makes the exponent an integral multiple of `2πi`
    intro h
    obtain ⟨k, hk⟩ := h
    rw [Work.FIArea6Hecke.R.ekern, Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    have hGr : (2 * Real.pi * (R.gdot s w : ℝ) / (Work.FIPlan.gnorm M : ℝ))
        = (k : ℝ) * (2 * Real.pi) := by
      rw [hk]; push_cast
      field_simp
    rw [show (↑k : ℂ) * (2 * ↑Real.pi * Complex.I)
        = (↑((k : ℝ) * (2 * Real.pi)) : ℂ) * Complex.I by push_cast; ring]
    exact congrArg (fun t : ℝ => (t : ℂ) * Complex.I) hGr

end Work.FIArea6Hecke.CGD
