import Mathlib
import Submission.Work.Analysis.IonescuWainger.FourierZ
import Submission.Port.Aesm

/-!
# The `ℒ²` seminorm against counting measure is the `ℓ²` norm

For `f ∈ ℓ²(ℤ; ℂ)` (realised as Mathlib's `lp (fun _ : ℤ => ℂ) 2`), the `ℒ²` seminorm of `f`
with respect to counting measure on `ℤ` is the `lp` norm of `f`:

  `eLpNorm (fun x : ℤ => f x) 2 Measure.count = ENNReal.ofReal ‖f‖`.

The proof is a direct computation: `eLpNorm` is the `1/2`-power of the `ℤ`-integral of
`‖f x‖ₑ ^ 2`, the counting integral is a `tsum`, and `ENNReal.ofReal` commutes with both the
`tsum` of nonnegative reals and with real powers of nonnegative bases; finally this is exactly
`lp.norm_eq_tsum_rpow`.
-/

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

theorem eLpNorm_count_eq_lp_norm (f : Work.Analysis.IonescuWainger.L2Z) : MeasureTheory.eLpNorm (fun x : ℤ => f x) 2 MeasureTheory.Measure.count = ENNReal.ofReal ‖f‖ := by
  -- summability of `x ↦ ‖f x‖ ^ 2`, from the defining property of `lp`
  have hsum : Summable (fun x : ℤ => ‖f x‖ ^ (2:ℝ)) := by
    have h := (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp f)
    simpa [ENNReal.toReal_ofNat] using h
  have hnn : ∀ x : ℤ, (0:ℝ) ≤ ‖f x‖ ^ (2:ℝ) := fun x => Real.rpow_nonneg (norm_nonneg _) _
  calc MeasureTheory.eLpNorm (fun x : ℤ => f x) 2 MeasureTheory.Measure.count
      = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) ^ (1/2 : ℝ) := by
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num)]
        norm_num
    _ = (∑' x, ‖f x‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) := by rw [MeasureTheory.lintegral_count]
    _ = (ENNReal.ofReal (∑' x, ‖f x‖ ^ (2:ℝ))) ^ (1/2 : ℝ) := by
        congr 1
        rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum]
        exact tsum_congr (fun x => by
          rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)])
    _ = ENNReal.ofReal ‖f‖ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg hnn) (by norm_num)]
        congr 1
        rw [lp.norm_eq_tsum_rpow (p := 2) (by norm_num)]
        norm_num

end Work.KMTAreas.A4
