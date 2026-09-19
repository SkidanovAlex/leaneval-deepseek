import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Commons.Analysis.Integral.abs_integral_Ioi_le_thin

open MeasureTheory

namespace Commons.Analysis.Integral

/-- If two real functions agree up to `ε` and are both bounded by `B` on a finite-measure
set `s`, then their squared integrals over `s` differ by at most `2 * B * ε * volume s`. -/
theorem abs_integral_sq_sub_sq_le {α : Type*} [MeasureTheory.MeasureSpace α]
    {s : Set α} (hs : MeasurableSet s) (hvol : MeasureTheory.MeasureSpace.volume s ≠ ⊤)
    {f g : α → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f
        (MeasureTheory.MeasureSpace.volume.restrict s))
    (hg : MeasureTheory.AEStronglyMeasurable g
        (MeasureTheory.MeasureSpace.volume.restrict s))
    {B ε : ℝ} (hB : 0 ≤ B) (hfB : ∀ x ∈ s, |f x| ≤ B) (hgB : ∀ x ∈ s, |g x| ≤ B)
    (hε : 0 ≤ ε) (hfg : ∀ x ∈ s, |f x - g x| ≤ ε) :
    |(∫ x in s, f x ^ 2) - (∫ x in s, g x ^ 2)|
      ≤ 2 * B * ε * (MeasureTheory.MeasureSpace.volume s).toReal := by
  have hvol_lt : (MeasureTheory.MeasureSpace.volume : Measure α) s < ⊤ :=
    lt_top_iff_ne_top.mpr hvol
  -- Both squared functions are integrable on `s`, since they are bounded there.
  have hf2 : IntegrableOn (fun x => f x ^ 2) s := by
    refine IntegrableOn.of_bound (μ := MeasureTheory.MeasureSpace.volume) (s := s)
      (f := fun x => f x ^ 2) hvol_lt ?_ (B ^ 2) ?_
    · exact hf.pow 2
    · filter_upwards [ae_restrict_mem hs] with x hx
      have h1 : |f x| ≤ B := hfB x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hg2 : IntegrableOn (fun x => g x ^ 2) s := by
    refine IntegrableOn.of_bound (μ := MeasureTheory.MeasureSpace.volume) (s := s)
      (f := fun x => g x ^ 2) hvol_lt ?_ (B ^ 2) ?_
    · exact hg.pow 2
    · filter_upwards [ae_restrict_mem hs] with x hx
      have h1 : |g x| ≤ B := hgB x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hdiff : (∫ x in s, f x ^ 2) - (∫ x in s, g x ^ 2) = ∫ x in s, (f x ^ 2 - g x ^ 2) :=
    (integral_sub hf2 hg2).symm
  calc |(∫ x in s, f x ^ 2) - (∫ x in s, g x ^ 2)|
      = |∫ x in s, (f x ^ 2 - g x ^ 2)| := by rw [hdiff]
    _ ≤ ∫ x in s, |f x ^ 2 - g x ^ 2| := abs_integral_le_integral_abs
    _ ≤ ∫ x in s, (2 * B * ε) := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun x => abs_nonneg _)
          · exact integrableOn_const hvol
          · filter_upwards [ae_restrict_mem hs] with x hx
            have h1 : |f x + g x| ≤ 2 * B := by
              calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
                _ ≤ B + B := add_le_add (hfB x hx) (hgB x hx)
                _ = 2 * B := by ring
            have h2 : f x ^ 2 - g x ^ 2 = (f x - g x) * (f x + g x) := by ring
            rw [h2, abs_mul]
            have hmul := mul_le_mul (hfg x hx) h1 (abs_nonneg _) hε
            linarith
    _ = 2 * B * ε * (MeasureTheory.MeasureSpace.volume s).toReal := by
          rw [setIntegral_const]
          rw [Measure.real]
          ring

end Commons.Analysis.Integral