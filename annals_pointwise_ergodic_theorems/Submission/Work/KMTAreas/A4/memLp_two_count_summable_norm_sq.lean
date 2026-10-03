import Mathlib

namespace Work.KMTAreas.A4

open MeasureTheory ENNReal
open scoped NNReal

/-- **`ℓ²(ℤ)` is `L²(ℤ, counting measure)`.**

If a sequence `f : ℤ → ℂ` belongs to `L²` of the counting measure on `ℤ`, i.e.
`∫⁻ x, ‖f x‖ₑ ^ 2 ∂count < ∞`, then the series of squared moduli `∑' x, ‖f x‖ ^ 2`
converges: an `L²` function against counting measure is exactly a square-summable
sequence.

The proof is the computation `∫⁻ x, g x ∂count = ∑' x, g x` (`lintegral_count`)
together with the identification `‖f x‖ₑ ^ 2 = ENNReal.ofReal (‖f x‖ ^ 2)`, and the
equivalence, for non-negative reals, between `Summable` and finiteness of the
associated `ℝ≥0∞`-valued `tsum`. -/
theorem memLp_two_count_summable_norm_sq {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    Summable (fun x : ℤ => ‖f x‖ ^ 2) := by
  -- Step 1: `MemLp f 2 count` gives finiteness of `∫⁻ x, ‖f x‖ₑ ^ 2 ∂count`,
  -- which against counting measure is the `tsum` of the terms `‖f x‖ₑ ^ 2`.
  have h2 : (∑' x : ℤ, ‖f x‖ₑ ^ (((2:ℕ):ℝ))) < ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2:ℝ≥0∞))
      (by norm_num) (by norm_num) hf.eLpNorm_lt_top
    rw [lintegral_count] at h
    simpa [ENNReal.toReal_ofNat] using h
  -- Step 2: rewrite each term as `ENNReal.ofReal (‖f x‖ ^ 2)`.
  have h3 : (∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ 2)) < ∞ := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun x => ?_) h2
    apply le_of_eq
    rw [← Real.rpow_natCast (‖f x‖) 2, ← ofReal_norm,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ ((2:ℕ):ℝ))]
  -- Step 3: finiteness of `∑' x, ENNReal.ofReal (‖f x‖ ^ 2)` is exactly summability
  -- of the non-negative real sequence `x ↦ ‖f x‖ ^ 2`.
  have h4 : Summable (fun x : ℤ => (Real.toNNReal (‖f x‖ ^ 2) : ℝ≥0)) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp h3.ne
  have h5 : Summable (fun x : ℤ => ((Real.toNNReal (‖f x‖ ^ 2) : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr h4
  exact h5.congr (fun x => Real.coe_toNNReal (‖f x‖ ^ 2) (sq_nonneg _))

end Work.KMTAreas.A4
