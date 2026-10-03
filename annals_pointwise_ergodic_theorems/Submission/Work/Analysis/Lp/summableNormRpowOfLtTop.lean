import Mathlib

/-!
# `ℓᵖ`-sequences on `ℤ` have summable `p`-th powers of the norms

If `f : ℤ → ℂ` satisfies `eLpNorm f (ofReal p) Measure.count < ⊤` for some real `1 < p`, then the
real series `∑_k ‖f k‖ ^ p` converges.

The measure `Measure.count` on `ℤ` is the sum of Dirac masses, so its `lintegral` theory is just
`tsum`: `∫⁻ x, g x ∂count = ∑' x, g x`. Hence `eLpNorm f p count < ⊤` says that
`∑'_x ‖f x‖ₑ ^ p` is finite in `ℝ≥0∞`, and since `‖f x‖ₑ ^ p = ENNReal.ofReal (‖f x‖ ^ p)`, that
`ℝ≥0∞`-sum is `∑'_x ofReal (‖f x‖ ^ p)`. Finiteness of it is equivalent
(`ENNReal.tsum_coe_ne_top_iff_summable`) to summability of the `ℝ≥0`-valued sequence
`x ↦ Real.toNNReal (‖f x‖ ^ p)`, which `NNReal.summable_coe` transfers back to `ℝ`.

This is the `p = ofReal p` instance of `Work.Analysis.Lp.summable_norm_rpow_of_eLpNorm`; the proof
is the general-`p` form of `Work.KMTAreas.A4.memLp_two_count_summable_norm_sq` (the case `p = 2`).
-/

namespace Work.Analysis.Lp

open MeasureTheory ENNReal
open scoped NNReal

theorem summableNormRpowOfLtTop (f : ℤ → ℂ) (p : ℝ) (hp : 1 < p)
    (hf : MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count < ⊤) :
    Summable (fun k : ℤ => ‖f k‖ ^ p) := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  -- Step 1: `eLpNorm f (ofReal p) count < ⊤` gives finiteness of
  -- `∫⁻ x, ‖f x‖ₑ ^ p ∂count`, which against the counting measure is `∑' x, ‖f x‖ₑ ^ p`.
  have h2 : (∑' x : ℤ, ‖f x‖ₑ ^ p) < ∞ := by
    have h := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := ENNReal.ofReal p) (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top hf
    rw [MeasureTheory.lintegral_count, ENNReal.toReal_ofReal hp0.le] at h
    exact h
  -- Step 2: rewrite every term as `ENNReal.ofReal (‖f x‖ ^ p)`.
  have h3 : (∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ p)) < ∞ := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun x => ?_) h2
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  -- Step 3: finiteness of `∑' x, ENNReal.ofReal (‖f x‖ ^ p)` is exactly summability of the
  -- non-negative real sequence `x ↦ ‖f x‖ ^ p`.
  have h4 : Summable (fun x : ℤ => (Real.toNNReal (‖f x‖ ^ p) : ℝ≥0)) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp h3.ne
  have h5 : Summable (fun x : ℤ => ((Real.toNNReal (‖f x‖ ^ p) : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr h4
  exact h5.congr
    (fun x => Real.coe_toNNReal (‖f x‖ ^ p) (Real.rpow_nonneg (norm_nonneg _) p))

end Work.Analysis.Lp
