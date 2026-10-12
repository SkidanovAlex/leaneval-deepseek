import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.integral_symbol_mul_le
import Submission.Work.BoseFixB3.CS.Pieces.norm_kinFT_indicator_acube_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.lowMult_abs_le_of_box_bound`

Pointwise bound for the low-momentum Fourier multiplier `lowMult` (FS's `Q_L = f_L(√−Δ)`)
applied to a state `ψ` which is bounded by `D` on the centred box `Λ(ℓ) = acube ℓ`:

`|lowMult fc κ ℓ ψ x| ≤ (2π)⁻³ · (∫_p |f(‖p‖/κ)|) · (D ℓ³)`,

uniformly in `x` and `κ`.  This is the box-uniform form of the elementary `L¹` bound: the
`p`-integral defining `lowMult` carries the symbol `f(‖p‖/κ)` (of `L¹`-norm `∫|f(‖p‖/κ)|`)
times the momentum profile `kinFT(1_Λψ)`, whose sup-norm is at most `∫_{Λ}|ψ| ≤ D·vol Λ = D ℓ³`.

## Route

1. `Work.BoseFixB3.HighMass.abs_lowMult_le` (with the integrability of `1_Λψ`, obtained from
   `|ψ| ≤ D` on the finite-measure box) bounds `|lowMult fc κ ℓ ψ x|` by
   `(2π)⁻³ ∫_p |f(‖p‖/κ)| · ‖kinFT(1_Λψ)(p)‖`;
2. `Work.BoseFixB3.CS.Pieces.norm_kinFT_indicator_acube_le` shows the pointwise bound
   `‖kinFT(1_Λψ)(p)‖ ≤ D ℓ³`;
3. `Work.BoseFixB3.CS.Pieces.integral_symbol_mul_le` upgrades it to
   `∫_p |f(‖p‖/κ)| ‖kinFT(1_Λψ)(p)‖ ≤ (∫_p |f(‖p‖/κ)|) · (D ℓ³)`;
4. the prefactors are rearranged by `ring`.

The hypothesis `0 < κ` is what makes the symbol compactly supported (hence the multiplier a
genuine absolutely convergent integral).
-/

namespace Work.BoseFixB3.CS.Pieces

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem lowMult_abs_le_of_box_bound {fc : Work.BoseBoxFix.LowCut} {κ ℓ D : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (hD : 0 ≤ D) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψm : Measurable ψ)
    (hψb : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ D)
    (x : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseBoxFix.lowMult fc κ ℓ ψ x|
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), |fc.f (‖p‖ / κ)|) * (D * ℓ ^ 3) := by
  have hΛm : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  have hΛtop : (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ :=
    Submission.BoseGases.acube_lt_top ℓ hℓ.le
  -- the truncated state `1_Λψ` is integrable (it is bounded on the finite-measure box)
  have hΛint : Integrable ((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => D)) volume := by
    rw [integrable_indicator_iff hΛm]
    exact integrableOn_const (s := Submission.BoseGases.acube ℓ) (C := D)
      (hs := ne_of_lt hΛtop) (hC := by simp)
  have hθint : Integrable
      (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) volume := by
    refine Integrable.mono' hΛint ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp (hψm.indicator hΛm)).aestronglyMeasurable
    · filter_upwards with z
      by_cases hz : z ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        simpa using hψb z hz
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        simp
  -- the momentum profile of `1_Λψ` is bounded by `D ℓ³`
  have hkin : ∀ p : E3,
      ‖Submission.BoseGases.kinFT
        (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) p‖ ≤ D * ℓ ^ 3 :=
    fun p => norm_kinFT_indicator_acube_le hℓ hD hψm hψb p
  -- hence the weighted `p`-integral is bounded by `(∫|f|)·(D ℓ³)`
  have hweight : ∫ p : E3, |fc.f (‖p‖ / κ)| *
      ‖Submission.BoseGases.kinFT
        (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) p‖
      ≤ (∫ p : E3, |fc.f (‖p‖ / κ)|) * (D * ℓ ^ 3) :=
    integral_symbol_mul_le (fc := fc) hκ (mul_nonneg hD (by positivity))
      (fun p => norm_nonneg _) hkin
  calc |Work.BoseBoxFix.lowMult fc κ ℓ ψ x|
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, |fc.f (‖p‖ / κ)| *
          ‖Submission.BoseGases.kinFT
            (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) p‖ :=
        Work.BoseFixB3.HighMass.abs_lowMult_le hκ hθint x
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((∫ p : E3, |fc.f (‖p‖ / κ)|) * (D * ℓ ^ 3)) :=
        mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, |fc.f (‖p‖ / κ)|) * (D * ℓ ^ 3) := by ring

end

end Work.BoseFixB3.CS.Pieces
