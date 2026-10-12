import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.chBslotAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chBW1farIntegrable`

The one-body weight of the `(B)` slot, `W₁ = g₀/(χ⋆χ)(·/ℓ)` (`Work.BoseFixR.W1fun`), is
integrable in absolute value as soon as the box is at least twice the potential radius,
`2R ≤ ℓ`.

**Proof.**  `W₁ = g₀ / (χ⋆χ)_ℓ`, with `g₀ = v(1−ω)` supported in `ball 0 R`
(`g0_zero_of_norm_ge`, from `tsupport v ⊆ ball 0 R`).  For `‖z‖ < ℓ` the convolution
`(χ⋆χ)_ℓ` is strictly positive (`convScale_pos_of_norm_lt`), so it attains a strictly
positive minimum `m` on the compact ball `‖z‖ ≤ R` (`convScale_lower_closedBall`, which
only needs `R < ℓ`, here `R < 2R ≤ ℓ`).  Hence

    |W₁ z| ≤ (1/m)·|g₀ z|     for every `z : ℝ³`

(the factor `1/m` on `‖z‖ ≤ R`, and both sides `0` for `‖z‖ > R`), and `g₀` is
integrable (`g0_integrable`).  Domination closes the argument.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem chBW1farIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hRℓ : 2 * R ≤ ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => |Work.BoseFixR.W1fun v h ℓ z|) := by
  -- a strictly positive uniform lower bound for `(χ⋆χ)_ℓ` on the support ball `‖z‖ ≤ R`
  obtain ⟨m, hmpos, hm⟩ := convScale_lower_closedBall (ℓ := ℓ) (r := R) hℓ (by linarith)
  -- `g₀ = v(1−ω)` is integrable and vanishes off `ball 0 R`
  have hgI : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0z : ∀ x : E3, R ≤ ‖x‖ → Submission.BoseGases.g0 v h x = 0 :=
    fun x hx => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
  -- measurability of `W₁ = g₀/(χ⋆χ)_ℓ`
  have hconv : MeasureTheory.AEStronglyMeasurable
      (fun x : E3 => (Submission.BoseGases.convScale ℓ x)⁻¹) :=
    ((Submission.BoseGases.convScale_continuous ℓ).measurable.inv).aestronglyMeasurable
  have hmeas : MeasureTheory.AEStronglyMeasurable (Work.BoseFixR.W1fun v h ℓ) := by
    refine MeasureTheory.AEStronglyMeasurable.congr (hgI.aestronglyMeasurable.mul hconv) ?_
    filter_upwards with x
    simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, div_eq_mul_inv]
  -- the pointwise domination `|W₁ z| ≤ (1/m)·|g₀ z|`
  have hbd : ∀ᵐ x ∂(volume : Measure E3),
      ‖Work.BoseFixR.W1fun v h ℓ x‖ ≤ (1 / m) * ‖Submission.BoseGases.g0 v h x‖ := by
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : ‖x‖ ≤ R
    · have hcs : m ≤ Submission.BoseGases.convScale ℓ x := hm x hx
      have hpos : 0 < Submission.BoseGases.convScale ℓ x := lt_of_lt_of_le hmpos hcs
      have h1 : (1 : ℝ) ≤ (1 / m) * Submission.BoseGases.convScale ℓ x := by
        have h2 : (1 : ℝ) ≤ Submission.BoseGases.convScale ℓ x / m :=
          (one_le_div hmpos).mpr hcs
        simpa [div_eq_mul_inv, mul_comm] using h2
      rw [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      nlinarith [abs_nonneg (Submission.BoseGases.g0 v h x)]
    · have hx' : R ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
      have hg : Submission.BoseGases.g0 v h x = 0 := hg0z x hx'
      rw [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hg, zero_div]
      simp
  -- integration by domination
  have hW1I : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    MeasureTheory.Integrable.mono' (hgI.norm.const_mul (1 / m)) hmeas hbd
  simpa only [Real.norm_eq_abs] using hW1I.abs

end Work.BoseBoxFock.PCFU
