/-
# Integrability of the `sinθcos²θ`-moment of a slice of an `ℋ⁴` profile

For a profile `f` which is `C^∞` on the open quadrant (`Work.FTS.LocData.SmoothQuad`) and
whose weighted derivatives are in `L²` (`Work.Spaces.HkMem α 4 f`), the angular slice
`θ ↦ f z θ` is integrable against the angular profile `sinθcos²θ` on `θ ∈ [0,π/2]`, for every
`z > 0`.

The mathematical content is small but the analytic control at the two endpoints `θ = 0` and
`θ = π/2` is exactly what `HkMem` provides:

* `Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted` absorbs the (bounded, vanishing)
  factor `|sinθcos²θ| ≤ 1` into the weighted square
  `(f z θ · w z / sin(2θ)^{η/2})²` plus the constant `1`;
* the square is integrable on `Iθ` because it is the `i = 0` summand of the integrand
  `Work.Spaces.HkIntegrand α 4 f z θ`, which is integrable for every `z ∈ Iz` by `HkMem`
  (`Work.Spaces.sq_le_HkIntegrand_z`);
* the constant `1` is integrable because `Iθ` has finite Lebesgue measure;
* the required almost-everywhere strong measurability comes from `SmoothQuad` through
  `Work.Spaces.aesm_slice_of_continuousOn_Qd`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T.Hardy

set_option autoImplicit false

/-! ## Elementary auxiliary facts -/

/-- The angular profile `sinθcos²θ` is continuous. -/
private theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- `SmoothQuad f` gives continuity of the uncurried `f` on the smaller open quadrant
`(0,∞) × (0,π/2)`. -/
private theorem continuousOn_uncurry_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  hsm.continuousOn.mono (Set.prod_mono (fun x hx => by
    simp only [Set.mem_Ioi] at hx ⊢
    linarith) (subset_refl _))

/-- The angular factor `θ ↦ w z / sin(2θ)^{η/2}` is measurable. -/
private theorem measurable_angularWeight (z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  exact measurable_const.div (hsin.pow_const _)

/-- The angular interval `Iθ = [0,π/2]` has finite Lebesgue measure. -/
private theorem volume_Iθ_lt_top : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-! ## The main statement -/

theorem slice_sinCos2_integrable (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro z hz
  have hu : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    continuousOn_uncurry_of_smoothQuad hsm
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- almost everywhere strong measurability of the angular slice of `f`
  have haesm_f : AEStronglyMeasurable (fun θ : ℝ => f z θ) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hu hz
  -- the weighted square `(f z θ · w z / sin(2θ)^{η/2})²` is the `i = 0` summand of the
  -- `ℋ⁴`-integrand at `z`, hence integrable
  have hterm : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ := by
    refine (hmem.1 z hzIz).mono' ?_ ?_
    · exact (haesm_f.mul (measurable_angularWeight z).aestronglyMeasurable).pow 2
    · refine Eventually.of_forall fun θ => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 0 (by norm_num)
  -- the dominating function of the AM–GM bound: the weighted square plus the constant `1`
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1) Work.Spaces.Iθ :=
    hterm.add (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ)
      (ne_of_lt volume_Iθ_lt_top))
  refine hdom.mono' ?_ ?_
  · exact haesm_f.mul continuous_sinCos2.measurable.aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem hIθ fun θ hθ => ?_
    rw [Real.norm_eq_abs]
    exact Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted hz hθ

end Work.FTS.CoercivityFix.Coer1T.Hardy
