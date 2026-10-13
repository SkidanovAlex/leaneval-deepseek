import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real BigOperators ENNReal
open MeasureTheory Filter

namespace Work.FTS.ClassC

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular weight `sEta θ = sin(2θ)^{-η}` is measurable. -/
theorem lplst_sEta_measurable : Measurable Work.FTS.EllipticEst.sEta := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

/-- The `N`-th partial sum `psiTrunc α F N z ·` is continuous in `θ`, being a finite linear
combination of the (continuous) eigenfunctions `eFam m`. -/
theorem lplst_psiTrunc_continuous (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ) (z : ℝ) :
    Continuous (fun θ : ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) := by
  unfold Work.FTS.PhiStar.Series.psiTrunc
  refine continuous_finsetSum _ (fun m _ => ?_)
  exact continuous_const.mul (Work.FTS.PhiStar.Series.continuous_eFam m)

/-- The `θ`-integrand of the truncated energy is (a.e.) measurable in `θ`.  This is what lets
Fatou's lemma be applied in the angular variable, pointwise in `z`. -/
theorem lplst_theta_integrand_aemeasurable (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ) (z : ℝ) :
    AEMeasurable (fun θ : ℝ => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h1 : Measurable (fun θ : ℝ => (Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2) :=
    (lplst_psiTrunc_continuous α F N z).measurable.pow_const 2
  have h2 : Measurable (fun θ : ℝ => (Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
      * (Work.Spaces.w z) ^ 2) := h1.mul measurable_const
  have h3 : Measurable (fun θ : ℝ => (Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    h2.mul lplst_sEta_measurable
  exact h3.ennreal_ofReal.aemeasurable

/-- **Angular Fatou.**  For every (fixed) `z`, the angular energy of the pointwise limit
`psiSeries` is bounded by the `liminf` of the angular energies of the truncations.  This is
Fatou's lemma in `θ`, applied to the (measurable) truncated integrands, and uses the pointwise
convergence `psiTrunc α F N z θ → psiSeries α F z θ`. -/
theorem lplst_theta_fatou (α : ℝ) (F : ℝ → ℝ → ℝ)
    (hconv : ∀ z θ, Filter.Tendsto (fun N => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
      Filter.atTop (nhds (Work.FTS.PhiStar.Series.psiSeries α F z θ))) (z : ℝ) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ))
      ≤ Filter.liminf (fun N : ℕ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) Filter.atTop := by
  have hfatou := MeasureTheory.lintegral_liminf_le'
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (u := Filter.atTop)
    (f := fun (N : ℕ) (θ : ℝ) => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ))
    (fun N => lplst_theta_integrand_aemeasurable α F N z)
  have hlim : (fun θ : ℝ => Filter.liminf (fun N : ℕ => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) Filter.atTop)
      = (fun θ : ℝ => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by
    funext θ
    have hc : Continuous (fun x : ℝ => ENNReal.ofReal
        (x ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
      ENNReal.continuous_ofReal.comp
        (((continuous_id.pow 2).mul continuous_const).mul continuous_const)
    exact (hc.continuousAt.tendsto.comp (hconv z θ)).liminf_eq
  rw [hlim] at hfatou
  exact hfatou

theorem lintegral_psiSeries_le_of_trunc (α : ℝ) (F : ℝ → ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hconv : ∀ z θ, Filter.Tendsto (fun N => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
      Filter.atTop (nhds (Work.FTS.PhiStar.Series.psiSeries α F z θ)))
    (hmeas : ∀ N : ℕ, AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hbd : ∀ N : ℕ, (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) ≤ ENNReal.ofReal C) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) ≤ ENNReal.ofReal C := by
  -- The `liminf` of the truncated energies is bounded by `ofReal C`, since every member is.
  have hliminf_le : Filter.liminf (fun N : ℕ => ∫⁻ z in Work.Spaces.Iz,
      ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) Filter.atTop ≤ ENNReal.ofReal C := by
    have hbdd : Filter.IsBoundedUnder (fun x1 x2 : ℝ≥0∞ => x2 ≤ x1) Filter.atTop
        (fun N : ℕ => ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) :=
      Filter.isBoundedUnder_of ⟨0, fun n => bot_le⟩
    exact Filter.liminf_le_of_frequently_le
      (Filter.Eventually.of_forall hbd).frequently hbdd
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, Filter.liminf (fun N : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop :=
        MeasureTheory.lintegral_mono (fun z => lplst_theta_fatou α F hconv z)
    _ ≤ Filter.liminf (fun N : ℕ => ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop :=
        MeasureTheory.lintegral_liminf_le' (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
          (u := Filter.atTop) hmeas
    _ ≤ ENNReal.ofReal C := hliminf_le

end Work.FTS.ClassC
