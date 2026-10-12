import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.PotCubicSmoothWeight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.uvKernel_tail_of_decay`

The UV-smoothing kernel `uvKernel fu Λ` obeys, for every `Λ > 0`, the *scaled* Schwartz decay
bound `‖uvKernel fu Λ z‖ ≤ C Λ³ (1 + Λ‖z‖)^{-5}` (the `N = 5` case of
`Work.BoseBoxFock.lowCut_invFT_scaled`).  This file shows that the **outer tail** of such a
kernel is negligible:

    ∫_{δ ≤ ‖z‖} ‖uvKernel fu Λ z‖ dz → 0   (Λ → ∞)      for every fixed `δ > 0`.

The mechanism is the scaling.  For `Λ > 0` the change of variables `z = Λ⁻¹ • y`
(`Measure.integral_comp_inv_smul_of_nonneg`) turns the majorant integral into

    ∫_{δ ≤ ‖z‖} Λ³ (1 + Λ‖z‖)^{-5} dz = ∫_{Λδ ≤ ‖y‖} (1 + ‖y‖)^{-5} dy ,

and the latter is the *tail of the fixed integrable function* `y ↦ (1 + ‖y‖)^{-5}` over the
shrinking family of exteriors `{Λδ ≤ ‖y‖}`: it vanishes by dominated convergence
(`tendsto_integral_filter_of_dominated_convergence`).  Integrability of the fixed majorant is
`integrable_one_add_norm` (`5 > 3 = finrank ℝ ℝ³`).

Both halves are proved here as standalone lemmas (`integrable_one_add_norm_zpow`,
`tendsto_setIntegral_tail_radial`), and the target is then a squeeze between `0` and the
rescaled majorant `C · ∫_{Λδ ≤ ‖y‖} (1 + ‖y‖)^{-5} dy`.

## Environment notes (for reuse)

* `Integrable.integrableOn` takes the set as an *implicit* argument (`(s := …)`).
* `Measure.setIntegral_comp_smul_of_pos` is *not* needed here: the set-integral form is avoided
  by working with indicator functions and the set-free
  `Measure.integral_comp_inv_smul_of_nonneg`.
* The `rpow`/`zpow` bridge for a nonnegative base is
  `rw [Real.rpow_neg (by positivity), Real.rpow_natCast, zpow_neg, zpow_natCast]`.
-/

namespace Work.BoseBoxFock

open MeasureTheory Filter
open scoped Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The radial majorant `y ↦ (1 + ‖y‖)^{-n}` is integrable on `ℝ³` as soon as `n > 3 = finrank`.
This is Mathlib's `integrable_one_add_norm` (which is stated with `rpow`), transported to the
integer power used by the decay hypotheses of this chapter. -/
lemma integrable_one_add_norm_zpow (n : ℕ) (hn : 3 < n) :
    Integrable (fun y : E3 => (1 + ‖y‖) ^ (-(n : ℤ))) volume := by
  have hn' : (Module.finrank ℝ E3 : ℝ) < (n : ℝ) := by
    rw [finrank_euclideanSpace_fin]; exact_mod_cast hn
  refine (integrable_one_add_norm (E := E3) (μ := volume) (r := (n : ℝ)) hn').congr ?_
  filter_upwards with y
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, zpow_neg, zpow_natCast]

/-- **The tail of the radial majorant vanishes.**  For `n > 3`, the integrals of
`y ↦ (1 + ‖y‖)^{-n}` over the exteriors `{R ≤ ‖y‖}` tend to `0` as `R → ∞`. -/
lemma tendsto_setIntegral_tail_radial_zpow (n : ℕ) (hn : 3 < n) :
    Tendsto (fun R : ℝ => ∫ y in {y : E3 | R ≤ ‖y‖}, (1 + ‖y‖) ^ (-(n : ℤ))) atTop (nhds 0) := by
  have hg := integrable_one_add_norm_zpow n hn
  have hmeas : ∀ R : ℝ, MeasurableSet {y : E3 | R ≤ ‖y‖} :=
    fun R => (isClosed_le continuous_const continuous_norm).measurableSet
  -- measurability, for every `R`, of the truncated integrand
  have hmeas' : ∀ᶠ R in atTop, AEStronglyMeasurable
      (fun y : E3 => ({y : E3 | R ≤ ‖y‖}).indicator (fun y => (1 + ‖y‖) ^ (-(n : ℤ))) y)
      volume :=
    Eventually.of_forall fun R => hg.aestronglyMeasurable.indicator (hmeas R)
  -- the fixed integrable majorant bounds every truncation
  have hbound' : ∀ᶠ R in atTop, ∀ᵐ y ∂volume,
      ‖({y : E3 | R ≤ ‖y‖}).indicator (fun y => (1 + ‖y‖) ^ (-(n : ℤ))) y‖
        ≤ (1 + ‖y‖) ^ (-(n : ℤ)) := by
    filter_upwards with R
    filter_upwards with y
    by_cases hy : R ≤ ‖y‖
    · rw [Set.indicator_of_mem (show y ∈ {y : E3 | R ≤ ‖y‖} from hy), Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    · rw [Set.indicator_of_notMem (show y ∉ {y : E3 | R ≤ ‖y‖} from hy), norm_zero]
      positivity
  -- pointwise, the truncations vanish (each `y` is eventually in the inner ball)
  have hlim' : ∀ᵐ y ∂volume, Tendsto
      (fun R : ℝ => ({y : E3 | R ≤ ‖y‖}).indicator (fun y => (1 + ‖y‖) ^ (-(n : ℤ))) y)
      atTop (nhds 0) := by
    filter_upwards with y
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [eventually_gt_atTop ‖y‖] with R hR
    rw [Set.indicator_of_notMem (show y ∉ {y : E3 | R ≤ ‖y‖} from not_le.mpr hR)]
  have hmain := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (bound := fun y : E3 => (1 + ‖y‖) ^ (-(n : ℤ)))
    (F := fun R : ℝ => fun y : E3 =>
      ({y : E3 | R ≤ ‖y‖}).indicator (fun y => (1 + ‖y‖) ^ (-(n : ℤ))) y)
    (f := fun _ : E3 => (0 : ℝ)) hmeas' hbound' hg hlim'
  have hF : (fun R : ℝ => ∫ y : E3,
        ({y : E3 | R ≤ ‖y‖}).indicator (fun y => (1 + ‖y‖) ^ (-(n : ℤ))) y)
      = fun R : ℝ => ∫ y in {y : E3 | R ≤ ‖y‖}, (1 + ‖y‖) ^ (-(n : ℤ)) := by
    funext R
    exact integral_indicator (hmeas R)
  rw [hF] at hmain
  simpa using hmain

theorem uvKernel_tail_of_decay (fu : Work.BoseBoxFix.LowCut) {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ (Λ : ℝ), 0 < Λ → ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.uvKernel fu Λ z‖ ≤ C * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun Λ : ℝ => ∫ z in {z : EuclideanSpace ℝ (Fin 3) | δ ≤ ‖z‖},
        ‖Work.BoseBoxFock.uvKernel fu Λ z‖)
      Filter.atTop (nhds 0) := by
  have hs : MeasurableSet {z : E3 | δ ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hg : Integrable (fun y : E3 => (1 + ‖y‖) ^ (-(5 : ℤ))) volume :=
    integrable_one_add_norm_zpow 5 (by norm_num)
  have htail : Tendsto (fun R : ℝ => ∫ y in {y : E3 | R ≤ ‖y‖}, (1 + ‖y‖) ^ (-(5 : ℤ)))
      atTop (nhds 0) := tendsto_setIntegral_tail_radial_zpow 5 (by norm_num)
  -- the rescaled majorant tends to `0`
  have hlim : Tendsto
      (fun Λ : ℝ => C * ∫ y in {y : E3 | Λ * δ ≤ ‖y‖}, (1 + ‖y‖) ^ (-(5 : ℤ)))
      atTop (nhds 0) := by
    have h2 : Tendsto (fun Λ : ℝ => Λ * δ) atTop atTop := by
      simpa [mul_comm] using tendsto_id.const_mul_atTop hδ
    have h3 : Tendsto (fun R : ℝ => C * ∫ y in {y : E3 | R ≤ ‖y‖}, (1 + ‖y‖) ^ (-(5 : ℤ)))
        atTop (nhds 0) := by
      simpa using htail.const_mul C
    exact h3.comp h2
  -- the pointwise bound, rescaled
  have hbound : ∀ Λ : ℝ, 0 < Λ →
      (∫ z in {z : E3 | δ ≤ ‖z‖}, ‖uvKernel fu Λ z‖)
        ≤ C * ∫ y in {y : E3 | Λ * δ ≤ ‖y‖}, (1 + ‖y‖) ^ (-(5 : ℤ)) := by
    intro Λ hΛ
    have hcomp : Integrable (fun z : E3 => (1 + ‖Λ • z‖) ^ (-(5 : ℤ))) volume :=
      (integrable_comp_smul_iff volume (fun y : E3 => (1 + ‖y‖) ^ (-(5 : ℤ))) hΛ.ne').mpr hg
    have hcomp' : Integrable (fun z : E3 => (1 + Λ * ‖z‖) ^ (-(5 : ℤ))) volume :=
      hcomp.congr (Eventually.of_forall fun z => by
        show (1 + ‖Λ • z‖) ^ (-(5 : ℤ)) = (1 + Λ * ‖z‖) ^ (-(5 : ℤ))
        rw [norm_smul, Real.norm_of_nonneg hΛ.le])
    have hmaj : Integrable (fun z : E3 => C * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
        (volume.restrict {z : E3 | δ ≤ ‖z‖}) :=
      (hcomp'.integrableOn (s := {z : E3 | δ ≤ ‖z‖})).const_mul (C * Λ ^ 3)
    have hmono : (∫ z in {z : E3 | δ ≤ ‖z‖}, ‖uvKernel fu Λ z‖)
        ≤ ∫ z in {z : E3 | δ ≤ ‖z‖}, C * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)) :=
      integral_mono_of_nonneg (μ := volume.restrict {z : E3 | δ ≤ ‖z‖})
        (Eventually.of_forall fun z => norm_nonneg _) hmaj
        (Eventually.of_forall fun z => hdec Λ hΛ z)
    -- the rescaled majorant identity `z = Λ⁻¹ • y`
    have hsub : (∫ z in {z : E3 | δ ≤ ‖z‖}, (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
        = (Λ ^ 3)⁻¹ * ∫ y in {y : E3 | Λ * δ ≤ ‖y‖}, (1 + ‖y‖) ^ (-(5 : ℤ)) := by
      set f : E3 → ℝ := ({z : E3 | δ ≤ ‖z‖}).indicator (fun z => (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
        with hf
      have hfun : (fun y : E3 =>
            ({y : E3 | Λ * δ ≤ ‖y‖}).indicator (fun y => (1 + ‖y‖) ^ (-(5 : ℤ))) y)
          = fun y : E3 => f (Λ⁻¹ • y) := by
        funext y
        rw [hf]
        by_cases hy : Λ * δ ≤ ‖y‖
        · rw [Set.indicator_of_mem (show y ∈ {y : E3 | Λ * δ ≤ ‖y‖} from hy)]
          have hy' : Λ⁻¹ • y ∈ {z : E3 | δ ≤ ‖z‖} := by
            change δ ≤ ‖Λ⁻¹ • y‖
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hΛ.le)]
            calc δ = Λ⁻¹ * (Λ * δ) := by rw [← mul_assoc, inv_mul_cancel₀ hΛ.ne', one_mul]
              _ ≤ Λ⁻¹ * ‖y‖ := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hΛ.le)
          rw [Set.indicator_of_mem hy']
          congr 1
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hΛ.le), ← mul_assoc,
            mul_inv_cancel₀ hΛ.ne', one_mul]
        · rw [Set.indicator_of_notMem (show y ∉ {y : E3 | Λ * δ ≤ ‖y‖} from hy)]
          have hy' : Λ⁻¹ • y ∉ {z : E3 | δ ≤ ‖z‖} := by
            change ¬ (δ ≤ ‖Λ⁻¹ • y‖)
            rw [not_le] at hy
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hΛ.le), not_le]
            calc Λ⁻¹ * ‖y‖ < Λ⁻¹ * (Λ * δ) := mul_lt_mul_of_pos_left hy (inv_pos.mpr hΛ)
              _ = δ := by rw [← mul_assoc, inv_mul_cancel₀ hΛ.ne', one_mul]
          rw [Set.indicator_of_notMem hy']
      have hc := Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure E3))
        (f := f) hΛ.le
      rw [finrank_euclideanSpace_fin, smul_eq_mul] at hc
      rw [← hfun, integral_indicator hs,
        integral_indicator (isClosed_le continuous_const continuous_norm).measurableSet] at hc
      rw [hc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 hΛ.ne'), one_mul]
    have hmaj_eq : (∫ z in {z : E3 | δ ≤ ‖z‖}, C * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
        = C * ∫ y in {y : E3 | Λ * δ ≤ ‖y‖}, (1 + ‖y‖) ^ (-(5 : ℤ)) := by
      rw [integral_const_mul, hsub, mul_assoc]
      congr 1
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hΛ.ne'), one_mul]
    exact hmono.trans_eq hmaj_eq
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with Λ
    exact setIntegral_nonneg hs (fun z _ => norm_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
    exact hbound Λ hΛ

end Work.BoseBoxFock
