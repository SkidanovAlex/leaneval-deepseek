import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.DivQ.sqIntervalIntegralLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Cauchy–Schwarz for the interval integral against the angular energy

The angular weight `sEta θ = sin(2θ)^{-η}` (`η = 99/100`, `Iθ = [0, π/2]`) satisfies `sEta ≥ 1`
on the open interval `(0, π/2)` (and the two endpoints are null), so the weighted energy
`∫_{Iθ} g² sEta` dominates the *unweighted* energy `∫_[a,b] g²` for every subinterval
`[a,b] ⊆ Iθ`.  Combined with the elementary Cauchy–Schwarz inequality for interval integrals
(`Work.FTS.H2.DivQ.sqIntervalIntegralLe`) and `b - a ≤ π/2`, this gives

  `(∫_a^b g)² ≤ (π/2) · ∫_{Iθ} g² sEta`.

The hypothesis `IntegrableOn (g² sEta) Iθ` forces `g²` (hence `g`) itself to be integrable on
`Iθ`, because `sEta ≥ 1` a.e. there: this is what makes all the interval integrals below the
honest ones (no junk value `0`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- On the open angular interval `(0, π/2)` the weight `sEta = sin(2θ)^{-η}` is at least `1`. -/
private theorem one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  show 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h := Real.rpow_le_rpow_of_nonpos hs (Real.sin_le_one (2 * θ))
    (neg_nonpos.mpr Work.Spaces.eta_nonneg)
  rw [Real.one_rpow] at h
  exact h

/-- `sEta` is nonnegative on `Iθ`. -/
private theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

theorem cs_interval_le {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) (hab : a ≤ b) :
    (∫ x in a..b, g x) ^ 2
      ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  -- ## Step 0: the sub-intervals of `[0, π/2]` sit inside `Iθ`, resp. `(0, π/2)`
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_trans ha (le_of_lt hx.1), le_trans hx.2 hb⟩
  have hIoo_sub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
  -- ## Step 1: `sEta ≥ 1` off the two null endpoints
  have haeIθ : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      1 ≤ Work.FTS.EllipticEst.sEta θ := by
    have h1 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)),
        1 ≤ Work.FTS.EllipticEst.sEta θ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      exact one_le_sEta_of_mem_Ioo hθ
    rw [MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h1
    simpa only [Work.Spaces.Iθ] using h1
  have haeIoc : ∀ᵐ θ ∂(volume : Measure ℝ).restrict (Set.Ioc a b),
      1 ≤ Work.FTS.EllipticEst.sEta θ := by
    have h1 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict (Set.Ioo a b),
        1 ≤ Work.FTS.EllipticEst.sEta θ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      exact one_le_sEta_of_mem_Ioo (hIoo_sub hθ)
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := a) (b := b))] at h1
    exact h1
  -- ## Step 2: `g²` is integrable on `Iθ`
  have hg2Iθ : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ := by
    have hAESM : AEStronglyMeasurable (fun θ => (g θ) ^ 2)
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
      have h1 : AEStronglyMeasurable (fun θ => (g θ) ^ 2)
          ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
        (hg.aestronglyMeasurable measurableSet_Ioo).pow 2
      rw [MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h1
      simpa only [Work.Spaces.Iθ] using h1
    refine MeasureTheory.Integrable.mono' hint hAESM ?_
    filter_upwards [haeIθ] with θ hθ
    have h2 : ‖(g θ) ^ 2‖ = (g θ) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [h2]
    exact le_mul_of_one_le_right (sq_nonneg _) hθ
  -- ## Step 3: `g²` and `g` are integrable on `Ioc a b`
  have hg2Ioc : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) (Set.Ioc a b) :=
    hg2Iθ.mono_set hsub
  have hAESM_Ioc : AEStronglyMeasurable g ((volume : Measure ℝ).restrict (Set.Ioc a b)) := by
    have h1 : AEStronglyMeasurable g ((volume : Measure ℝ).restrict (Set.Ioo a b)) :=
      (hg.mono hIoo_sub).aestronglyMeasurable measurableSet_Ioo
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := a) (b := b))] at h1
    exact h1
  have hgIoc : MeasureTheory.IntegrableOn g (Set.Ioc a b) := by
    haveI : MeasureTheory.IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc a b)) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
    have hmem : MemLp g 2 ((volume : Measure ℝ).restrict (Set.Ioc a b)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq hAESM_Ioc).mpr hg2Ioc
    have hmem1 : MemLp g 1 ((volume : Measure ℝ).restrict (Set.Ioc a b)) :=
      hmem.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)
    exact MeasureTheory.memLp_one_iff_integrable.mp hmem1
  -- ## Step 4: Cauchy–Schwarz on `[a,b]`
  have hf : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hgIoc
  have hf2 : IntervalIntegrable (fun x => g x ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hg2Ioc
  have hCS := Work.FTS.H2.DivQ.sqIntervalIntegralLe g hab hf hf2
  -- ## Step 5: `∫_a^b g² ≤ ∫_{Iθ} g² sEta`
  have hcmp : (∫ x in a..b, g x ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [intervalIntegral.integral_of_le hab]
    have hstep1 : (∫ x in Set.Ioc a b, g x ^ 2)
        ≤ ∫ x in Set.Ioc a b, g x ^ 2 * Work.FTS.EllipticEst.sEta x := by
      refine MeasureTheory.integral_mono_ae hg2Ioc (hint.mono_set hsub) ?_
      filter_upwards [haeIoc] with θ hθ
      exact le_mul_of_one_le_right (sq_nonneg _) hθ
    have hstep2 : (∫ x in Set.Ioc a b, g x ^ 2 * Work.FTS.EllipticEst.sEta x)
        ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
      · filter_upwards [MeasureTheory.self_mem_ae_restrict
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ)
      · filter_upwards with x hx using hsub hx
    linarith
  -- ## Step 6: assemble
  have hba : b - a ≤ Real.pi / 2 := by linarith
  have hnn : 0 ≤ ∫ x in a..b, g x ^ 2 :=
    intervalIntegral.integral_nonneg hab fun u _ => sq_nonneg _
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  calc (∫ x in a..b, g x) ^ 2 ≤ (b - a) * (∫ x in a..b, g x ^ 2) := hCS
    _ ≤ (Real.pi / 2) * (∫ x in a..b, g x ^ 2) := mul_le_mul_of_nonneg_right hba hnn
    _ ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
        mul_le_mul_of_nonneg_left hcmp hpi

end Work.FTS.EllipticEst.Mine
