import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Have
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.RPFresh.deriv_integrableOn_right
import Submission.Work.RPFresh.integral_sin_two_rpow_le_right
import Submission.Work.FTS.EllipticEst.RPFresh.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RPFresh

open MeasureTheory Set intervalIntegral Filter
open scoped Real Topology

set_option autoImplicit false

/-- **The core of the right-endpoint slice bound.**  Under the hypotheses of
`slice_sq_le_right` one has, for every `θ ∈ (0,π/2)`,
`g θ ^ 2 ≤ (∫_θ^{π/2} σ (g')²) · (∫_θ^{π/2} sin(2t)^η dt)`.

This is the exact mirror of `slice_sq_le_core`: the fundamental theorem of calculus gives
`∫_θ^{π/2} g' = -g θ` (the trace hypothesis being now at the *right* endpoint `π/2`), and
the weighted Cauchy–Schwarz inequality applied to the pair
`(σ^{1/2} g', σ^{-1/2})` on `(θ, π/2)` gives the product of the two integrals. -/
theorem slice_sq_le_core_right (g : ℝ → ℝ) (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi/2)))
    (hg1 : Filter.Tendsto g (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.RPFresh.sg θ * (deriv g θ)^2) (Set.Ioo 0 (Real.pi/2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (g θ)^2 ≤ (∫ t in θ..(Real.pi/2), Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2)
      * (∫ t in θ..(Real.pi/2), (Real.sin (2*t))^(Work.Spaces.eta)) := by
  set A : ℝ → ℝ := fun t => Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2 with hA
  set B : ℝ → ℝ := fun t => (Real.sin (2*t))^(Work.Spaces.eta) with hB
  have hsin_nonneg : ∀ t ∈ Set.Ioo θ (Real.pi/2), 0 ≤ Real.sin (2*t) := by
    intro t ht
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1, hθ.1]) (by linarith [ht.2])
  have hAnneg : ∀ t ∈ Set.Ioo θ (Real.pi/2), 0 ≤ A t := by
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (hsin_nonneg t ht) _) (sq_nonneg _)
  have hBnneg : ∀ t ∈ Set.Ioo θ (Real.pi/2), 0 ≤ B t := by
    intro t ht
    exact Real.rpow_nonneg (hsin_nonneg t ht) _
  -- ### Fundamental theorem of calculus: `∫_θ^{π/2} g' = - g θ`
  have hderiv_int : IntegrableOn (deriv g) (Set.Ioo θ (Real.pi/2)) :=
    deriv_integrableOn_right g hg hint hθ
  have hII : IntervalIntegrable (deriv g) volume θ (Real.pi/2) := by
    rw [intervalIntegrable_iff, uIoc_of_le hθ.2.le]
    exact hderiv_int.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hderiv : ∀ x ∈ Set.Ioo θ (Real.pi/2), HasDerivAt g (deriv g x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    exact ((hg.differentiableOn (by norm_num)).differentiableAt
      (Ioo_mem_nhds hx'.1 hx'.2)).hasDerivAt
  have hcontθ : Tendsto g (𝓝[>] θ) (𝓝 (g θ)) :=
    ((hg.continuousOn.continuousAt (Ioo_mem_nhds hθ.1 hθ.2)).tendsto).mono_left
      nhdsWithin_le_nhds
  have hftc : ∫ t in θ..(Real.pi/2), deriv g t = - g θ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hθ.2 hderiv hII hcontθ hg1
    simpa using h
  have habs : |g θ| ≤ ∫ t in θ..(Real.pi/2), |deriv g t| := by
    have h := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := deriv g) hθ.2.le
    rwa [hftc, abs_neg] at h
  -- ### the pointwise identity `|g'| = √A √B` on `(θ,π/2)`
  have hident : ∀ t ∈ Set.Ioo θ (Real.pi/2), |deriv g t| = Real.sqrt (A t) * Real.sqrt (B t) := by
    intro t ht
    have hs : 0 < Real.sin (2*t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1, hθ.1]) (by linarith [ht.2])
    have hkey : Work.FTS.EllipticEst.RPFresh.sg t * (Real.sin (2*t))^(Work.Spaces.eta) = 1 := by
      rw [Work.FTS.EllipticEst.RPFresh.sg_def, ← Real.rpow_add hs]
      simp
    have hAB : A t * B t = (deriv g t)^2 := by
      simp only [hA, hB]
      rw [show Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2
            * (Real.sin (2*t))^(Work.Spaces.eta)
          = (deriv g t)^2 * (Work.FTS.EllipticEst.RPFresh.sg t
            * (Real.sin (2*t))^(Work.Spaces.eta)) by ring,
        hkey, mul_one]
    rw [show |deriv g t| = Real.sqrt ((deriv g t)^2) from
          (Real.sqrt_sq_eq_abs (deriv g t)).symm,
      ← hAB, Real.sqrt_mul (hAnneg t ht)]
  have hstep : |g θ| ≤ ∫ t in Set.Ioo θ (Real.pi/2), Real.sqrt (A t) * Real.sqrt (B t) := by
    calc |g θ| ≤ ∫ t in θ..(Real.pi/2), |deriv g t| := habs
      _ = ∫ t in Set.Ioc θ (Real.pi/2), |deriv g t| :=
            intervalIntegral.integral_of_le hθ.2.le
      _ = ∫ t in Set.Ioo θ (Real.pi/2), |deriv g t| :=
            setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume)).symm
      _ = ∫ t in Set.Ioo θ (Real.pi/2), Real.sqrt (A t) * Real.sqrt (B t) :=
            setIntegral_congr_fun measurableSet_Ioo hident
  -- ### integrability and measurability of the two factors on `(θ,π/2)`
  have hAint_Ioo : IntegrableOn A (Set.Ioo θ (Real.pi/2)) :=
    hint.mono_set (fun t ht => ⟨lt_trans hθ.1 ht.1, ht.2⟩)
  have hA_sq : IntegrableOn (fun t => (Real.sqrt (A t))^2) (Set.Ioo θ (Real.pi/2)) :=
    hAint_Ioo.congr_fun_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact (Real.sq_sqrt (hAnneg t ht)).symm)
  have hA_aesm : AEStronglyMeasurable (fun t => Real.sqrt (A t))
      (volume.restrict (Set.Ioo θ (Real.pi/2))) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hAint_Ioo.aestronglyMeasurable
  have hBcont : Continuous (fun t : ℝ => (Real.sin (2*t))^(Work.Spaces.eta)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
      (fun x => Or.inr Work.Spaces.eta_pos.le)
  have hB_II : IntervalIntegrable (fun t : ℝ => (Real.sin (2*t))^(Work.Spaces.eta))
      volume θ (Real.pi/2) := hBcont.intervalIntegrable _ _
  have hBint_Ioc : IntegrableOn B (Set.Ioc θ (Real.pi/2)) := by
    rw [intervalIntegrable_iff, uIoc_of_le hθ.2.le] at hB_II
    exact hB_II
  have hBint_Ioo : IntegrableOn B (Set.Ioo θ (Real.pi/2)) :=
    hBint_Ioc.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume))
  have hB_sq : IntegrableOn (fun t => (Real.sqrt (B t))^2) (Set.Ioo θ (Real.pi/2)) :=
    hBint_Ioo.congr_fun_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact (Real.sq_sqrt (hBnneg t ht)).symm)
  have hB_aesm : AEStronglyMeasurable (fun t => Real.sqrt (B t))
      (volume.restrict (Set.Ioo θ (Real.pi/2))) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hBint_Ioo.aestronglyMeasurable
  -- ### Cauchy–Schwarz
  have hCS := integral_mul_sq_le_sq_mul_sq (volume.restrict (Set.Ioo θ (Real.pi/2)))
    (f := fun t => Real.sqrt (A t)) (h := fun t => Real.sqrt (B t))
    hA_aesm hB_aesm hA_sq hB_sq
  have hAeq : ∫ t in Set.Ioo θ (Real.pi/2), (Real.sqrt (A t))^2
      = ∫ t in Set.Ioo θ (Real.pi/2), A t :=
    setIntegral_congr_fun measurableSet_Ioo (fun t ht => Real.sq_sqrt (hAnneg t ht))
  have hBeq : ∫ t in Set.Ioo θ (Real.pi/2), (Real.sqrt (B t))^2
      = ∫ t in Set.Ioo θ (Real.pi/2), B t :=
    setIntegral_congr_fun measurableSet_Ioo (fun t ht => Real.sq_sqrt (hBnneg t ht))
  have hCS' : (∫ t in Set.Ioo θ (Real.pi/2), Real.sqrt (A t) * Real.sqrt (B t))^2
      ≤ (∫ t in Set.Ioo θ (Real.pi/2), A t) * (∫ t in Set.Ioo θ (Real.pi/2), B t) := by
    rw [hAeq, hBeq] at hCS
    exact hCS
  -- ### assembly
  have hsq : (g θ)^2
      ≤ (∫ t in Set.Ioo θ (Real.pi/2), Real.sqrt (A t) * Real.sqrt (B t))^2 := by
    rw [← sq_abs (g θ)]
    exact pow_le_pow_left₀ (abs_nonneg (g θ)) hstep 2
  have hfin : (g θ)^2
      ≤ (∫ t in Set.Ioo θ (Real.pi/2), A t) * (∫ t in Set.Ioo θ (Real.pi/2), B t) :=
    hsq.trans hCS'
  have hconvA : ∫ t in Set.Ioo θ (Real.pi/2), A t = ∫ t in θ..(Real.pi/2), A t :=
    (setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume))).trans
      (intervalIntegral.integral_of_le hθ.2.le).symm
  have hconvB : ∫ t in Set.Ioo θ (Real.pi/2), B t = ∫ t in θ..(Real.pi/2), B t :=
    (setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume))).trans
      (intervalIntegral.integral_of_le hθ.2.le).symm
  rw [hconvA, hconvB] at hfin
  exact hfin

/-- Mirror of the proved `Work.RPFresh.slice_sq_le` at the *right* endpoint `π/2`.

If `g` is `C¹` on `(0,π/2)`, tends to `0` at `(π/2)⁻`, and `∫ (g')² σ < ∞` on `(0,π/2)` with
`σ θ = sin(2θ)^{-η}`, `η = 99/100`, then for every `θ ∈ (0,π/2)`

`g θ ^ 2 ≤ (∫_{(0,π/2)} σ (g')²) · 2^η (π/2 - θ)^{1+η} / (1+η)`.

Route: the reflection `θ ↦ π/2 - θ` of `slice_sq_le`, or a verbatim mirror of that file's proof
with the right endpoint in place of `0`.  The sibling `slice_eq_sq_le.lean` in the same directory
(`Submission/Work/RPFresh/slice_sq_le.lean`) contains the whole left-endpoint argument, including
`Work.RPFresh.slice_sq_le_core` (FTC `∫_0^θ g' = g θ` from the trace hypothesis, weighted
Cauchy–Schwarz against `σ^{-1} = sin(2t)^η`, and the elementary bound
`∫_0^θ sin(2t)^η dt ≤ 2^η θ^{1+η}/(1+η)` from `Work.RPFresh.integral_sin_two_rpow_le`).  For the
right endpoint use `∫_θ^{π/2} (g')² σ ≤ ∫_0^{π/2} (g')² σ`,
`∫_θ^{π/2} sin(2t)^η dt ≤ 2^η (π/2-θ)^{1+η}/(1+η)` (since `sin(2t) = sin(2(π/2-t)) ≤ 2(π/2-t)`)
and `∫_θ^{π/2} g' = -g θ`. -/
theorem slice_sq_le_right (g : ℝ → ℝ) (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi/2)))
    (hg1 : Filter.Tendsto g (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.RPFresh.sg θ * (deriv g θ)^2) (Set.Ioo 0 (Real.pi/2))) :
    ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), (g θ)^2 ≤
      (∫ t in (0:ℝ)..(Real.pi/2), Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2)
        * (2^Work.Spaces.eta * (Real.pi/2 - θ)^(1 + Work.Spaces.eta)
            / (1 + Work.Spaces.eta)) := by
  intro θ hθ
  have hcore := slice_sq_le_core_right g hg hg1 hint hθ
  -- monotonicity of the weighted energy in the slice
  have hIIfull : IntervalIntegrable
      (fun t => Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2) volume
      (0:ℝ) (Real.pi/2) := by
    rw [intervalIntegrable_iff, uIoc_of_le (le_of_lt (by positivity : (0:ℝ) < Real.pi/2))]
    exact hint.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hmono : (∫ t in θ..(Real.pi/2), Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2)
      ≤ (∫ t in (0:ℝ)..(Real.pi/2),
          Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2) := by
    refine integral_mono_interval
      (f := fun t => Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2)
      (c := (0:ℝ)) (a := θ) (b := Real.pi/2) (d := Real.pi/2) (μ := volume)
      hθ.1.le hθ.2.le le_rfl ?_ hIIfull
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])) _) (sq_nonneg _)
  -- the elementary bound on the weight `σ^{-1} = sin(2t)^η`
  have hbnd := integral_sin_two_rpow_le_right (θ := θ) hθ
  have hAnnB : 0 ≤ ∫ t in θ..(Real.pi/2), (Real.sin (2*t))^(Work.Spaces.eta) := by
    rw [intervalIntegral.integral_of_le hθ.2.le]
    exact setIntegral_nonneg measurableSet_Ioc (fun t ht =>
      Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1, hθ.1])
        (by linarith [ht.2])) _)
  have hAnnA : 0 ≤ ∫ t in (0:ℝ)..(Real.pi/2),
      Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2 := by
    rw [intervalIntegral.integral_of_le (le_of_lt (by positivity : (0:ℝ) < Real.pi/2))]
    exact setIntegral_nonneg measurableSet_Ioc (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
        (by linarith [ht.2, Real.pi_pos])) _) (sq_nonneg _))
  exact hcore.trans (mul_le_mul hmono hbnd hAnnB hAnnA)

end Work.RPFresh
