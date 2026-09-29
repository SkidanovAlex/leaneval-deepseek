import Mathlib
import Submission.Work.Holonomy3.jensen_mean_ineq

/-!
# The smoothed Jensen inequality

For `f` analytic on a neighbourhood of the closed unit ball and `ε > 0`,

`log (‖f 0‖ + ε) ≤ ⨍ log (‖f‖ + ε)`

where the average is taken over the unit circle, parametrised by `t ↦ exp (2 π i t)`.

The proof shifts `f` by a unimodular constant `ε c` chosen so that `‖f 0 + ε c‖ = ‖f 0‖ + ε`,
applies Jensen's mean value inequality (`jensen_mean_ineq`) to the shifted function, and compares
the two circle averages.  The two integrands agree except on the (discrete) zero set of the shifted
function on the circle, which is taken care of by `circleAverage_congr_codiscreteWithin`.
-/

namespace Work.Holonomy3

open MeasureTheory Filter Topology
open scoped Real

/-- The `Real.circleAverage` over the unit circle, written against the parametrisation
`t ↦ exp (2 π i t)`. -/
lemma circleAverage_unit_eq_integral (F : ℂ → ℝ) :
    Real.circleAverage F 0 1
      = ∫ t in (0 : ℝ)..1, F (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) := by
  rw [Real.circleAverage_def]
  have hmap : ∀ θ : ℝ, circleMap (0 : ℂ) 1 θ = Complex.exp ((θ : ℂ) * Complex.I) :=
    fun θ => by simp [circleMap]
  simp only [hmap]
  have key := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (c := 2 * Real.pi)
    (fun θ : ℝ => F (Complex.exp ((θ : ℂ) * Complex.I))) (by positivity)
  rw [mul_zero, mul_one] at key
  rw [← key]
  apply intervalIntegral.integral_congr
  intro t _
  push_cast
  ring_nf

/-- The norm of a real number, viewed as a complex number. -/
lemma norm_complex_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [show (r : ℂ) = RCLike.ofReal r from rfl, RCLike.norm_ofReal]

/-- Zeros of a nonzero analytic function on the unit circle are isolated: the complement of the
zero set is `codiscreteWithin` the unit circle. -/
lemma analytic_zero_compl_mem_codiscreteWithin_sphere (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall 0 1)) (hg0 : g 0 ≠ 0) :
    {z : ℂ | g z ≠ 0} ∈ Filter.codiscreteWithin (Metric.sphere (0 : ℂ) 1) := by
  have h1 : {z : ℂ | g z ≠ 0} ∈ Filter.codiscreteWithin (Metric.closedBall (0 : ℂ) 1) := by
    rcases hg.eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_closedBall (0 : ℂ) 1).isPreconnected with hzero | hne
    · exact absurd (hzero (x := (0 : ℂ)) (by simp [Metric.mem_closedBall])) hg0
    · exact hne
  rw [mem_codiscreteWithin] at h1 ⊢
  intro x hx
  exact (h1 x (Metric.sphere_subset_closedBall hx)).mono_right
    (Filter.principal_mono.mpr (Set.sdiff_subset_sdiff_left Metric.sphere_subset_closedBall))

theorem smoothed_jensen (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    Real.log (‖f 0‖ + ε) ≤
      ∫ t : ℝ, Real.log (‖f (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))‖ + ε)
        ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) := by
  -- The unimodular constant `c` is chosen so that `f 0` and `ε * c` are positively aligned.
  set c : ℂ := if f 0 = 0 then 1 else ((‖f 0‖ : ℝ) : ℂ)⁻¹ * f 0 with hc
  have hcnorm : ‖c‖ = 1 := by
    rw [hc]
    split_ifs with h
    · simp
    · have hr : (0 : ℝ) < ‖f 0‖ := norm_pos_iff.mpr h
      rw [norm_mul, norm_inv, norm_complex_ofReal, abs_of_pos hr]
      exact inv_mul_cancel₀ (ne_of_gt hr)
  set g : ℂ → ℂ := fun z => f z + (ε : ℂ) * c with hg_def
  have hg0norm : ‖g 0‖ = ‖f 0‖ + ε := by
    simp only [hg_def]
    rw [hc]
    split_ifs with h
    · rw [h, zero_add, mul_one, norm_zero, zero_add, norm_complex_ofReal, abs_of_pos hε]
    · have hr : (0 : ℝ) < ‖f 0‖ := norm_pos_iff.mpr h
      have key : f 0 + (ε : ℂ) * (((‖f 0‖ : ℝ) : ℂ)⁻¹ * f 0)
          = (((1 + ε / ‖f 0‖ : ℝ)) : ℂ) * f 0 := by
        push_cast
        ring
      rw [key, norm_mul, norm_complex_ofReal]
      have hpos : (0 : ℝ) ≤ 1 + ε / ‖f 0‖ := by positivity
      rw [abs_of_nonneg hpos, add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hr)]
  have hg : AnalyticOnNhd ℂ g (Metric.closedBall 0 1) := by
    rw [hg_def]
    exact hf.add analyticOnNhd_const
  have hg0ne : g 0 ≠ 0 := by
    rw [← norm_ne_zero_iff, hg0norm]
    positivity
  -- Jensen's mean value inequality for the shifted function.
  have hJ := jensen_mean_ineq g 1 (by norm_num) hg hg0ne
  -- The comparison function.
  set U : ℂ → ℝ := fun z => Real.log (‖f z‖ + ε) with hU
  have hUcont : ContinuousOn U (Metric.closedBall (0 : ℂ) 1) := by
    rw [hU]
    exact ((hf.continuousOn.norm).add continuousOn_const).log (fun z _ => by
      have : (0 : ℝ) < ‖f z‖ + ε := by positivity
      exact ne_of_gt this)
  have hUint : CircleIntegrable U 0 1 := by
    rw [circleIntegrable_def]
    have hmapsto : Set.MapsTo (circleMap (0 : ℂ) 1) Set.univ (Metric.closedBall (0 : ℂ) 1) :=
      fun θ _ => by simp
    have hcomp : ContinuousOn (fun θ : ℝ => U (circleMap (0 : ℂ) 1 θ))
        (Set.uIcc 0 (2 * Real.pi)) :=
      (hUcont.comp (continuous_circleMap (0 : ℂ) 1).continuousOn hmapsto).mono (Set.subset_univ _)
    exact hcomp.intervalIntegrable
  have hGint : CircleIntegrable (fun z => Real.log ‖g z‖) 0 1 := by
    refine MeromorphicOn.circleIntegrable_log_norm ?_
    simpa using (hg.mono Metric.sphere_subset_closedBall).meromorphicOn
  -- The comparison function modified on the zero set of `g`.
  set W : ℂ → ℝ := fun z => if g z = 0 then U z else Real.log ‖g z‖ with hW
  have hcodisc : {z : ℂ | g z ≠ 0} ∈ Filter.codiscreteWithin (Metric.sphere (0 : ℂ) 1) :=
    analytic_zero_compl_mem_codiscreteWithin_sphere g hg hg0ne
  have hWG : W =ᶠ[Filter.codiscreteWithin (Metric.sphere (0 : ℂ) 1)]
      (fun z => Real.log ‖g z‖) := by
    filter_upwards [hcodisc] with z hz
    rw [hW]
    simp only [if_neg hz]
  have hWU : ∀ z ∈ Metric.sphere (0 : ℂ) 1, W z ≤ U z := by
    intro z _
    rw [hW]
    by_cases hgz : g z = 0
    · simp [hgz]
    · simp only [if_neg hgz]
      apply Real.log_le_log
      · exact norm_pos_iff.mpr hgz
      · simp only [hg_def]
        have hεnorm : ‖(ε : ℂ)‖ = ε := by rw [norm_complex_ofReal, abs_of_pos hε]
        calc ‖f z + (ε : ℂ) * c‖ ≤ ‖f z‖ + ‖(ε : ℂ) * c‖ := norm_add_le _ _
          _ = ‖f z‖ + ε * ‖c‖ := by rw [norm_mul, hεnorm]
          _ = ‖f z‖ + ε := by rw [hcnorm, mul_one]
  have hWint : CircleIntegrable W 0 1 :=
    CircleIntegrable.congr_codiscreteWithin (by simpa using hWG.symm) hGint
  have hmono : Real.circleAverage W 0 1 ≤ Real.circleAverage U 0 1 :=
    Real.circleAverage_mono hWint hUint (fun z hz => hWU z (by simpa using hz))
  have heq : Real.circleAverage (fun z => Real.log ‖g z‖) 0 1 = Real.circleAverage W 0 1 :=
    Real.circleAverage_congr_codiscreteWithin (by simpa using hWG.symm) (by norm_num)
  have hmain : Real.log ‖g 0‖ ≤ Real.circleAverage U 0 1 :=
    hJ.trans (heq.symm ▸ hmono)
  -- Identify the circle average with the integral against `volume.restrict (Icc 0 1)`.
  have hconv : Real.circleAverage U 0 1
      = ∫ t : ℝ, Real.log (‖f (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))‖ + ε)
          ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) := by
    rw [circleAverage_unit_eq_integral U]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← hg0norm, ← hconv]
  exact hmain

end Work.Holonomy3
