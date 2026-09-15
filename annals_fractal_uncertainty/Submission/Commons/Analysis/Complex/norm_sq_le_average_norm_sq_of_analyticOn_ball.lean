import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Integral.norm_integral_sq_le_mul_length
import Submission.Commons.MeasureTheory.Integral.norm_integral_sq_le_integral_norm_sq

open MeasureTheory Metric Complex
open scoped Real

namespace Commons.Analysis.Complex

/-- **Sub-mean-value inequality for `‖f‖²`.**  If `f` is complex analytic on the open ball
`Metric.ball z r` and `0 < t < r`, then `‖f z‖²` is bounded by the circle average of
`‖f‖²` over the circle of radius `t` about `z`. -/
private lemma circleAverage_norm_sq_ge_of_analyticAt {f : ℂ → ℂ} {z : ℂ} {r t : ℝ}
    (ht : 0 < t) (htr : t < r)
    (hAt : ∀ x ∈ Metric.ball z r, AnalyticAt ℂ f x) :
    ‖f z‖ ^ 2 ≤ Real.circleAverage (fun w => ‖f w‖ ^ 2) z t := by
  have hdiff : DifferentiableOn ℂ f (Metric.ball z t) := by
    intro x hx
    have hxr : x ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
      exact lt_trans hx htr
    exact (hAt x hxr).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn f (closure (Metric.ball z t)) := by
    rw [closure_ball z ht.ne']
    intro x hx
    have hxr : x ∈ Metric.ball z r := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt hx htr
    exact (hAt x hxr).continuousAt.continuousWithinAt
  have hdcc : DiffContOnCl ℂ f (Metric.ball z t) := ⟨hdiff, hcont⟩
  have hMV : Real.circleAverage f z t = f z := by
    have h := DiffContOnCl.circleAverage (f := f) (c := z) (R := t) ?_
    · simpa using h
    · rw [abs_of_pos ht]; exact hdcc
  -- continuity of the circle parametrisation
  have hIcont : Continuous (fun θ : ℝ => f (circleMap z t θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hmem : circleMap z t θ ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos ht]
      exact htr
    exact (hAt _ hmem).continuousAt.comp (continuous_circleMap z t).continuousAt
  set I : ℂ := ∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap z t θ) with hI
  set J : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap z t θ)‖ ^ 2 with hJ
  have hpi : 0 < 2 * Real.pi := by positivity
  have hCS : ‖I‖ ^ 2 ≤ 2 * Real.pi * J := by
    have h := Commons.Analysis.Integral.norm_integral_sq_le_mul_length (a := 0)
      (b := 2 * Real.pi) (le_of_lt hpi) (f := fun θ => f (circleMap z t θ)) hIcont
    simpa [I, J] using h
  have hnorm : ‖f z‖ ^ 2 = ((2 * Real.pi)⁻¹ * ‖I‖) ^ 2 := by
    rw [← hMV, Real.circleAverage_def, ← hI, norm_smul,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (2 * Real.pi)⁻¹)]
  have hcircle : Real.circleAverage (fun w => ‖f w‖ ^ 2) z t = (2 * Real.pi)⁻¹ * J := by
    rw [Real.circleAverage_def, ← hJ]
    simp [smul_eq_mul]
  rw [hnorm, hcircle]
  calc ((2 * Real.pi)⁻¹ * ‖I‖) ^ 2
      = (2 * Real.pi)⁻¹ ^ 2 * ‖I‖ ^ 2 := by ring
    _ ≤ (2 * Real.pi)⁻¹ ^ 2 * (2 * Real.pi * J) := by
        exact mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = (2 * Real.pi)⁻¹ * J := by
        field_simp

/-- Integral of a `2 * π`-periodic function over `(-π, π)` equals its integral over `(0, 2π)`. -/
private lemma integral_Ioo_neg_pi_pi_eq_interval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : ℝ → E} (hper : Function.Periodic φ (2 * Real.pi)) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, φ θ = ∫ θ in (0 : ℝ)..(2 * Real.pi), φ θ := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (a := -Real.pi) (b := Real.pi))]
  rw [← intervalIntegral.integral_of_le hle]
  have h := hper.intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at h
  exact h

/-- The integral of `g` over the circle of radius `t` about `z`, written as
`2 * π` times the circle average of `g`. -/
private lemma integral_Ioo_circleMap_eq {g : ℂ → ℝ} {z : ℂ} {t : ℝ} :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap z t θ) = 2 * Real.pi * Real.circleAverage g z t := by
  have hper : Function.Periodic (fun θ : ℝ => g (circleMap z t θ)) (2 * Real.pi) :=
    fun θ => by
      show g (circleMap z t (θ + 2 * Real.pi)) = g (circleMap z t θ)
      rw [periodic_circleMap z t θ]
  rw [integral_Ioo_neg_pi_pi_eq_interval hper, Real.circleAverage_def, smul_eq_mul]
  field_simp

/-- **Ball mean-value inequality for the squared modulus.**  If `f` is complex analytic on the
closed ball `Metric.closedBall z r` (`r > 0`), then
`‖f z‖² ≤ (π r²)⁻¹ ∫_{ball z r} ‖f‖²`. -/
theorem norm_sq_le_average_norm_sq_of_analyticOn_ball {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOn ℂ f (Metric.closedBall z r)) :
    ‖f z‖ ^ 2 ≤ (1 / (Real.pi * r ^ 2)) * ∫ w in Metric.ball z r, ‖f w‖ ^ 2 := by
  classical
  -- analyticity (in the strong sense) on the open ball
  have hfn : AnalyticOnNhd ℂ f (Metric.ball z r) :=
    (isOpen_ball.analyticOn_iff_analyticOnNhd).mp (hf.mono ball_subset_closedBall)
  have hAt : ∀ x ∈ Metric.ball z r, AnalyticAt ℂ f x := fun x hx => hfn x hx
  -- the squared modulus
  set g : ℂ → ℝ := fun w => ‖f w‖ ^ 2 with hg
  have hgnn : ∀ w, 0 ≤ g w := fun w => by rw [hg]; positivity
  have hgcont : ContinuousOn g (Metric.closedBall z r) := by
    rw [hg]; exact (hf.continuousOn.norm).pow 2
  obtain ⟨M, hM⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hgcont
  have hMnn : 0 ≤ M := le_trans (norm_nonneg (g z)) (hM z (mem_closedBall_self hr.le))
  have hgle : ∀ w ∈ Metric.closedBall z r, g w ≤ M := fun w hw => by
    rw [← Real.norm_of_nonneg (hgnn w)]; exact hM w hw
  -- the parametrisation of polar coordinates is continuous
  have hΦcont : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    have h : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
        = fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
      funext p
      simpa using Complex.polarCoord_symm_apply p
    rw [h]; fun_prop
  -- translation of the ball to the origin
  set A : ℂ → ℝ := (Metric.ball 0 r).indicator (fun u => g (z + u)) with hA
  have htrans : ∫ w in Metric.ball z r, g w = ∫ u in Metric.ball 0 r, g (z + u) := by
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun w => (Metric.ball z r).indicator g w) z]
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hw : w ∈ Metric.ball 0 r
    · have hw0 : ‖w‖ < r := by rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
      have hw' : w + z ∈ Metric.ball z r := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]; exact hw0
      rw [if_pos hw', if_pos hw, add_comm]
    · have hw0 : ¬ ‖w‖ < r := by rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
      have hw' : w + z ∉ Metric.ball z r := by
        intro h
        exact hw0 (by rwa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] at h)
      rw [if_neg hw', if_neg hw]
  have hAeq : ∫ u in Metric.ball 0 r, g (z + u) = ∫ w, A w := by
    rw [hA]
    exact (MeasureTheory.integral_indicator (f := fun u => g (z + u)) measurableSet_ball).symm
  -- polar coordinates
  set U : Set (ℝ × ℝ) := Set.Ioo 0 r ×ˢ Set.Ioo (-Real.pi) Real.pi with hU
  set F : ℝ × ℝ → ℝ := fun p => p.1 • A (Complex.polarCoord.symm p) with hF
  have hpol : ∫ w, A w = ∫ p in Complex.polarCoord.target, F p := by
    rw [hF]
    exact (Complex.integral_comp_polarCoord_symm (E := ℝ) A).symm
  have hUtarget : U ⊆ Complex.polarCoord.target := by
    rw [hU, Complex.polarCoord_target]
    exact Set.prod_mono Set.Ioo_subset_Ioi_self (subset_refl _)
  have hUmeas : MeasurableSet U := by
    rw [hU]; exact (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  have hsupp : ∀ p ∈ Complex.polarCoord.target, p ∉ U → F p = 0 := by
    intro p hp hpU
    change p.1 • A (Complex.polarCoord.symm p) = 0
    have hp' : p.1 ∈ Set.Ioi 0 ∧ p.2 ∈ Set.Ioo (-Real.pi) Real.pi := by
      have h := hp
      rw [Complex.polarCoord_target, Set.mem_prod] at h
      exact h
    have hnot : Complex.polarCoord.symm p ∉ Metric.ball 0 r := by
      intro hmem
      apply hpU
      rw [hU, Set.mem_prod]
      refine ⟨⟨hp'.1, ?_⟩, hp'.2⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_polarCoord_symm] at hmem
      rwa [abs_of_pos hp'.1] at hmem
    rw [smul_eq_mul, hA, Set.indicator_of_notMem hnot, mul_zero]
  have hrestr : ∫ p in Complex.polarCoord.target, F p = ∫ p in U, F p := by
    have hcongr : ∫ p in Complex.polarCoord.target, F p
        = ∫ p in Complex.polarCoord.target, U.indicator F p := by
      apply MeasureTheory.setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
      intro p hp
      by_cases hUp : p ∈ U
      · rw [Set.indicator_of_mem hUp]
      · rw [Set.indicator_of_notMem hUp, hsupp p hp hUp]
    rw [hcongr, MeasureTheory.setIntegral_indicator hUmeas,
      Set.inter_eq_right.mpr hUtarget]
  -- integrability of the polar integrand
  have hUfin : ((volume : Measure ℝ).prod (volume : Measure ℝ))
      (Set.Ioo 0 r ×ˢ Set.Ioo (-Real.pi) Real.pi) < ⊤ := by
    rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hFmeas : AEStronglyMeasurable F
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Set.Ioo 0 r ×ˢ Set.Ioo (-Real.pi) Real.pi)) := by
    have hmap : Set.MapsTo (fun p : ℝ × ℝ => z + Complex.polarCoord.symm p)
        (Set.Ioo 0 r ×ˢ Set.Ioo (-Real.pi) Real.pi) (Metric.ball z r) := by
      intro p hp
      rw [Set.mem_prod] at hp
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_polarCoord_symm,
        abs_of_pos hp.1.1]
      exact hp.1.2
    have hcontU : ContinuousOn (fun p : ℝ × ℝ => f (z + Complex.polarCoord.symm p))
        (Set.Ioo 0 r ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
      (hfn.continuousOn).comp (continuous_const.add hΦcont).continuousOn hmap
    have hstep : AEStronglyMeasurable (fun p : ℝ × ℝ => f (z + Complex.polarCoord.symm p))
        (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (Set.Ioo 0 r ×ˢ Set.Ioo (-Real.pi) Real.pi)) :=
      hcontU.aestronglyMeasurable ((isOpen_Ioo.prod isOpen_Ioo).measurableSet)
    have hstep2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => p.1 * ‖f (z + Complex.polarCoord.symm p)‖ ^ 2)
        (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (Set.Ioo 0 r ×ˢ Set.Ioo (-Real.pi) Real.pi)) :=
      (continuous_fst.aestronglyMeasurable.mul ((hstep.norm).pow 2))
    refine hstep2.congr ?_
    apply MeasureTheory.ae_restrict_of_forall_mem ((isOpen_Ioo.prod isOpen_Ioo).measurableSet)
    intro p hp
    change p.1 * ‖f (z + Complex.polarCoord.symm p)‖ ^ 2
      = p.1 • A (Complex.polarCoord.symm p)
    rw [Set.mem_prod] at hp
    rw [smul_eq_mul, hA]
    have hmem : Complex.polarCoord.symm p ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_polarCoord_symm,
        abs_of_pos hp.1.1]
      exact hp.1.2
    rw [Set.indicator_of_mem hmem]
  have hFbound : ∀ᵐ p ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Set.Ioo 0 r ×ˢ Set.Ioo (-Real.pi) Real.pi)), ‖F p‖ ≤ r * M := by
    apply MeasureTheory.ae_restrict_of_forall_mem ((isOpen_Ioo.prod isOpen_Ioo).measurableSet)
    intro p hp
    change ‖p.1 • A (Complex.polarCoord.symm p)‖ ≤ r * M
    rw [Set.mem_prod] at hp
    rw [smul_eq_mul, norm_mul, Real.norm_of_nonneg hp.1.1.le, hA]
    have hmem : Complex.polarCoord.symm p ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_polarCoord_symm,
        abs_of_pos hp.1.1]
      exact hp.1.2
    rw [Set.indicator_of_mem hmem, Real.norm_of_nonneg (hgnn _)]
    have hz : z + Complex.polarCoord.symm p ∈ Metric.closedBall z r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_polarCoord_symm,
        abs_of_pos hp.1.1]
      exact hp.1.2.le
    exact mul_le_mul hp.1.2.le (hgle _ hz) (hgnn _) hr.le
  have hInt : IntegrableOn F (Set.Ioo 0 r ×ˢ Set.Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    IntegrableOn.of_bound hUfin hFmeas (r * M) hFbound
  have hFub : ∫ p in U, F p
      = ∫ t in Set.Ioo 0 r, ∫ θ in Set.Ioo (-Real.pi) Real.pi, F (t, θ) := by
    rw [hU, Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.setIntegral_prod F hInt
  -- evaluate the inner integral
  have hinner : ∫ t in Set.Ioo 0 r, ∫ θ in Set.Ioo (-Real.pi) Real.pi, F (t, θ)
      = ∫ t in Set.Ioo 0 r, t * (∫ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap z t θ)) := by
    apply MeasureTheory.setIntegral_congr_fun isOpen_Ioo.measurableSet
    intro t ht
    change (∫ θ in Set.Ioo (-Real.pi) Real.pi, F (t, θ))
        = t * (∫ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap z t θ))
    have ht1 : 0 < t := ht.1
    have ht2 : t < r := ht.2
    have hpt : (∫ θ in Set.Ioo (-Real.pi) Real.pi, F (t, θ))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi, t * g (circleMap z t θ) := by
      apply MeasureTheory.setIntegral_congr_fun isOpen_Ioo.measurableSet
      intro θ hθ
      change F (t, θ) = t * g (circleMap z t θ)
      rw [hF]
      change t • A (Complex.polarCoord.symm (t, θ)) = t * g (circleMap z t θ)
      rw [smul_eq_mul, hA]
      have hmem : Complex.polarCoord.symm (t, θ) ∈ Metric.ball 0 r := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_polarCoord_symm,
          abs_of_pos ht1]
        exact ht2
      rw [Set.indicator_of_mem hmem]
      have harg : z + Complex.polarCoord.symm (t, θ) = circleMap z t θ := by
        have h1 := Complex.polarCoord_symm_apply (t, θ)
        unfold circleMap
        rw [Complex.exp_ofReal_mul_I, h1]
      rw [harg]
    rw [hpt]
    exact MeasureTheory.integral_const_mul t (fun θ => g (circleMap z t θ))
  -- replace the inner integral by `2 π` times the circle average
  have hinner2 : ∫ t in Set.Ioo 0 r, t * (∫ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap z t θ))
      = ∫ t in Set.Ioo 0 r, t * (2 * Real.pi * Real.circleAverage g z t) := by
    apply MeasureTheory.setIntegral_congr_fun isOpen_Ioo.measurableSet
    intro t _
    change t * (∫ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap z t θ))
        = t * (2 * Real.pi * Real.circleAverage g z t)
    rw [integral_Ioo_circleMap_eq]
  -- analytic ingredients for the monotonicity step
  have hca_cont : ContinuousOn (Real.circleAverage g z) (Set.Ioo 0 r) := by
    refine Real.ContinuousOn.circleAverage (f := g) (s := Set.Ioo 0 r) (c := z) ?_ ?_
    · intro x hx
      have hxr : x ∈ Metric.ball z r := by
        rw [Metric.mem_ball, dist_eq_norm]; exact hx.2
      exact ((hAt x hxr).continuousAt.norm.pow 2).continuousWithinAt
    · intro ρ hρ; exact hρ.1.le
  have hca_nonneg : ∀ t, 0 ≤ Real.circleAverage g z t := by
    intro t
    rw [Real.circleAverage_def, smul_eq_mul]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg (by positivity) (fun u _ => hgnn _))
  have hca_le : ∀ t ∈ Set.Ioo 0 r, Real.circleAverage g z t ≤ M := by
    intro t ht
    refine Real.circleAverage_mono_on_of_le_circle (c := z) (R := t) ?_ ?_
    · refine ContinuousOn.circleIntegrable' ?_
      intro x hx
      have hxr : x ∈ Metric.ball z r := by
        rw [Metric.mem_sphere, dist_eq_norm] at hx
        rw [Metric.mem_ball, dist_eq_norm, hx, abs_of_pos ht.1]
        exact ht.2
      exact ((hAt x hxr).continuousAt.norm.pow 2).continuousWithinAt
    · intro x hx
      rw [Metric.mem_sphere, dist_eq_norm] at hx
      exact hgle x (by
        rw [Metric.mem_closedBall, dist_eq_norm, hx, abs_of_pos ht.1]; exact ht.2.le)
  have hcmp : ∫ t in Set.Ioo 0 r, t * (2 * Real.pi * g z)
      ≤ ∫ t in Set.Ioo 0 r, t * (2 * Real.pi * Real.circleAverage g z t) := by
    have hf_int : IntegrableOn (fun t : ℝ => t * (2 * Real.pi * g z)) (Set.Ioo 0 r) volume := by
      refine IntegrableOn.of_bound ?_ ?_ (r * (2 * Real.pi * M)) ?_
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      · exact ((continuous_id.continuousOn.mul continuousOn_const).aestronglyMeasurable
          isOpen_Ioo.measurableSet)
      · apply MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioo.measurableSet
        intro t ht
        rw [norm_mul, norm_mul, Real.norm_of_nonneg ht.1.le,
          Real.norm_of_nonneg (le_of_lt (by positivity : (0:ℝ) < 2 * Real.pi)),
          Real.norm_of_nonneg (hgnn z)]
        exact mul_le_mul ht.2.le
          (mul_le_mul_of_nonneg_left (hgle z (mem_closedBall_self hr.le)) (by positivity))
          (by positivity) hr.le
    have hg_int : IntegrableOn (fun t : ℝ => t * (2 * Real.pi * Real.circleAverage g z t))
        (Set.Ioo 0 r) volume := by
      refine IntegrableOn.of_bound ?_ ?_ (r * (2 * Real.pi * M)) ?_
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      · exact ((continuous_id.continuousOn.mul (continuousOn_const.mul hca_cont)).aestronglyMeasurable
          isOpen_Ioo.measurableSet)
      · apply MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioo.measurableSet
        intro t ht
        have hca0 := hca_nonneg t
        have hcaM := hca_le t ht
        rw [norm_mul, norm_mul, Real.norm_of_nonneg ht.1.le,
          Real.norm_of_nonneg (le_of_lt (by positivity : (0:ℝ) < 2 * Real.pi)),
          Real.norm_of_nonneg hca0]
        exact mul_le_mul ht.2.le (mul_le_mul_of_nonneg_left hcaM (by positivity))
          (mul_nonneg (by positivity) hca0) hr.le
    refine MeasureTheory.setIntegral_mono_on hf_int hg_int isOpen_Ioo.measurableSet ?_
    intro t ht
    have hsub : g z ≤ Real.circleAverage g z t := by
      have := circleAverage_norm_sq_ge_of_analyticAt (f := f) (z := z) (r := r) ht.1 ht.2 hAt
      simpa [hg] using this
    have hpi2 : 0 < 2 * Real.pi := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub hpi2.le) ht.1.le
  have hRHS : ∫ t in Set.Ioo 0 r, t * (2 * Real.pi * g z) = Real.pi * r ^ 2 * g z := by
    rw [show (fun t : ℝ => t * (2 * Real.pi * g z))
        = fun t : ℝ => (2 * Real.pi * g z) * t by funext t; ring]
    rw [MeasureTheory.integral_const_mul]
    have hid : ∫ t in Set.Ioo 0 r, t = r ^ 2 / 2 := by
      rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (a := 0) (b := r))]
      rw [← intervalIntegral.integral_of_le hr.le, integral_id]
      ring
    rw [hid]; ring
  -- combine
  have hkey : Real.pi * r ^ 2 * g z ≤ ∫ w in Metric.ball z r, g w := by
    rw [htrans, hAeq]
    have hle : ∫ t in Set.Ioo 0 r, t * (2 * Real.pi * g z) ≤ ∫ w, A w := by
      rw [hpol, hrestr, hFub, hinner, hinner2]
      exact hcmp
    rw [hRHS] at hle
    exact hle
  have hkey' : Real.pi * r ^ 2 * ‖f z‖ ^ 2 ≤ ∫ w in Metric.ball z r, ‖f w‖ ^ 2 := by
    simpa [hg] using hkey
  have hpos : (0 : ℝ) < 1 / (Real.pi * r ^ 2) := by positivity
  calc ‖f z‖ ^ 2 = (1 / (Real.pi * r ^ 2)) * (Real.pi * r ^ 2 * ‖f z‖ ^ 2) := by
        field_simp
    _ ≤ (1 / (Real.pi * r ^ 2)) * ∫ w in Metric.ball z r, ‖f w‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hkey' hpos.le

end Commons.Analysis.Complex