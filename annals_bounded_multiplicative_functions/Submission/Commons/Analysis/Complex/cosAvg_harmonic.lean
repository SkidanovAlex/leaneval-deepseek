import Mathlib.Analysis.Complex.Harmonic.Analytic
import Submission.Commons.Analysis.Complex.cosAvg_analytic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex Metric MeasureTheory Set Topology
open scoped Interval

namespace Commons.Analysis.Complex

/-- The real part of a real-differentiable complex curve is real-differentiable, with
derivative the real part of the complex derivative. -/
private lemma hasDerivAt_re {F : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hF : HasDerivAt F f' x) :
    HasDerivAt (fun t : ℝ => (F t).re) (Complex.re f') x := by
  have hFd : HasFDerivAt F (ContinuousLinearMap.toSpanSingleton ℝ f') x := hF.hasFDerivAt
  have hc : HasFDerivAt (fun t : ℝ => Complex.re (F t))
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).comp (ContinuousLinearMap.toSpanSingleton ℝ f')) x := by
    exact (ContinuousLinearMap.hasFDerivAt (Complex.reCLM : ℂ →L[ℝ] ℝ)).comp x hFd
  simpa [Complex.reCLM_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hc.hasDerivAt

theorem cosAvg_harmonic {h : ℂ → ℝ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hh : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall a |R|)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * h (circleMap a R θ)) =
      Real.pi * R * deriv (fun t : ℝ => h (a + (t : ℂ))) 0 := by
  -- R > 0, so |R| = R
  have hhR : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall a R) := by
    simpa [abs_of_pos hR] using hh
  -- Harmonicity is open: h is harmonic on a slightly larger open ball `ball a (R + e)`.
  have hhS : Metric.closedBall a R ⊆ {x : ℂ | InnerProductSpace.HarmonicAt h x} := by
    intro x hx
    exact hhR x hx
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall a R).exists_thickening_subset_open
    (InnerProductSpace.isOpen_setOfPred_harmonicAt h) hhS
  have hBall : Metric.ball a (e + R) ⊆ {x : ℂ | InnerProductSpace.HarmonicAt h x} := by
    simpa [thickening_closedBall h₁e (le_of_lt hR) a] using h₂e
  have hBall' : Metric.ball a (R + e) ⊆ {x : ℂ | InnerProductSpace.HarmonicAt h x} := by
    simpa [add_comm] using hBall
  have hhball : InnerProductSpace.HarmonicOnNhd h (Metric.ball a (R + e)) := by
    intro x hx
    exact hBall' hx
  -- Represent h = Re F with F analytic on that open ball.
  obtain ⟨F, hF_an, hF_eq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f := h) (z := a)
      (R := R + e) hhball
  -- restrict F-analyticity to the closed ball of radius R
  have hF_closed : AnalyticOnNhd ℂ F (Metric.closedBall a R) :=
    hF_an.mono (Metric.closedBall_subset_ball (lt_add_of_pos_right R h₁e))
  -- The cosine average of h over the circle equals that of Re F
  have hcircle : (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * h (circleMap a R θ)) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * Complex.re (F (circleMap a R θ))) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change Real.cos θ * h (circleMap a R θ) =
      Real.cos θ * Complex.re (F (circleMap a R θ))
    have hmem : circleMap a R θ ∈ Metric.ball a (R + e) :=
      (Metric.closedBall_subset_ball (lt_add_of_pos_right R h₁e))
        (circleMap_mem_closedBall a hR.le θ)
    rw [(hF_eq hmem).symm]
  -- the analytic cosine-average lemma
  have havg : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * Complex.re (F (circleMap a R θ))) =
      Real.pi * R * Complex.re (deriv F a) :=
    cosAvg_analytic hR hF_closed
  -- the real derivative of t ↦ h (a + t) at 0 equals Re (deriv F a)
  have hF_deriv : HasDerivAt F (deriv F a) a :=
    (hF_an a (Metric.mem_ball_self (add_pos hR h₁e))).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun z : ℂ => F (a + z)) (deriv F a) 0 := by
    have h0 : HasDerivAt (fun z : ℂ => a + z) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add a
    have hF_deriv0 : HasDerivAt F (deriv F a) (a + 0) := by
      simpa using hF_deriv
    have hcomp' : HasDerivAt (F ∘ (fun z : ℂ => a + z)) (deriv F a) 0 := by
      simpa using (hF_deriv0.comp (0 : ℂ) h0)
    exact hcomp'
  have hcompRe : HasDerivAt (fun t : ℝ => Complex.re (F (a + (t : ℂ))))
      (Complex.re (deriv F a)) 0 := by
    exact hasDerivAt_re (hcomp.comp_ofReal)
  have hagg : (fun t : ℝ => h (a + (t : ℂ))) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => Complex.re (F (a + (t : ℂ)))) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (add_pos hR h₁e)] with t ht
    have ht1 : ‖t‖ < R + e := by simpa using (mem_ball_iff_norm.mp ht)
    have hnorm : ‖(t : ℂ)‖ < R + e := by
      rwa [Complex.norm_real]
    have hmem2 : a + (t : ℂ) ∈ Metric.ball a (R + e) := by
      simpa [mem_ball_iff_norm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hnorm
    exact (hF_eq hmem2).symm
  have hh_deriv : HasDerivAt (fun t : ℝ => h (a + (t : ℂ))) (Complex.re (deriv F a)) 0 :=
    hcompRe.congr_of_eventuallyEq hagg
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * h (circleMap a R θ))
        = Real.pi * R * Complex.re (deriv F a) := by
          rw [hcircle]
          exact havg
    _ = Real.pi * R * deriv (fun t : ℝ => h (a + (t : ℂ))) 0 := by
      rw [hh_deriv.deriv]

end Commons.Analysis.Complex