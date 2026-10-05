import Mathlib
import Submission.Work.RPB.B1.AreaDefs
import Submission.Work.RPB.B1.AreaPosDefs
import Submission.Work.RPB.B1.polarKernel
import Submission.Work.RPB.B1.kernelSwap
import Submission.Work.RPB.B1.thetaIntegral
import Submission.Work.RPB.B1.remainderTendsto

set_option autoImplicit false

noncomputable section

open scoped ContDiff Interval
open MeasureTheory

namespace Work.RPB.B1

/-! ## The elementary angle integrals -/

/-- `∫_0^{2π} Im (C e^{-iθ}) dθ = 0`. -/
theorem thetaIntegralSin (C : ℂ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), (C * Complex.exp (-(θ : ℂ) * Complex.I)).im = 0 := by
  have hexp : ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(θ : ℂ) * Complex.I) = 0 := by
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I) * Complex.I)
          (Complex.exp (-(θ : ℂ) * Complex.I)) θ := by
      intro θ _
      have h1 : HasDerivAt (fun t : ℝ => (-(t : ℂ)) * Complex.I) ((-1 : ℂ) * Complex.I) θ := by
        simpa using ((hasDerivAt_id (θ : ℝ)).ofReal_comp.neg.mul_const Complex.I)
      have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((-(t : ℂ)) * Complex.I))
          (Complex.exp ((-(θ : ℂ)) * Complex.I) * ((-1 : ℂ) * Complex.I)) θ :=
        (Complex.hasDerivAt_exp ((-(θ : ℂ)) * Complex.I)).comp θ h1
      have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((-(t : ℂ)) * Complex.I) * Complex.I)
          (Complex.exp ((-(θ : ℂ)) * Complex.I) * ((-1 : ℂ) * Complex.I) * Complex.I) θ :=
        h2.mul_const Complex.I
      have hv : Complex.exp ((-(θ : ℂ)) * Complex.I) * ((-1 : ℂ) * Complex.I) * Complex.I
          = Complex.exp ((-(θ : ℂ)) * Complex.I) := by
        rw [mul_assoc, show ((-1 : ℂ) * Complex.I) * Complex.I = 1 by
          rw [mul_assoc, Complex.I_mul_I]; ring, mul_one]
      simpa only [hv] using h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (u := fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I))
        (by fun_prop) 0 (2 * Real.pi))]
    have h2pi : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
      rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    have hA : Complex.exp (-(↑(2 * Real.pi) : ℂ) * Complex.I) = 1 := by
      have : (-(↑(2 * Real.pi) : ℂ)) * Complex.I = -(2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      rw [this, h2pi]
    have hB : Complex.exp (-(↑(0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
    rw [hA, hB]; ring
  have hI : IntervalIntegrable (fun θ : ℝ => C * Complex.exp (-(θ : ℂ) * Complex.I)) volume
      (0 : ℝ) (2 * Real.pi) := Continuous.intervalIntegrable (by fun_prop) _ _
  simp only [← Complex.imCLM_apply]
  rw [ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hI]
  rw [intervalIntegral.integral_const_mul, hexp, mul_zero, Complex.imCLM_apply, Complex.zero_im]

/-! ## Boundedness of a periodic continuous curve -/

/-- A continuous, `2π`-periodic curve is bounded. -/
lemma exists_bound_periodic (u : ℝ → ℂ) (hu : Continuous u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) : ∃ M : ℝ, ∀ t, ‖u t‖ ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    ((isCompact_Icc.image_of_continuousOn hu.continuousOn)).isBounded
  refine ⟨M, fun t => ?_⟩
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  set k : ℤ := ⌊t / (2 * Real.pi)⌋ with hk
  set s : ℝ := t - (k : ℝ) * (2 * Real.pi) with hs
  have hs_mem : s ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    constructor
    · have h := Int.floor_le (t / (2 * Real.pi))
      have h' : ((k : ℝ)) * (2 * Real.pi) ≤ t := by
        rw [hk]
        exact (le_div_iff₀ h2pi).mp h
      rw [hs]; linarith
    · have h := Int.lt_floor_add_one (t / (2 * Real.pi))
      have h' : t < ((k : ℝ) + 1) * (2 * Real.pi) := by
        rw [hk]
        rw [div_lt_iff₀ h2pi] at h
        linarith
      rw [hs]; linarith
  have hper' : Function.Periodic u (2 * Real.pi) := hper
  have hshift := hper'.zsmul k s
  have hst : s + (k : ℝ) * (2 * Real.pi) = t := by rw [hs]; ring
  have hut : u t = u s := by
    rw [← hst]
    simpa [zsmul_eq_mul] using hshift
  rw [hut]
  exact hM (u s) ⟨s, hs_mem, rfl⟩

/-! ## Splitting a double interval integral of a pointwise sum -/

/-- Additivity of the double interval integral for continuous integrands. -/
lemma double_integral_add (F G : ℝ → ℝ → ℝ)
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi), (F t θ + G t θ))
      = (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi), F t θ)
        + (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi), G t θ) := by
  have hFt : ∀ t, Continuous fun θ : ℝ => F t θ :=
    fun t => hF.comp (continuous_const.prodMk continuous_id)
  have hGt : ∀ t, Continuous fun θ : ℝ => G t θ :=
    fun t => hG.comp (continuous_const.prodMk continuous_id)
  have hInner : ∀ t, (∫ θ in (0 : ℝ)..(2 * Real.pi), (F t θ + G t θ))
      = (∫ θ in (0 : ℝ)..(2 * Real.pi), F t θ)
        + (∫ θ in (0 : ℝ)..(2 * Real.pi), G t θ) := by
    intro t
    exact intervalIntegral.integral_add ((hFt t).intervalIntegrable _ _)
      ((hGt t).intervalIntegrable _ _)
  have hc1 : Continuous fun t : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi), F t θ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 (2 * Real.pi)
  have hc2 : Continuous fun t : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi), G t θ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG 0 (2 * Real.pi)
  rw [intervalIntegral.integral_congr (fun t _ => hInner t)]
  exact intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)

/-! ## The disc integral of the winding integrand -/

/-- For `R` exceeding `‖u‖` everywhere, the integral of `windInt u` over the disc of radius `R`
is the flux expression `fluxR u R`. -/
theorem windInt_ball_integral' (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) {R : ℝ}
    (hR : ∀ t, ‖u t‖ < R) :
    ∫ q in Metric.ball (0 : ℂ) R, windInt u q = fluxR u R := by
  have hmain : ∫ q in Metric.ball (0 : ℂ) R, windInt u q
      = (1 / (2 * Real.pi)) * ∫ q in Metric.ball (0 : ℂ) R,
          ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv u t / (u t - q)).im := by
    rw [show (∫ q in Metric.ball (0 : ℂ) R, windInt u q)
        = ∫ q in Metric.ball (0 : ℂ) R, (1 / (2 * Real.pi)) *
            ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv u t / (u t - q)).im from rfl]
    rw [MeasureTheory.integral_const_mul]
  rw [hmain, kernelSwap u hu hR, fluxR]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact polarKernel (u t) (deriv u t) (hR t)

/-! ## The limit of the flux expression -/

/-- `fluxR u R` tends to `(1/2) ∮ ω_ℂ(u, u')` as `R → ∞`. -/
theorem fluxR_tendsto' (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) :
    Filter.Tendsto (fluxR u) Filter.atTop (nhds ((1 / 2) * areaInt u)) := by
  have hkey : ∀ R : ℝ, fluxR u R = (1 / 2) * areaInt u + (1 / (2 * Real.pi)) *
      ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im *
          (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2) - R) := by
    intro R
    have hAB : (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
            * (u t * Complex.exp (-(θ : ℂ) * Complex.I)).re)
        = Real.pi * areaInt u := by
      have hper : ∀ t, (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
              * (u t * Complex.exp (-(θ : ℂ) * Complex.I)).re)
          = Real.pi * Work.RPV.ωC (u t) (deriv u t) :=
        fun t => thetaIntegral (deriv u t) (u t)
      rw [intervalIntegral.integral_congr (fun t _ => hper t),
        intervalIntegral.integral_const_mul]
      rfl
    have hAR : (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im * R) = 0 := by
      have hper : ∀ t, (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im * R) = 0 := by
        intro t
        rw [show (∫ θ in (0 : ℝ)..(2 * Real.pi),
              (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im * R)
            = ∫ θ in (0 : ℝ)..(2 * Real.pi),
              R * (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im by
          apply intervalIntegral.integral_congr; intro θ _; ring]
        rw [intervalIntegral.integral_const_mul, thetaIntegralSin, mul_zero]
      rw [intervalIntegral.integral_congr (fun t _ => hper t)]
      simp
    have hAS : (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
            * Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2))
        = (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
              * (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2)
                - R)) := by
      have hFc : Continuous fun p : ℝ × ℝ =>
          (deriv u p.1 * Complex.exp (-(p.2 : ℂ) * Complex.I)).im * R := by fun_prop
      have hGc : Continuous fun p : ℝ × ℝ =>
          (deriv u p.1 * Complex.exp (-(p.2 : ℂ) * Complex.I)).im
            * (Real.sqrt (R ^ 2 - (u p.1 * Complex.exp (-(p.2 : ℂ) * Complex.I)).im ^ 2)
              - R) := by fun_prop
      rw [show (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
              * Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2))
          = ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
              ((deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im * R
                + (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
                  * (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2)
                    - R)) by
        apply intervalIntegral.integral_congr; intro t _
        apply intervalIntegral.integral_congr; intro θ _
        ring]
      rw [double_integral_add _ _ hFc hGc, hAR, zero_add]
    have hmain : (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
            * ((u t * Complex.exp (-(θ : ℂ) * Complex.I)).re
              + Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2)))
        = Real.pi * areaInt u
          + (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
                * (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2)
                  - R)) := by
      have hFc : Continuous fun p : ℝ × ℝ =>
          (deriv u p.1 * Complex.exp (-(p.2 : ℂ) * Complex.I)).im
            * (u p.1 * Complex.exp (-(p.2 : ℂ) * Complex.I)).re := by fun_prop
      have hGc : Continuous fun p : ℝ × ℝ =>
          (deriv u p.1 * Complex.exp (-(p.2 : ℂ) * Complex.I)).im
            * Real.sqrt (R ^ 2 - (u p.1 * Complex.exp (-(p.2 : ℂ) * Complex.I)).im ^ 2) := by
        fun_prop
      rw [show (∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
              * ((u t * Complex.exp (-(θ : ℂ) * Complex.I)).re
                + Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2)))
          = ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
              ((deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
                  * (u t * Complex.exp (-(θ : ℂ) * Complex.I)).re
                + (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im
                  * Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2)) by
        apply intervalIntegral.integral_congr; intro t _
        apply intervalIntegral.integral_congr; intro θ _
        ring]
      rw [double_integral_add _ _ hFc hGc, hAB, hAS]
    rw [fluxR, hmain]
    have hpi : (1 / (2 * Real.pi)) * Real.pi = 1 / 2 := by
      field_simp
    rw [mul_add, ← mul_assoc, hpi]
  have hlim : Filter.Tendsto (fun R : ℝ => (1 / 2) * areaInt u + (1 / (2 * Real.pi)) *
        ∫ t in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (deriv u t * Complex.exp (-(θ : ℂ) * Complex.I)).im *
            (Real.sqrt (R ^ 2 - (u t * Complex.exp (-(θ : ℂ) * Complex.I)).im ^ 2) - R))
      Filter.atTop (nhds ((1 / 2) * areaInt u)) := by
    have := (tendsto_const_nhds (x := (1 / 2) * areaInt u)).add (remainderTendsto u hu)
    simpa using this
  simpa only [funext hkey] using hlim

/-! ## The area formula -/

theorem areaFormula (c : ℝ → ℂ) (hc : ContDiff ℝ 1 c) (hper : ∀ t, c (t + 2 * Real.pi) = c t)
    (hint : MeasureTheory.Integrable (Work.RPB.B1.windInt c) MeasureTheory.volume) :
    (1 / 2) * Work.RPB.B1.areaInt c = ∫ z, Work.RPB.B1.windInt c z := by
  obtain ⟨M, hM⟩ := exists_bound_periodic c hc.continuous hper
  have hunion : (⋃ R : ℝ, Metric.ball (0 : ℂ) R) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨‖z‖ + 1, by rw [Metric.mem_ball, dist_zero_right]; linarith⟩
  have hlim1 : Filter.Tendsto (fun R : ℝ => ∫ z in Metric.ball (0 : ℂ) R, windInt c z)
      Filter.atTop (nhds (∫ z, windInt c z)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone
      (f := windInt c) (μ := volume) (s := fun R : ℝ => Metric.ball (0 : ℂ) R)
      (fun R => Metric.isOpen_ball.measurableSet)
      (fun R R' hRR' => Metric.ball_subset_ball hRR')
      (by rw [hunion, MeasureTheory.integrableOn_univ]; exact hint)
    simpa [hunion] using h
  have hflux : Filter.Tendsto (fluxR c) Filter.atTop (nhds ((1 / 2) * areaInt c)) :=
    fluxR_tendsto' c hc
  have heq : (fun R : ℝ => ∫ z in Metric.ball (0 : ℂ) R, windInt c z)
      =ᶠ[Filter.atTop] (fluxR c) := by
    filter_upwards [Filter.eventually_gt_atTop M] with R hR
    exact windInt_ball_integral' c hc (fun t => lt_of_le_of_lt (hM t) hR)
  have hlim2 : Filter.Tendsto (fun R : ℝ => ∫ z in Metric.ball (0 : ℂ) R, windInt c z)
      Filter.atTop (nhds ((1 / 2) * areaInt c)) :=
    Filter.Tendsto.congr' heq.symm hflux
  exact tendsto_nhds_unique hlim2 hlim1

end Work.RPB.B1
