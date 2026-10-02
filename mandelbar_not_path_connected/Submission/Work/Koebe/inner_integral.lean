import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Koebe

open Complex MeasureTheory intervalIntegral
open scoped Real Interval

/-- The integrand `θ ↦ (ζ - r e^{iθ})⁻¹` is `2π`-periodic. -/
private lemma periodic_innerIntegrand (ζ : ℂ) (r : ℝ) :
    Function.Periodic
      (fun θ : ℝ => (ζ - (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))⁻¹) (2 * Real.pi) := by
  intro θ
  change (ζ - (r:ℂ) * Complex.exp (((θ + 2 * Real.pi : ℝ):ℂ) * Complex.I))⁻¹
      = (ζ - (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))⁻¹
  have h : ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
      = (θ:ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_add,
    show ((2 * Real.pi : ℂ) * Complex.I) = (2 * Real.pi * Complex.I : ℂ) from by ring,
    Complex.exp_two_pi_mul_I, mul_one]

/-- Value of the circle integral `∮_{|z|=r} dz / (z (ζ - z))`. -/
private lemma circle_integral_value (ζ : ℂ) (r : ℝ) (hr : 0 < r) (hr' : r ≠ ‖ζ‖) :
    ∮ z in C(0, r), (z * (ζ - z))⁻¹
      = if r < ‖ζ‖ then 2 * Real.pi * Complex.I / ζ else 0 := by
  rcases lt_or_gt_of_ne hr' with hlt | hgt
  · rw [if_pos hlt]
    -- ζ lies outside the closed disc; Cauchy integral formula
    have hmem : (0:ℂ) ∈ Metric.ball 0 r := by simp [Metric.mem_ball, hr]
    have hcont : ContinuousOn (fun z => (ζ - z)⁻¹) (Metric.closedBall 0 r) := by
      apply ContinuousOn.inv₀
      · exact continuousOn_const.sub continuousOn_id
      · intro z hz
        rw [sub_ne_zero]
        intro h
        have hz' : ‖z‖ ≤ r := by
          have := Metric.mem_closedBall.1 hz
          simpa [dist_eq_norm] using this
        rw [← h] at hz'
        linarith
    have hdiff : ∀ x ∈ Metric.ball 0 r \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun z => (ζ - z)⁻¹) x := by
      intro x hx
      rw [Set.sdiff_empty] at hx
      apply DifferentiableAt.inv
      · exact (differentiableAt_const ζ).sub differentiableAt_id
      · rw [sub_ne_zero]
        intro h
        have hx' : ‖x‖ < r := by
          have := Metric.mem_ball.1 hx
          simpa [dist_eq_norm] using this
        rw [← h] at hx'
        linarith
    have hc := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        (s := (∅ : Set ℂ)) Set.countable_empty hmem hcont hdiff
    have hcong : ∮ z in C(0, r), (z * (ζ - z))⁻¹
        = ∮ z in C(0, r), (z - 0)⁻¹ • (ζ - z)⁻¹ := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      simp only [smul_eq_mul, sub_zero]
      rw [mul_inv, mul_comm]
    rw [hcong, hc]
    simp only [smul_eq_mul, sub_zero, div_eq_mul_inv]
  · rw [if_neg (not_lt.mpr hgt.le)]
    rcases eq_or_ne ζ 0 with h0 | hζ
    · -- ζ = 0 : integrand is -z⁻², whose circle integral vanishes
      subst h0
      have hcong : ∮ z in C(0, r), (z * ((0:ℂ) - z))⁻¹
          = ∮ z in C(0, r), (-1:ℂ) • (z - 0) ^ (-2:ℤ) := by
        apply circleIntegral.integral_congr hr.le
        intro z hz
        show (z * ((0:ℂ) - z))⁻¹ = (-1:ℂ) • (z - 0) ^ (-2:ℤ)
        rw [show z * ((0:ℂ) - z) = -(z^2) by ring]
        simp [zpow_neg, zpow_ofNat, smul_eq_mul, inv_neg]
      rw [hcong, circleIntegral.integral_smul,
        circleIntegral.integral_sub_zpow_of_ne (n := -2) (by decide) 0 0 r]
      simp
    · -- ζ ≠ 0 : partial fractions; both poles contribute ±2πi
      have hmem0 : (0:ℂ) ∈ Metric.ball 0 r := by simp [Metric.mem_ball, hr]
      have hmemζ : ζ ∈ Metric.ball 0 r := by
        rw [Metric.mem_ball]; simpa [dist_eq_norm] using hgt
      have hcong : ∮ z in C(0, r), (z * (ζ - z))⁻¹
          = ∮ z in C(0, r), ζ⁻¹ * (z⁻¹ - (z - ζ)⁻¹) := by
        apply circleIntegral.integral_congr hr.le
        intro z hz
        have hzn : ‖z‖ = r := by
          have := Metric.mem_sphere.1 hz; simpa [dist_eq_norm] using this
        have hz0 : z ≠ 0 := by intro h; rw [h] at hzn; simp at hzn; linarith
        have hzζ : z - ζ ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hzn; linarith
        have hζz : ζ - z ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [← h] at hzn; linarith
        field_simp
        ring
      rw [hcong, circleIntegral.integral_const_mul]
      have hInt1 : CircleIntegrable (fun z : ℂ => z⁻¹) 0 r := by
        apply ContinuousOn.circleIntegrable hr.le
        apply ContinuousOn.inv₀ continuousOn_id
        intro z hz h
        have hzn : ‖z‖ = r := by
          have := Metric.mem_sphere.1 hz; simpa [dist_eq_norm] using this
        have hz_eq : z = 0 := h
        rw [hz_eq] at hzn; simp at hzn; linarith
      have hInt2 : CircleIntegrable (fun z : ℂ => (z - ζ)⁻¹) 0 r := by
        apply ContinuousOn.circleIntegrable hr.le
        apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
        intro z hz h
        have hzn : ‖z‖ = r := by
          have := Metric.mem_sphere.1 hz; simpa [dist_eq_norm] using this
        have hz_eq : z = ζ := sub_eq_zero.mp h
        rw [hz_eq] at hzn; linarith
      rw [circleIntegral.integral_sub hInt1 hInt2]
      have h1 : (∮ z in C(0, r), z⁻¹) = 2 * Real.pi * Complex.I := by
        simpa using circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := r) hmem0
      have h2 : (∮ z in C(0, r), (z - ζ)⁻¹) = 2 * Real.pi * Complex.I :=
        circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := ζ) (R := r) hmemζ
      rw [h1, h2]
      ring

/-- The interval integral over one period equals `i⁻¹` times the circle integral. -/
private lemma interval_eq_circle (ζ : ℂ) (r : ℝ) (hr : 0 < r) :
    (∫ θ in (0:ℝ)..2*Real.pi, (ζ - (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))⁻¹)
      = (Complex.I)⁻¹ * ∮ z in C(0, r), (z * (ζ - z))⁻¹ := by
  have hpoint : ∀ θ : ℝ,
      deriv (circleMap 0 r) θ • ((circleMap 0 r θ) * (ζ - circleMap 0 r θ))⁻¹
        = Complex.I * (ζ - circleMap 0 r θ)⁻¹ := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul]
    have hne : circleMap 0 r θ ≠ 0 := by
      rw [circleMap_zero]
      exact mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)
    rw [mul_inv]
    field_simp
  have hc : ∮ z in C(0, r), (z * (ζ - z))⁻¹
      = Complex.I * ∫ θ in (0:ℝ)..2*Real.pi, (ζ - circleMap 0 r θ)⁻¹ := by
    rw [circleIntegral]
    rw [show (∫ θ in (0:ℝ)..2*Real.pi,
          deriv (circleMap 0 r) θ • ((circleMap 0 r θ) * (ζ - circleMap 0 r θ))⁻¹)
        = ∫ θ in (0:ℝ)..2*Real.pi, Complex.I * (ζ - circleMap 0 r θ)⁻¹ from
      intervalIntegral.integral_congr (fun θ _ => hpoint θ)]
    rw [intervalIntegral.integral_const_mul]
  have hmain : (Complex.I)⁻¹ * ∮ z in C(0, r), (z * (ζ - z))⁻¹
      = ∫ θ in (0:ℝ)..2*Real.pi, (ζ - circleMap 0 r θ)⁻¹ := by
    rw [hc, ← mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero, one_mul]
  rw [hmain]
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp only [circleMap_zero]

theorem inner_integral (ζ : ℂ) (r : ℝ) (hr : 0 ≤ r) (hr' : r ≠ ‖ζ‖) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, (ζ - (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))⁻¹
      = if r < ‖ζ‖ then 2 * Real.pi / ζ else 0 := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  rcases eq_or_lt_of_le hr with h0 | hrpos
  · -- r = 0 : the integrand is the constant ζ⁻¹
    subst h0
    simp only [Complex.ofReal_zero, zero_mul, sub_zero]
    rw [intervalIntegral.integral_const]
    have hnorm : 0 < ‖ζ‖ := by
      rcases eq_or_ne ζ 0 with h | h
      · have : ‖ζ‖ = 0 := by rw [h, norm_zero]
        exact absurd this.symm hr'
      · exact norm_pos_iff.mpr h
    rw [if_pos hnorm, Complex.real_smul]
    push_cast
    ring
  · -- r > 0
    have hper : ∫ θ in (-Real.pi)..Real.pi,
          (ζ - (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))⁻¹
        = ∫ θ in (0:ℝ)..2*Real.pi,
          (ζ - (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))⁻¹ := by
      have := (periodic_innerIntegrand ζ r).intervalIntegral_add_eq (-Real.pi) (0:ℝ)
      rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at this
      exact this
    rw [hper, interval_eq_circle ζ r hrpos]
    rcases lt_or_gt_of_ne hr' with hlt | hgt
    · rw [if_pos hlt, circle_integral_value ζ r hrpos hr', if_pos hlt]
      have hζ : ζ ≠ 0 := by
        intro hz0; rw [hz0, norm_zero] at hlt; linarith
      field_simp
    · rw [if_neg (not_lt.mpr hgt.le), circle_integral_value ζ r hrpos hr',
        if_neg (not_lt.mpr hgt.le)]
      ring

end Work.Koebe
