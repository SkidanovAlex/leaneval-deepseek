import Mathlib
import Submission.Work.BMF.liouville.twist_small_defs
import Submission.Work.BMF.liouville.twist_ibp
import Submission.Work.BMF.liouville.twist_int_small_low
import Submission.Work.BMF.liouville.prime_power_twist_defs
import Submission.Work.BMF.liouville.norm_corr_pow_le
import Submission.Work.BMF.liouville.corr_ne_zero_imp
import Submission.Work.BMF.liouville.sum_prime_pow_le_rect_sum
import Submission.Work.BMF.liouville.rect_inv_pow_sum_le_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open MeasureTheory Finset Real

noncomputable section

/-- The integrand `t^{-1-iu} (1 + 1/log t)/log t` of the twisted reciprocal prime sum. -/
def rcpF (u t : ℝ) : ℂ := (t : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)) *
    (((1 + 1 / Real.log t) / Real.log t : ℝ) : ℂ)

/-- `log t ≥ 1` for `t ≥ 3` (since `log 3 > 1`). -/
lemma log_ge_one_of_three {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  have h : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have h13 : (1 : ℝ) < Real.log 3 := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  linarith

/-- Norm of `t^{-iu}/(-iu)`: it is `1/|u|`. -/
lemma rcp_norm_osc_recip (u : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (-(Complex.I * (u : ℂ))) / (-(Complex.I * (u : ℂ)))‖ = 1 / |u| := by
  rw [norm_div, norm_cpow_neg_I_mul u ht]
  congr 1
  rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- A boundary term of the integration by parts: for `3 ≤ a ≤ t`,
`‖t^{-iu}/(-iu) * Hw(log t)‖ ≤ 2`, as long as `|u| log a ≥ 1`. -/
lemma rcp_boundary_le (u : ℝ) {a t : ℝ} (ha3 : 3 ≤ a) (hat : a ≤ t)
    (hprod : 1 ≤ |u| * Real.log a) :
    ‖(t : ℂ) ^ (-(Complex.I * (u : ℂ))) / (-(Complex.I * (u : ℂ))) *
        ((Hw (Real.log t)) : ℂ)‖ ≤ 2 := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  have hloga1 : 1 ≤ Real.log a := log_ge_one_of_three ha3
  have hloga0 : 0 < Real.log a := by linarith
  have hlogt1 : 1 ≤ Real.log t := log_ge_one_of_three (by linarith)
  have hlogt0 : 0 < Real.log t := by linarith
  have hHwt0 : 0 ≤ Hw (Real.log t) := Hw_nonneg hlogt0
  have hHwmono : Hw (Real.log t) ≤ Hw (Real.log a) :=
    Hw_antitone hloga1 hlogt1 (Real.log_le_log ha0 hat)
  rw [norm_mul, rcp_norm_osc_recip u ht0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hHwt0]
  have h1 : 1 / (|u| * Real.log a) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hprod
  have h2 : 1 / Real.log a ≤ 1 := by
    rw [div_le_one hloga0]
    linarith
  have hHwa : Hw (Real.log a) = 1 / Real.log a + 1 / (Real.log a) ^ 2 :=
    Hw_eq (ne_of_gt hloga0)
  have hfac : 1 / |u| * (1 / Real.log a + 1 / (Real.log a) ^ 2)
      = (1 / (|u| * Real.log a)) * (1 + 1 / Real.log a) := by
    field_simp
  have step1 : 1 / |u| * Hw (Real.log t) ≤ 1 / |u| * Hw (Real.log a) :=
    mul_le_mul_of_nonneg_left hHwmono (by positivity)
  have step2 : 1 / |u| * Hw (Real.log a) ≤ 2 := by
    rw [hHwa, hfac]
    calc (1 / (|u| * Real.log a)) * (1 + 1 / Real.log a)
        ≤ 1 * 2 := by
          apply mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
      _ = 2 := by norm_num
  linarith

/-- Pointwise norm of the integrand: `‖rcpF u t‖ = t⁻¹ Hw(log t)` for `t ≥ 3`. -/
lemma rcp_norm_F (u : ℝ) {t : ℝ} (ht : 3 ≤ t) : ‖rcpF u t‖ = t⁻¹ * Hw (Real.log t) := by
  have ht0 : 0 < t := by linarith
  have hlogt0 : 0 < Real.log t := Real.log_pos (by linarith)
  rw [rcpF, norm_mul, norm_cpow_neg_one_sub_I_mul u ht0]
  have hc : ‖(((1 + 1 / Real.log t) / Real.log t : ℝ) : ℂ)‖ = Hw (Real.log t) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < (1 + 1 / Real.log t) / Real.log t)]
    simp only [Hw]
  rw [hc]

/-- The remaining integral in the integration by parts is at most `3` in modulus, whenever
`3 ≤ a ≤ b` and `|u| log a ≥ 1`. -/
lemma rcp_rem_bound (u : ℝ) {a b : ℝ} (h3 : 3 ≤ a) (hab : a ≤ b)
    (hprod : 1 ≤ |u| * Real.log a) :
    ‖∫ t in a..b, ((t : ℂ) ^ (-(Complex.I * (u : ℂ))) / (-(Complex.I * (u : ℂ)))) *
        ((Hwderiv (Real.log t)) : ℂ) / t‖ ≤ 3 := by
  have ha1 : 1 ≤ Real.log a := log_ge_one_of_three h3
  have hapos : 0 < Real.log a := by linarith
  have hua : 0 < |u| := by
    rcases eq_or_lt_of_le (abs_nonneg u) with h | h
    · rw [← h] at hprod
      linarith
    · exact h
  have h1u : 1 / |u| ≤ Real.log a := by
    rw [div_le_iff₀ hua]
    linarith [hprod]
  have hcont : ContinuousOn (fun t : ℝ => 3 / (t * (Real.log t) ^ 2)) (Set.Icc (3:ℝ) b) := by
    have hlog : ContinuousOn Real.log (Set.Icc (3:ℝ) b) := fun t ht =>
      (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
    have hsq : ContinuousOn (fun t : ℝ => (Real.log t) ^ 2) (Set.Icc (3:ℝ) b) := hlog.pow 2
    have hid : ContinuousOn (fun t : ℝ => t) (Set.Icc (3:ℝ) b) := continuousOn_id
    have hne : ∀ t ∈ Set.Icc (3:ℝ) b, t * (Real.log t) ^ 2 ≠ 0 := by
      intro t ht
      have h1 : (0:ℝ) < t := by linarith [ht.1]
      have h2 : (0:ℝ) < Real.log t := Real.log_pos (by linarith [ht.1])
      exact ne_of_gt (mul_pos h1 (pow_pos h2 2))
    exact continuousOn_const.div (hid.mul hsq) hne
  have hint3 : IntervalIntegrable (fun t : ℝ => 3 / (t * (Real.log t) ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hcont.mono (Set.Icc_subset_Icc h3 le_rfl)
  have hpt : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc a b →
      ‖((t : ℂ) ^ (-(Complex.I * (u : ℂ))) / (-(Complex.I * (u : ℂ)))) *
        ((Hwderiv (Real.log t)) : ℂ) / t‖ ≤ Real.log a * (3 / (t * (Real.log t) ^ 2)) := by
    apply Filter.Eventually.of_forall
    intro t ht
    have ht3 : (3:ℝ) ≤ t := le_trans h3 (le_of_lt ht.1)
    have ht0 : 0 < t := by linarith
    have hlt1 : 1 ≤ Real.log t := log_ge_one_of_three ht3
    have hlt0 : 0 < Real.log t := by linarith
    rw [norm_div, norm_mul, rcp_norm_osc_recip u ht0, Complex.norm_real, Real.norm_eq_abs,
      abs_Hwderiv hlt0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hnum : 1 / (Real.log t) ^ 2 + 2 / (Real.log t) ^ 3 ≤ 3 / (Real.log t) ^ 2 := by
      have h3' : 2 / (Real.log t) ^ 3 ≤ 2 / (Real.log t) ^ 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [hlt1]
      calc 1 / (Real.log t) ^ 2 + 2 / (Real.log t) ^ 3
          ≤ 1 / (Real.log t) ^ 2 + 2 / (Real.log t) ^ 2 := by linarith
        _ = 3 / (Real.log t) ^ 2 := by ring
    calc 1 / |u| * (1 / (Real.log t) ^ 2 + 2 / (Real.log t) ^ 3) / t
        ≤ Real.log a * (3 / (Real.log t) ^ 2) / t := by
          gcongr
      _ = Real.log a * (3 / (t * (Real.log t) ^ 2)) := by
          field_simp
          try ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.log a * (3 / (t * (Real.log t) ^ 2)))
      volume a b := hint3.const_mul (Real.log a)
  have hmain : ‖∫ t in a..b, ((t : ℂ) ^ (-(Complex.I * (u : ℂ))) / (-(Complex.I * (u : ℂ)))) *
        ((Hwderiv (Real.log t)) : ℂ) / t‖
      ≤ Real.log a * ∫ t in a..b, 3 / (t * (Real.log t) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.norm_integral_le_of_norm_le hab hpt hint
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => -3 / Real.log t)
      (3 / (x * (Real.log x) ^ 2)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx3 : (3:ℝ) ≤ x := le_trans h3 hx.1
    have hx0 : x ≠ 0 := by linarith
    have hlx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    have h2 : HasDerivAt (fun t : ℝ => (Real.log t)⁻¹) (-(x⁻¹) / (Real.log x) ^ 2) x :=
      (Real.hasDerivAt_log hx0).inv hlx
    have h3' : HasDerivAt (fun t : ℝ => -3 * (Real.log t)⁻¹)
        (-3 * (-(x⁻¹) / (Real.log x) ^ 2)) x := h2.const_mul (-3)
    have h4 : (fun t : ℝ => -3 * (Real.log t)⁻¹) = fun t : ℝ => -3 / Real.log t := by
      ext t
      rw [div_eq_mul_inv]
    rw [h4] at h3'
    convert h3' using 1
    field_simp
    try ring
  have hFTC : ∫ t in a..b, 3 / (t * (Real.log t) ^ 2) = -3 / Real.log b - -3 / Real.log a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint3
  have hval : Real.log a * ∫ t in a..b, 3 / (t * (Real.log t) ^ 2) ≤ 3 := by
    rw [hFTC]
    have hb0 : 0 < Real.log b := Real.log_pos (by linarith)
    have heq : Real.log a * (-3 / Real.log b - -3 / Real.log a)
        = 3 - 3 * Real.log a / Real.log b := by
      field_simp
      ring
    rw [heq]
    have hnn : 0 ≤ 3 * Real.log a / Real.log b :=
      div_nonneg (mul_nonneg (by norm_num) (le_of_lt hapos)) (le_of_lt hb0)
    linarith
  linarith

/-- **Integration-by-parts bound.** For `3 ≤ a ≤ b` and `|u| log a ≥ 1`,
`‖∫_a^b t^{-1-iu} (1 + 1/log t)/log t dt‖ ≤ 7`. -/
lemma rcp_int_bound_ibp (u : ℝ) (hu : u ≠ 0) {a b : ℝ} (h3 : 3 ≤ a) (hab : a ≤ b)
    (hprod : 1 ≤ |u| * Real.log a) : ‖∫ t in a..b, rcpF u t‖ ≤ 7 := by
  have hgoal : ∫ t in a..b, rcpF u t
      = ∫ t in a..b, (t : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)) * ((Hw (Real.log t)) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [rcpF, Hw]
  rw [hgoal, twist_ibp u hu h3 hab]
  have hA := rcp_boundary_le u h3 le_rfl hprod
  have hB := rcp_boundary_le u h3 hab hprod
  have hC := rcp_rem_bound u h3 hab hprod
  have h1 := norm_sub_le ((b : ℂ) ^ (-(Complex.I * (u : ℂ))) / (-(Complex.I * (u : ℂ))) *
      ((Hw (Real.log b)) : ℂ) - (a : ℂ) ^ (-(Complex.I * (u : ℂ))) /
        (-(Complex.I * (u : ℂ))) * ((Hw (Real.log a)) : ℂ))
    (∫ t in a..b, ((t : ℂ) ^ (-(Complex.I * (u : ℂ))) / (-(Complex.I * (u : ℂ)))) *
        ((Hwderiv (Real.log t)) : ℂ) / t)
  have h2 := norm_sub_le ((b : ℂ) ^ (-(Complex.I * (u : ℂ))) / (-(Complex.I * (u : ℂ))) *
      ((Hw (Real.log b)) : ℂ)) ((a : ℂ) ^ (-(Complex.I * (u : ℂ))) /
        (-(Complex.I * (u : ℂ))) * ((Hw (Real.log a)) : ℂ))
  linarith

/-- Conjunct 1 of the requested statement: for `|u| ≥ 1` the oscillatory integral over any
`[N,M]`, `3 ≤ N ≤ M`, is bounded by an absolute constant. -/
theorem rcp_int_large : ∃ K : ℝ, 0 < K ∧ ∀ (u : ℝ), 1 ≤ |u| → ∀ N M : ℝ, 3 ≤ N → N ≤ M →
    ‖∫ t in N..M, rcpF u t‖ ≤ K := by
  refine ⟨7, by norm_num, ?_⟩
  intro u hu1 N M hN hNM
  have hla1 : 1 ≤ Real.log N := log_ge_one_of_three hN
  have hprod : 1 ≤ |u| * Real.log N := by nlinarith
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, abs_zero] at hu1
    linarith
  exact rcp_int_bound_ibp u hu0 hN hNM hprod

/-- Continuity of the integrand `rcpF u` on `[3,R]`. -/
lemma continuousOn_rcpF (u R : ℝ) : ContinuousOn (rcpF u) (Set.Icc (3:ℝ) R) := by
  have hwreal : ContinuousOn (fun t : ℝ => (1 + 1 / Real.log t) / Real.log t)
      (Set.Icc (3:ℝ) R) := by
    have hlog : ContinuousOn Real.log (Set.Icc (3:ℝ) R) := fun t ht =>
      (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
    have hlog0 : ∀ t ∈ Set.Icc (3:ℝ) R, Real.log t ≠ 0 := by
      intro t ht
      exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hres : ContinuousOn (fun t : ℝ => (1 + (Real.log t)⁻¹) / (Real.log t))
        (Set.Icc (3:ℝ) R) :=
      ((continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (3:ℝ) R)).add
        (hlog.inv₀ hlog0)).div hlog hlog0
    convert hres using 1
    ext t
    rw [one_div]
  have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)))
      (Set.Icc (3:ℝ) R) := by
    intro t ht
    have hmem : (t : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.ofReal_mem_slitPlane]
      linarith [ht.1]
    exact (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
      hmem).continuousWithinAt
  have h2 : ContinuousOn (fun t : ℝ => (((1 + 1 / Real.log t) / Real.log t : ℝ) : ℂ))
      (Set.Icc (3:ℝ) R) := Complex.continuous_ofReal.comp_continuousOn hwreal
  exact h1.mul h2

/-- Continuity of the weight `t ↦ t⁻¹ Hw(log t)` on `[3,R]`. -/
lemma continuousOn_rcpW (R : ℝ) :
    ContinuousOn (fun t : ℝ => t⁻¹ * Hw (Real.log t)) (Set.Icc (3:ℝ) R) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
  have hHw : ContinuousAt Hw (Real.log t) := (hasDerivAt_Hw hlt).continuousAt
  exact ((continuousAt_id.inv₀ ht0).mul (hHw.comp (Real.continuousAt_log ht0))).continuousWithinAt

/-- Conjunct 2 of the requested statement, for `0 < |u| ≤ 1`. -/
theorem rcp_int_small : ∃ K : ℝ, 0 < K ∧ ∀ (u : ℝ), 0 < |u| → |u| ≤ 1 → ∀ M : ℝ, 3 ≤ M →
    (((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * ∫ t in (3 : ℝ)..M, rcpF u t).re ≤
      Real.log (1 / |u|) + K := by
  refine ⟨14, by norm_num, ?_⟩
  intro u hu hu1 M hM
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, abs_zero] at hu
    exact lt_irrefl 0 hu
  set S : ℝ := max 3 (Real.exp (1 / |u|)) with hS
  have hS3 : 3 ≤ S := le_max_left _ _
  have hlogS : 1 / |u| ≤ Real.log S := by
    rw [hS]
    calc 1 / |u| = Real.log (Real.exp (1 / |u|)) := (Real.log_exp _).symm
      _ ≤ Real.log (max 3 (Real.exp (1 / |u|))) :=
          Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
  have hlow : ∫ t in (3 : ℝ)..S, t⁻¹ * Hw (Real.log t) ≤ Real.log (1 / |u|) + 2 := by
    rw [hS]
    simpa only using twist_int_small_low u hu hu1
  have hni : ‖((1 : ℂ) - Complex.I * (u : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have hre : ((1 : ℂ) - Complex.I * (u : ℂ)).re = 1 := by
      simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by
      have := Complex.abs_re_le_norm ((1 : ℂ) - Complex.I * (u : ℂ))
      rw [hre] at this
      simpa using this
    exact inv_le_one_of_one_le₀ h1
  have hintW : ∫ t in (3 : ℝ)..S, t⁻¹ * Hw (Real.log t) = ∫ t in (3 : ℝ)..S, ‖rcpF u t‖ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hS3] at ht
    exact (rcp_norm_F u ht.1).symm
  have hstep1 : (((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * ∫ t in (3 : ℝ)..M, rcpF u t).re
      ≤ ‖∫ t in (3 : ℝ)..M, rcpF u t‖ := by
    calc (((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * ∫ t in (3 : ℝ)..M, rcpF u t).re
        ≤ ‖((1 : ℂ) - Complex.I * (u : ℂ))⁻¹ * ∫ t in (3 : ℝ)..M, rcpF u t‖ :=
          Complex.re_le_norm _
      _ ≤ ‖∫ t in (3 : ℝ)..M, rcpF u t‖ := by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) hni
  have hstep2 : ‖∫ t in (3 : ℝ)..M, rcpF u t‖ ≤ Real.log (1 / |u|) + 14 := by
    by_cases hMS : M ≤ S
    · have hnorm : ‖∫ t in (3 : ℝ)..M, rcpF u t‖ ≤ ∫ t in (3 : ℝ)..M, ‖rcpF u t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hM
      have hcong : ∫ t in (3 : ℝ)..M, ‖rcpF u t‖ = ∫ t in (3 : ℝ)..M, t⁻¹ * Hw (Real.log t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hM] at ht
        exact rcp_norm_F u ht.1
      have hmono : ∫ t in (3 : ℝ)..M, t⁻¹ * Hw (Real.log t)
          ≤ ∫ t in (3 : ℝ)..S, t⁻¹ * Hw (Real.log t) := by
        have hpt : ∀ x ∈ Set.Icc (3:ℝ) S, 0 ≤ x⁻¹ * Hw (Real.log x) := by
          intro x hx
          exact mul_nonneg (inv_nonneg.mpr (by linarith [hx.1]))
            (Hw_nonneg (Real.log_pos (by linarith [hx.1])))
        have hadd : (∫ t in (3 : ℝ)..M, t⁻¹ * Hw (Real.log t))
            + ∫ t in M..S, t⁻¹ * Hw (Real.log t)
            = ∫ t in (3 : ℝ)..S, t⁻¹ * Hw (Real.log t) :=
          intervalIntegral.integral_add_adjacent_intervals
            (by
              apply ContinuousOn.intervalIntegrable
              rw [Set.uIcc_of_le hM]
              exact continuousOn_rcpW M)
            (by
              apply ContinuousOn.intervalIntegrable
              rw [Set.uIcc_of_le hMS]
              exact (continuousOn_rcpW S).mono (Set.Icc_subset_Icc hM le_rfl))
        have hnn : 0 ≤ ∫ t in M..S, t⁻¹ * Hw (Real.log t) :=
          intervalIntegral.integral_nonneg hMS
            (fun x hx => hpt x (Set.Icc_subset_Icc hM le_rfl hx))
        linarith
      linarith
    · push Not at hMS
      have hSM : S ≤ M := le_of_lt hMS
      have hint1 : IntervalIntegrable (rcpF u) volume (3:ℝ) S := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hS3]
        exact continuousOn_rcpF u S
      have hint2 : IntervalIntegrable (rcpF u) volume S M := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hSM]
        exact (continuousOn_rcpF u M).mono (Set.Icc_subset_Icc hS3 le_rfl)
      have hsplit : ∫ t in (3 : ℝ)..M, rcpF u t
          = (∫ t in (3 : ℝ)..S, rcpF u t) + ∫ t in S..M, rcpF u t :=
        (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
      have hnormS : ‖∫ t in (3 : ℝ)..S, rcpF u t‖ ≤ ∫ t in (3 : ℝ)..S, ‖rcpF u t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hS3
      have hhigh : ‖∫ t in S..M, rcpF u t‖ ≤ 7 := by
        have hprod : 1 ≤ |u| * Real.log S := by
          have hpos : 0 < |u| := hu
          have h2 : |u| * (1 / |u|) ≤ |u| * Real.log S :=
            mul_le_mul_of_nonneg_left hlogS (le_of_lt hpos)
          have h1 : |u| * (1 / |u|) = 1 := by field_simp
          linarith
        exact rcp_int_bound_ibp u hu0 hS3 hSM hprod
      have hbound : ‖∫ t in (3 : ℝ)..S, rcpF u t‖ ≤ Real.log (1 / |u|) + 2 := by
        linarith [hnormS, hintW, hlow]
      calc ‖∫ t in (3 : ℝ)..M, rcpF u t‖
          = ‖(∫ t in (3 : ℝ)..S, rcpF u t) + ∫ t in S..M, rcpF u t‖ := by rw [← hsplit]
        _ ≤ ‖∫ t in (3 : ℝ)..S, rcpF u t‖ + ‖∫ t in S..M, rcpF u t‖ := norm_add_le _ _
        _ ≤ (Real.log (1 / |u|) + 2) + 7 := add_le_add hbound hhigh
        _ = Real.log (1 / |u|) + 9 := by ring
        _ ≤ Real.log (1 / |u|) + 14 := by linarith
  linarith

/-- The `≤ 1` prime-power correction: the logarithmically weighted von Mangoldt sum differs
from the prime sum by at most `1`. -/
theorem rcp_ppc (u : ℝ) (N M : ℕ) :
    ‖(∑ n ∈ Finset.Icc N M,
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((Real.log n : ℝ) : ℂ)) *
            (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)))
        - ∑ p ∈ (Finset.Icc N M).filter Nat.Prime,
            (p : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ))‖ ≤ 1 := by
  have hcorr : ∑ n ∈ Finset.Icc N M, corr u n
      = (∑ n ∈ Finset.Icc N M,
            (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((Real.log n : ℝ) : ℂ)) *
              (n : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)))
        - ∑ p ∈ (Finset.Icc N M).filter Nat.Prime,
            (p : ℂ) ^ (-(1 : ℂ) - Complex.I * (u : ℂ)) := by
    simp only [corr, twistZ]
    rw [Finset.sum_sub_distrib, Finset.sum_filter]
  rw [← hcorr]
  calc ‖∑ n ∈ Finset.Icc N M, corr u n‖
      ≤ ∑ n ∈ Finset.Icc N M, ‖corr u n‖ := norm_sum_le _ _
    _ = ∑ n ∈ (Finset.Icc N M).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), ‖corr u n‖ := by
        refine (Finset.sum_filter_of_ne ?_).symm
        intro n _ hne
        exact corr_ne_zero_imp u n (norm_ne_zero_iff.mp hne)
    _ ≤ ∑ p ∈ Finset.Icc 2 M, ∑ k ∈ Finset.Icc 2 M, ‖corr u (p ^ k)‖ :=
        sum_prime_pow_le_rect_sum (fun n => ‖corr u n‖) (fun n => norm_nonneg _) N M
    _ ≤ ∑ p ∈ Finset.Icc 2 M, ∑ k ∈ Finset.Icc 2 M, (((p : ℝ))⁻¹) ^ k := by
        apply Finset.sum_le_sum; intro p hp
        apply Finset.sum_le_sum; intro k hk
        exact norm_corr_pow_le u p k (Finset.mem_Icc.mp hp).1 (Finset.mem_Icc.mp hk).1
    _ = ∑ p ∈ Finset.Icc 2 M, ∑ k ∈ Finset.Icc 2 M, (1 : ℝ) / (p : ℝ) ^ k := by
        apply Finset.sum_congr rfl; intro p _
        apply Finset.sum_congr rfl; intro k _
        rw [inv_pow, one_div]
    _ ≤ 1 := rect_inv_pow_sum_le_one M

end

end Work.BMF.liouville
