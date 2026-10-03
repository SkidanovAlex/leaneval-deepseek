import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.V5.harmonic_integral_segment
import Submission.Work.Pert.V5.inv_one_sub_exp_le
import Submission.Work.Pert.V5.integral_comp_complex_affine

namespace Work.Pert.V5

open MeasureTheory


/-- The gate integral bound used by the V5 deviation assembly: for `α` in Shishikura's class `𝓕₁`,
a short interval `[a,b]` (`‖α‖(b-a) ≤ 1/2`) on which `α(x + s i)` keeps distance `‖α‖Ξ/2` from every
integer, the integral of `1/‖1 - exp(-2πi α (x+si))‖` is bounded logarithmically. -/
theorem integral_inv_exp_gate {Ξ : ℝ} {α : ℂ} {s a b : ℝ} (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (hab : a ≤ b)
    (hshort : ‖α‖*(b-a) ≤ 1/2)
    (hclear : ∀ x ∈ Set.Icc a b, ∀ k : ℤ, ‖α‖*Ξ/2 ≤ ‖α*((x:ℂ)+(s:ℂ)*Complex.I) - (k:ℂ)‖) :
    ∫ x in a..b, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*α*((x:ℂ)+(s:ℂ)*Complex.I)))‖
      ≤ 8*(1+1/‖α‖)*(1+Real.log (2+(b-a)/Ξ)) := by
  have arith_aux : ∀ u : ℝ, 0 ≤ u →
      (18/Real.pi)*(1+Real.log (2+2*u)) + 1/2 ≤ 8*(1+Real.log (2+u)) := by
    intro u hu
    have hR : 1 + Real.log (2 + 2 * u) ≤ (4/3) * (1 + Real.log (2 + u)) := by
      have h1 : 8 * (1 + u) ^ 3 ≤ (2 + u) ^ 4 := by nlinarith [pow_nonneg hu 4, hu]
      have h3 : (0:ℝ) < (2+u)^4 := by positivity
      have h4 : (2 + 2*u)^3 = 8 * (1+u)^3 := by ring
      have h5 : (2+2*u)^3 ≤ Real.exp 1 * (2+u)^4 := by
        rw [h4]
        have h2 : (1:ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
        nlinarith [h1, h2, h3]
      have h6 : (0:ℝ) < (2+2*u)^3 := by positivity
      have h7 : Real.log ((2+2*u)^3) ≤ Real.log (Real.exp 1 * (2+u)^4) := Real.log_le_log h6 h5
      rw [Real.log_pow, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt h3), Real.log_exp] at h7
      rw [Real.log_pow] at h7
      have : (3:ℝ) * Real.log (2 + 2 * u) ≤ 1 + 4 * Real.log (2 + u) := by
        push_cast at h7 ⊢; linarith
      linarith
    have hP2 : (1:ℝ) + Real.log 2 ≤ 1 + Real.log (2 + u) := by
      have : Real.log 2 ≤ Real.log (2+u) := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hlog2 : (1:ℝ) + Real.log 2 ≥ 5/3 := by
      have := Real.log_two_gt_d9; linarith
    have h36 : (36:ℝ)/100 * (1 + Real.log (2+u)) ≥ 1/2 := by
      have h0 : (36:ℝ)/100*(1+Real.log 2) ≥ 1/2 := by nlinarith [hlog2]
      nlinarith [h0, hP2]
    have hp : (24:ℝ)/Real.pi ≤ 8 - 36/100 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_d20]
    have hposn : (0:ℝ) ≤ 1 + Real.log (2+u) := by
      have : (0:ℝ) < Real.log (2+u) := Real.log_pos (by linarith)
      linarith
    calc (18/Real.pi)*(1+Real.log (2+2*u)) + 1/2
        ≤ (18/Real.pi)*((4/3)*(1+Real.log (2+u))) + 1/2 := by
          have h := mul_le_mul_of_nonneg_left hR (by positivity : (0:ℝ) ≤ 18/Real.pi)
          linarith
      _ = (24/Real.pi)*(1+Real.log (2+u)) + 1/2 := by ring
      _ ≤ (8 - 36/100)*(1+Real.log (2+u)) + 1/2 := by
          linarith [mul_le_mul_of_nonneg_right hp hposn]
      _ = 8*(1+Real.log (2+u)) - ((36:ℝ)/100*(1+Real.log (2+u)) - 1/2) := by ring
      _ ≤ 8*(1+Real.log (2+u)) := by linarith [h36]
  have hα0 : α ≠ 0 := by
    intro h0
    have h1 : |α.im| < α.re := hInF1
    rw [h0] at h1
    simp at h1
  have hMpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  rcases eq_or_lt_of_le hab with hEq | hLt
  · subst hEq
    rw [intervalIntegral.integral_same]
    have h3 : (0:ℝ) < 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
    have h4 : (0:ℝ) < 1 + 1/‖α‖ := by positivity
    simp only [sub_self, zero_div, add_zero]
    positivity
  · have hba : 0 < b - a := sub_pos.mpr hLt
    set L : ℝ := ‖α‖*(b-a) with hL
    set δ : ℝ := ‖α‖*Ξ/2 with hδ
    set u : ℝ := (b-a)/Ξ with hu
    set p : ℂ := α*((a:ℂ)+(s:ℂ)*Complex.I) with hp
    set v : ℂ := α/‖α‖ with hv
    have hLpos : 0 < L := by rw [hL]; positivity
    have hL0 : 0 ≤ L := le_of_lt hLpos
    have hLhalf : L ≤ 1/2 := by rw [hL]; exact hshort
    have hδpos : 0 < δ := by rw [hδ]; positivity
    have hu0 : 0 ≤ u := by rw [hu]; positivity
    have hv1 : ‖v‖ = 1 := by
      have h1 : ‖(((‖α‖:ℝ)):ℂ)‖ = ‖α‖ := by simp
      rw [hv, norm_div, h1]
      exact div_self (ne_of_gt hMpos)
    have hLδ : L / δ = 2*u := by
      rw [hL, hδ, hu]; field_simp
    have hcleart : ∀ t ∈ Set.Icc (0:ℝ) L, ∀ k : ℤ, δ ≤ ‖(p + (t:ℂ) • v) - (k:ℂ)‖ := by
      intro t ht k
      have hxmem : a + t/‖α‖ ∈ Set.Icc a b := by
        constructor
        · have : 0 ≤ t/‖α‖ := div_nonneg ht.1 (le_of_lt hMpos); linarith
        · have h1 : t/‖α‖ ≤ L/‖α‖ := div_le_div_of_nonneg_right ht.2 (le_of_lt hMpos)
          rw [hL] at h1
          rw [mul_div_cancel_left₀ (b-a) (ne_of_gt hMpos)] at h1
          linarith
      have hkey : p + (t:ℂ) • v = α*(((a + t/‖α‖):ℝ) + (s:ℂ)*Complex.I) := by
        rw [hp, hv, smul_eq_mul]
        push_cast
        field_simp
        ring
      rw [hkey, hδ]
      exact hclear _ hxmem k
    set m : ℤ := ⌊min p.re (p.re + L * v.re)⌋ with hm
    let ρ : ℝ → ℝ := fun t => min ‖(p + (t:ℂ) • v) - ((m:ℤ):ℂ)‖ ‖(p + (t:ℂ) • v) - (((m+1:ℤ)):ℂ)‖
    have hρeq : ∀ t ∈ Set.Icc (0:ℝ) L, (⨅ k : ℤ, ‖(p + (t:ℂ) • v) - (k:ℂ)‖) = ρ t := by
      intro t ht
      have hh := re_part_mem_floor_min (p := p) (v := v) (ℓ := L) (t := t) hL0 hLhalf hv1 ht
      rw [← hm] at hh
      exact iInf_norm_sub_int_eq_min hh.1 hh.2
    have hρpos : ∀ t ∈ Set.Icc (0:ℝ) L, 0 < ρ t := by
      intro t ht
      rw [← hρeq t ht]
      exact lt_of_lt_of_le hδpos (le_ciInf (fun k => hcleart t ht k))
    have hpt : ∀ t ∈ Set.Icc (0:ℝ) L,
        1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(p + (t:ℂ) • v)))‖ ≤ 9/(2*Real.pi*ρ t) + 1 := by
      intro t ht
      have h2 : 0 < (⨅ k : ℤ, ‖(p + (t:ℂ) • v) - (k:ℂ)‖) :=
        lt_of_lt_of_le hδpos (le_ciInf (fun k => hcleart t ht k))
      have h3 := inv_one_sub_exp_le (z := p + (t:ℂ) • v)
        (D := ⨅ k : ℤ, ‖(p + (t:ℂ) • v) - (k:ℂ)‖) h2 le_rfl
      rw [hρeq t ht] at h3
      exact h3
    -- continuity / integrability
    have hρc : Continuous ρ := by
      change Continuous (fun t : ℝ => min ‖(p + (t:ℂ) • v) - ((m:ℤ):ℂ)‖ ‖(p + (t:ℂ) • v) - (((m+1:ℤ)):ℂ)‖)
      fun_prop
    have hdenne : ∀ t ∈ Set.uIcc (0:ℝ) L, 2*Real.pi*ρ t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le hL0] at ht
      have := hρpos t ht
      positivity
    have hGcont : ContinuousOn (fun t : ℝ => 9/(2*Real.pi*ρ t) + 1) (Set.uIcc (0:ℝ) L) :=
      (ContinuousOn.div continuousOn_const (continuous_const.mul hρc).continuousOn hdenne).add continuousOn_const
    have hGint : IntervalIntegrable (fun t : ℝ => 9/(2*Real.pi*ρ t) + 1) volume (0:ℝ) L :=
      hGcont.intervalIntegrable
    have hFmeas : AEStronglyMeasurable
        (fun t : ℝ => 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(p + (t:ℂ) • v)))‖)
        (volume.restrict (Set.uIoc (0:ℝ) L)) := by
      apply Measurable.aestronglyMeasurable
      have hc : Continuous (fun t : ℝ => ‖(1:ℂ) - Complex.exp (-(2*Real.pi*Complex.I*(p + (t:ℂ) • v)))‖) := by
        fun_prop
      have hM : Measurable (fun t : ℝ => (‖(1:ℂ) - Complex.exp (-(2*Real.pi*Complex.I*(p + (t:ℂ) • v)))‖)⁻¹) :=
        hc.measurable.inv
      simpa only [one_div] using hM
    have hFint : IntervalIntegrable
        (fun t : ℝ => 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(p + (t:ℂ) • v)))‖) volume (0:ℝ) L := by
      refine IntervalIntegrable.mono_fun' hGint hFmeas ?_
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
      intro t ht
      have ht' : t ∈ Set.Icc (0:ℝ) L := by
        have h := Set.uIoc_subset_uIcc ht
        rwa [Set.uIcc_of_le hL0] at h
      dsimp only
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpt t ht'
    have hmono : (∫ t in (0:ℝ)..L, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(p + (t:ℂ) • v)))‖)
        ≤ ∫ t in (0:ℝ)..L, (9/(2*Real.pi*ρ t) + 1) :=
      intervalIntegral.integral_mono_on hL0 hFint hGint (fun t ht => hpt t ht)
    have hgeoeq : (∫ t in (0:ℝ)..L, 1/ρ t)
        = ∫ t in (0:ℝ)..L, 1/(⨅ k : ℤ, ‖(p + (t:ℂ) • v) - (k:ℂ)‖) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hL0] at ht
      dsimp only
      rw [hρeq t ht]
    have hgeo : (∫ t in (0:ℝ)..L, 1/ρ t) ≤ 4*(1 + Real.log (2 + L/δ)) := by
      rw [hgeoeq]
      exact harmonic_integral_segment hδpos hLpos hv1 hcleart hLhalf
    have hG1 : IntervalIntegrable (fun t : ℝ => 9/(2*Real.pi*ρ t)) volume (0:ℝ) L :=
      (ContinuousOn.div continuousOn_const (continuous_const.mul hρc).continuousOn hdenne).intervalIntegrable
    have hG2 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume (0:ℝ) L := intervalIntegrable_const
    have hGval : (∫ t in (0:ℝ)..L, (9/(2*Real.pi*ρ t) + 1))
        = (9/(2*Real.pi))*(∫ t in (0:ℝ)..L, 1/ρ t) + L := by
      rw [intervalIntegral.integral_add hG1 hG2]
      congr 1
      · rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hL0] at ht
        field_simp
      · rw [intervalIntegral.integral_const]; ring
    have hmain : (∫ t in (0:ℝ)..L, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(p + (t:ℂ) • v)))‖)
        ≤ (18/Real.pi)*(1+Real.log (2+2*u)) + L := by
      refine le_trans hmono ?_
      rw [hGval]
      have hg := hgeo
      rw [hLδ] at hg
      have h9 : (9/(2*Real.pi)) * (∫ t in (0:ℝ)..L, 1/ρ t) ≤ (18/Real.pi)*(1+Real.log (2+2*u)) := by
        refine le_trans (mul_le_mul_of_nonneg_left hg (by positivity)) ?_
        have : (9/(2*Real.pi)) * (4*(1+Real.log (2+2*u))) = (18/Real.pi)*(1+Real.log (2+2*u)) := by
          ring
        rw [this]
      linarith
    have harith : (18/Real.pi)*(1+Real.log (2+2*u)) + L ≤ 8*(‖α‖+1)*(1+Real.log (2+u)) := by
      have h2 := arith_aux u hu0
      have hPv : (0:ℝ) < 1 + Real.log (2+u) := by
        have hp2 : (1:ℝ) < 2 + u := by linarith
        have := Real.log_pos hp2
        linarith
      have h5 : 8*(1+Real.log (2+u)) ≤ 8*(‖α‖+1)*(1+Real.log (2+u)) := by
        nlinarith [hPv, hMpos]
      linarith
    have hcov := integral_comp_complex_affine (α := α) hα0 (s := s) hab
      (f := fun z : ℂ => 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*z))‖)
    have hLHS : (∫ x in a..b, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*α*((x:ℂ)+(s:ℂ)*Complex.I)))‖)
        = ∫ x in a..b, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(α*((x:ℂ)+(s:ℂ)*Complex.I))))‖ := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      have harg : 2 * (Real.pi : ℂ) * Complex.I * α * ((x:ℂ)+(s:ℂ)*Complex.I)
          = 2 * (Real.pi : ℂ) * Complex.I * (α * ((x:ℂ)+(s:ℂ)*Complex.I)) := by ring
      rw [harg]
    have hstep : (∫ x in a..b, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*α*((x:ℂ)+(s:ℂ)*Complex.I)))‖)
        = (1/‖α‖) * ∫ t in (0:ℝ)..L, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(p + (t:ℂ) • v)))‖ := by
      calc (∫ x in a..b, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*α*((x:ℂ)+(s:ℂ)*Complex.I)))‖)
          = ∫ x in a..b, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(α*((x:ℂ)+(s:ℂ)*Complex.I))))‖ := hLHS
        _ = (1/‖α‖) * ∫ t in (0:ℝ)..(‖α‖*(b-a)), 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(α*((a:ℂ)+(s:ℂ)*Complex.I) + (t:ℂ)*(α/‖α‖))))‖ := hcov
        _ = (1/‖α‖) * ∫ t in (0:ℝ)..L, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(p + (t:ℂ) • v)))‖ := by
              rw [hL]
              congr 1
    calc ∫ x in a..b, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*α*((x:ℂ)+(s:ℂ)*Complex.I)))‖
        = (1/‖α‖) * ∫ t in (0:ℝ)..L, 1/‖1 - Complex.exp (-(2*Real.pi*Complex.I*(p + (t:ℂ) • v)))‖ := hstep
      _ ≤ (1/‖α‖) * ((18/Real.pi)*(1+Real.log (2+2*u)) + L) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ ≤ (1/‖α‖) * (8*(‖α‖+1)*(1+Real.log (2+u))) :=
          mul_le_mul_of_nonneg_left harith (by positivity)
      _ = 8*(1+1/‖α‖)*(1+Real.log (2+u)) := by field_simp
      _ = 8*(1+1/‖α‖)*(1+Real.log (2+(b-a)/Ξ)) := by rw [hu]

end Work.Pert.V5
