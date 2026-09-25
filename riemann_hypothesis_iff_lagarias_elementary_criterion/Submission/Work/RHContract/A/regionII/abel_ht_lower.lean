import Mathlib

open MeasureTheory intervalIntegral

namespace Work.RHContract.A.regionII

theorem abel_ht_lower {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    2 * (1/(a * Real.log a) - 1/(b * Real.log b))
        - (1/(a * Real.log a) - 1/(b * Real.log b)) / (Real.log a + 1)
      ≤ ∫ t in a..b, (2 * Real.log t + 1)/(t^2 * (Real.log t)^2) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hla : 0 < Real.log a := Real.log_pos ha
  have hIcc : ∀ t ∈ Set.uIcc a b, 1 < t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  have hne : ∀ t ∈ Set.uIcc a b, t ≠ 0 := fun t ht =>
    ne_of_gt (lt_trans zero_lt_one (hIcc t ht))
  have hlne : ∀ t ∈ Set.uIcc a b, Real.log t ≠ 0 := fun t ht =>
    ne_of_gt (Real.log_pos (hIcc t ht))
  have hlogcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc a b) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hne x hx)
  have hgcont : ContinuousOn (fun t : ℝ => (Real.log t + 1)/(t^2 * (Real.log t)^2)) (Set.uIcc a b) := by
    apply ContinuousOn.div
    · exact hlogcont.add continuousOn_const
    · exact ((continuousOn_id' (Set.uIcc a b)).pow 2).mul (hlogcont.pow 2)
    · intro t ht
      exact mul_ne_zero (pow_ne_zero 2 (hne t ht)) (pow_ne_zero 2 (hlne t ht))
  have hhcont : ContinuousOn (fun t : ℝ => 1/(t^2 * Real.log t)) (Set.uIcc a b) := by
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact ((continuousOn_id' (Set.uIcc a b)).pow 2).mul hlogcont
    · intro t ht
      exact mul_ne_zero (pow_ne_zero 2 (hne t ht)) (hlne t ht)
  have hgi : IntervalIntegrable (fun t : ℝ => (Real.log t + 1)/(t^2 * (Real.log t)^2)) volume a b :=
    hgcont.intervalIntegrable
  have hhi : IntervalIntegrable (fun t : ℝ => 1/(t^2 * Real.log t)) volume a b :=
    hhcont.intervalIntegrable
  have habel {x : ℝ} (hx0 : x ≠ 0) (hlx : Real.log x ≠ 0) :
      HasDerivAt (fun t : ℝ => -((t * Real.log t)⁻¹))
        ((Real.log x + 1)/(x^2 * (Real.log x)^2)) x := by
    have hprod : x * Real.log x ≠ 0 := mul_ne_zero hx0 hlx
    have h1 : HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x := by
      have h : HasDerivAt (id * Real.log) (Real.log x + x * x⁻¹) x := by
        have := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)
        simpa using this
      have h' : HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + x * x⁻¹) x := h
      rw [mul_inv_cancel₀ hx0] at h'
      simpa using h'
    have h2 : HasDerivAt (fun t : ℝ => (t * Real.log t)⁻¹) (-(Real.log x + 1)/(x * Real.log x)^2) x := h1.inv hprod
    have h4 := h2.neg
    have he : -(-(Real.log x + 1)/(x * Real.log x)^2) = (Real.log x + 1)/(x^2 * (Real.log x)^2) := by
      field_simp
    rw [he] at h4
    exact h4
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => -((t * Real.log t)⁻¹)) ((Real.log x+1)/(x^2*(Real.log x)^2)) x := by
    intro x hx
    exact habel (hne x hx) (hlne x hx)
  have hFTC : ∫ t in a..b, (Real.log t + 1)/(t^2 * (Real.log t)^2) = 1/(a*Real.log a) - 1/(b*Real.log b) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => -((t*Real.log t)⁻¹))
      (f' := fun t : ℝ => (Real.log t + 1)/(t^2 * (Real.log t)^2)) hderiv hgi
    rw [h]
    simp only [one_div]
    ring
  set D : ℝ := 1/(a*Real.log a) - 1/(b*Real.log b) with hDdef
  set I : ℝ := ∫ t in a..b, 1/(t^2 * Real.log t) with hIdef
  have hf_eq0 : ∫ t in a..b, (2*Real.log t + 1)/(t^2*(Real.log t)^2)
      = (∫ t in a..b, (Real.log t + 1)/(t^2*(Real.log t)^2)) + ∫ t in a..b, 1/(t^2*Real.log t) := by
    rw [← intervalIntegral.integral_add hgi hhi]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : (1:ℝ) < t := lt_of_lt_of_le ha ht.1
    have hl : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have ht0 : t ≠ 0 := by linarith
    field_simp
    ring
  have hf_eq : ∫ t in a..b, (2*Real.log t + 1)/(t^2*(Real.log t)^2) = D + I := by
    rw [hf_eq0, hFTC, ← hIdef]
  have hDle : D ≤ (1 + 1/Real.log a) * I := by
    rw [hIdef, ← hFTC]
    rw [← intervalIntegral.integral_const_mul (1 + 1/Real.log a) (fun t => 1/(t^2*Real.log t))]
    apply intervalIntegral.integral_mono_on hab hgi (hhi.const_mul _)
    intro t ht
    have ht1 : (1:ℝ) < t := lt_of_lt_of_le ha ht.1
    have hl : 0 < Real.log t := Real.log_pos ht1
    have hlt : Real.log a ≤ Real.log t := Real.log_le_log ha0 ht.1
    have hkey : (Real.log t + 1)/(t^2*(Real.log t)^2) = (1/(t^2*Real.log t)) * (1 + 1/Real.log t) := by
      field_simp
    rw [hkey]
    have hle1 : (1 + 1/Real.log t) ≤ (1 + 1/Real.log a) := by
      have := one_div_le_one_div_of_le hla hlt
      linarith
    have hpos : 0 < 1/(t^2*Real.log t) :=
      one_div_pos.mpr (mul_pos (pow_pos (by linarith : (0:ℝ) < t) 2) hl)
    calc (1/(t^2*Real.log t)) * (1 + 1/Real.log t)
        ≤ (1/(t^2*Real.log t)) * (1 + 1/Real.log a) := mul_le_mul_of_nonneg_left hle1 (le_of_lt hpos)
      _ = (1 + 1/Real.log a) * (1/(t^2*Real.log t)) := by ring
  have hstep : D * Real.log a / (Real.log a + 1) ≤ I := by
    have hla1 : 0 < Real.log a + 1 := by linarith
    rw [div_le_iff₀ hla1]
    have h2 : D * Real.log a ≤ (Real.log a + 1) * I := by
      have hm := mul_le_mul_of_nonneg_right hDle (le_of_lt hla)
      have he : ((1 + 1/Real.log a) * I) * Real.log a = (Real.log a + 1) * I := by
        field_simp
      rwa [he] at hm
    rw [mul_comm (Real.log a + 1) I] at h2
    exact h2
  have hgoal : 2 * D - D/(Real.log a + 1) ≤ D + I := by
    have h1 : 2 * D - D/(Real.log a + 1) = D + D * Real.log a / (Real.log a + 1) := by
      field_simp
      ring
    rw [h1]
    linarith [hstep]
  rw [hf_eq]
  exact hgoal

end Work.RHContract.A.regionII
