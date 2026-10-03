import Mathlib

set_option autoImplicit false

namespace Work.FIArea2

open MeasureTheory
open scoped BigOperators

noncomputable section

/-! ### Elementary helper lemmas -/

/-- `arsinh x = log (x + √(1+x²))` -/
lemma si_arsinh_eq_log (x : ℝ) : Real.arsinh x = Real.log (x + Real.sqrt (1+x^2)) := by
  have hpos : 0 < x + Real.sqrt (1+x^2) := by
    have h1 : |x| < Real.sqrt (1+x^2) := by
      rw [Real.lt_sqrt (abs_nonneg x)]; rw [sq_abs]; linarith
    linarith [neg_abs_le x]
  rw [show Real.arsinh x = Real.log (Real.exp (Real.arsinh x)) from (Real.log_exp _).symm,
      Real.exp_arsinh]

/-- Derivative of `u ↦ arsinh(u/√c)`. -/
lemma si_hasDerivAt_arsinh_div (c : ℝ) (hc : 0 < c) (x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.arsinh (u/Real.sqrt c)) ((Real.sqrt (c+x^2))⁻¹) x := by
  have h1 : HasDerivAt (fun u : ℝ => u / Real.sqrt c) ((Real.sqrt c)⁻¹) x := by
    simpa using (hasDerivAt_id x).div_const (Real.sqrt c)
  have h2 := h1.arsinh
  have hsq : (x / Real.sqrt c) ^ 2 = x^2 / c := by rw [div_pow, Real.sq_sqrt hc.le]
  have hmain : (√(1 + (x / √c) ^ 2))⁻¹ * (√c)⁻¹ = (√(c + x ^ 2))⁻¹ := by
    have hmul : √(1+(x/√c)^2) * √c = √(c+x^2) := by
      rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 1+(x/√c)^2) c]
      congr 1; rw [hsq]; field_simp
    rw [← hmul, mul_inv]
  rw [smul_eq_mul, hmain] at h2
  exact h2

/-- Derivative of `u ↦ -arsinh(1/u)`. -/
lemma si_hasDerivAt_neg_arsinh_inv (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => - Real.arsinh (1/u)) ((x * Real.sqrt (1+x^2))⁻¹) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have h1 : HasDerivAt (fun u : ℝ => 1/u) (-(1/x^2)) x := by
    simpa [one_div] using (hasDerivAt_inv (x:=x) hxne)
  have h2 : HasDerivAt (fun u : ℝ => Real.arsinh (1/u))
      ((Real.sqrt (1+(1/x)^2))⁻¹ * (-(1/x^2))) x := by
    have := h1.arsinh; simpa [smul_eq_mul] using this
  have h3 : HasDerivAt (fun u : ℝ => - Real.arsinh (1/u))
      (-((Real.sqrt (1+(1/x)^2))⁻¹ * (-(1/x^2)))) x := h2.neg
  have hkey : (Real.sqrt (1 + (1/x)^2))⁻¹ * (1/x^2) = (x * Real.sqrt (1+x^2))⁻¹ := by
    have hsq : 1 + (1/x)^2 = (x^2+1)/x^2 := by field_simp
    rw [hsq, Real.sqrt_div (by positivity : (0:ℝ) ≤ x^2+1) (x^2), Real.sqrt_sq_eq_abs, abs_of_pos hx]
    have h1 : (√(x^2+1)/x)⁻¹ = x/√(x^2+1) := by rw [inv_div]
    rw [h1, show x^2+1 = 1+x^2 by ring, div_mul_eq_mul_div]; field_simp
  have hval : -((Real.sqrt (1+(1/x)^2))⁻¹ * (-(1/x^2))) = (x * Real.sqrt (1+x^2))⁻¹ := by
    rw [mul_neg, neg_neg]; exact hkey
  exact h3.congr_deriv hval

/-- Derivative of `u ↦ -log(1+√(1+u²))`. -/
lemma si_hasDerivAt_neg_log (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => - Real.log (1 + Real.sqrt (1+u^2)))
      (((Real.sqrt (1+x^2))⁻¹ - 1)/x) x := by
  have hder : HasDerivAt (fun u : ℝ => 1 + Real.sqrt (1+u^2)) (x / Real.sqrt (1+x^2)) x := by
    have h2 : HasDerivAt (fun u : ℝ => 1 + u^2) (2*x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add 1)
    have h3 : HasDerivAt (fun u : ℝ => Real.sqrt (1+u^2)) (2*x/(2*Real.sqrt (1+x^2))) x :=
      h2.sqrt (by positivity)
    have h3' : HasDerivAt (fun u : ℝ => Real.sqrt (1+u^2)) (x/Real.sqrt (1+x^2)) x :=
      h3.congr_deriv (by field_simp)
    simpa using h3'.const_add 1
  have h4 : HasDerivAt (fun u : ℝ => Real.log (1 + Real.sqrt (1+u^2)))
      ((x / Real.sqrt (1+x^2)) / (1 + Real.sqrt (1+x^2))) x := hder.log (by positivity)
  have h5 : HasDerivAt (fun u : ℝ => - Real.log (1 + Real.sqrt (1+u^2)))
      (-((x / Real.sqrt (1+x^2)) / (1 + Real.sqrt (1+x^2)))) x := h4.neg
  have hval : -((x / Real.sqrt (1+x^2)) / (1 + Real.sqrt (1+x^2)))
      = ((Real.sqrt (1+x^2))⁻¹ - 1)/x := by
    field_simp
    rw [show (1+Real.sqrt (1+x^2))*(1-Real.sqrt (1+x^2))
          = 1 - (Real.sqrt (1+x^2))^2 by ring, Real.sq_sqrt (by positivity)]
    ring
  exact h5.congr_deriv hval

/-- `((√(1+x²))⁻¹-1)/x = -x/(√(1+x²)(1+√(1+x²)))`. -/
lemma si_hkey (x : ℝ) (hx : x ≠ 0) :
    ((Real.sqrt (1+x^2))⁻¹ - 1)/x = -x/(Real.sqrt (1+x^2)*(1+Real.sqrt (1+x^2))) := by
  have h1 : Real.sqrt (1+x^2) ≠ 0 := by positivity
  have h2 : 1 + Real.sqrt (1+x^2) ≠ 0 := by positivity
  field_simp
  rw [show (1-Real.sqrt (1+x^2))*(1+Real.sqrt (1+x^2))
        = 1 - (Real.sqrt (1+x^2))^2 by ring, Real.sq_sqrt (by positivity)]
  ring

/-- `c/2 * u^(-4) = c/(2u^4)`. -/
lemma si_rpow_neg_four (c u : ℝ) (hu0 : 0 < u) : c/2 * u^(-4:ℝ) = c/(2*u^4) := by
  rw [show (-4:ℝ) = -((4:ℕ):ℝ) by norm_num, Real.rpow_neg (le_of_lt hu0), Real.rpow_natCast]
  field_simp

/-! ### Bound on `arsinh(1/√c) - log(2/√c)` -/
lemma si_arsinh_inv_sqrt_bound (c : ℝ) (hc : 0 < c) (hc4 : c ≤ 1/4) :
    |Real.arsinh (1/Real.sqrt c) - Real.log (2/Real.sqrt c)| ≤ c/4 := by
  have hcpos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsq : Real.sqrt (1+(1/Real.sqrt c)^2) = Real.sqrt (1+c)/Real.sqrt c := by
    have : 1+(1/Real.sqrt c)^2 = (1+c)/c := by
      field_simp; rw [Real.sq_sqrt hc.le]; ring
    rw [this, Real.sqrt_div (by positivity : (0:ℝ) ≤ 1+c) c]
  have hval : Real.arsinh (1/Real.sqrt c) - Real.log (2/Real.sqrt c)
      = Real.log ((1+Real.sqrt (1+c))/2) := by
    rw [si_arsinh_eq_log, hsq]
    rw [show 1/Real.sqrt c + Real.sqrt (1+c)/Real.sqrt c = (1+Real.sqrt (1+c))/Real.sqrt c by ring]
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by norm_num) (ne_of_gt hcpos)]
    rw [Real.log_div (by positivity) (by norm_num)]
    ring
  rw [hval, abs_of_nonneg]
  · have hs : Real.sqrt (1+c) ≤ 1 + c/2 := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1+c), Real.sqrt_nonneg (1+c),
        sq_nonneg (1+c/2)]
    have h1 : (1:ℝ) ≤ (1+Real.sqrt (1+c))/2 := by
      have : (1:ℝ) ≤ Real.sqrt (1+c) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
      linarith
    have h2 : (1+Real.sqrt (1+c))/2 ≤ 1 + c/4 := by linarith
    calc Real.log ((1+Real.sqrt (1+c))/2) ≤ Real.log (1 + c/4) :=
          Real.log_le_log (by linarith) h2
      _ ≤ c/4 := by
          have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + c/4)
          linarith
  · apply Real.log_nonneg
    have : (1:ℝ) ≤ Real.sqrt (1+c) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
    linarith

/-! ### D2: `∫₀¹ du/√(c+u²) = arsinh(1/√c)` -/
lemma si_integral_zero_one_inv_sqrt (c : ℝ) (hc : 0 < c) :
    (∫ u in (0:ℝ)..1, (Real.sqrt (c+u^2))⁻¹) = Real.arsinh (1/Real.sqrt c) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => si_hasDerivAt_arsinh_div c hc x)]
  · rw [zero_div, Real.arsinh_zero, sub_zero]
  · exact Continuous.intervalIntegrable (by
      apply Continuous.inv₀
      · fun_prop
      · intro x; positivity) 0 1

/-! ### D3: `∫₁^∞ du/(u√(1+u²)) = arsinh 1` -/
lemma si_integrableOn_inv_mul_sqrt :
    IntegrableOn (fun u : ℝ => (u * Real.sqrt (1+u^2))⁻¹) (Set.Ioi 1) := by
  apply MeasureTheory.Integrable.mono'
    ((integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (by norm_num : (0:ℝ)<1)).integrable)
  · exact ContinuousOn.aestronglyMeasurable (by
      apply ContinuousOn.inv₀
      · fun_prop
      · intro x hx
        exact mul_ne_zero (ne_of_gt (lt_trans one_pos hx))
          (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))) measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans one_pos hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (le_of_lt hu0), Real.rpow_natCast]
    apply inv_anti₀ (by positivity)
    have hle : u ≤ Real.sqrt (1+u^2) := by
      rw [Real.le_sqrt (le_of_lt hu0) (by positivity)]; linarith
    nlinarith [hle, hu0]

lemma si_integral_Ioi_one_inv_mul_sqrt :
    (∫ u in Set.Ioi 1, (u * Real.sqrt (1+u^2))⁻¹) = Real.arsinh 1 := by
  have hderiv : ∀ x ∈ Set.Ici (1:ℝ),
      HasDerivAt (fun u : ℝ => - Real.arsinh (1/u)) ((x * Real.sqrt (1+x^2))⁻¹) x :=
    fun x hx => si_hasDerivAt_neg_arsinh_inv x (lt_of_lt_of_le one_pos hx)
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) hderiv
      si_integrableOn_inv_mul_sqrt ?_]
  · simp
  · have h1 : Filter.Tendsto (fun u:ℝ => 1/u) Filter.atTop (nhds 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero
    have h2 : Filter.Tendsto (fun u:ℝ => Real.arsinh (1/u)) Filter.atTop (nhds (Real.arsinh 0)) :=
      h1.arsinh
    rw [Real.arsinh_zero] at h2
    simpa using h2.neg

/-! ### D4: `∫₀¹ ((√(1+u²))⁻¹-1)/u = log 2 - arsinh 1` -/
lemma si_corr_zero_value :
    (∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/u) = Real.log 2 - Real.arsinh 1 := by
  have hfuneq : (fun x : ℝ => ((Real.sqrt (1+x^2))⁻¹ - 1)/x)
      = fun x : ℝ => -x/(Real.sqrt (1+x^2)*(1+Real.sqrt (1+x^2))) := by
    funext x
    rcases eq_or_ne x 0 with hx | hx
    · subst hx; simp
    · exact si_hkey x hx
  rw [hfuneq]
  have hcont : ContinuousOn (fun u : ℝ => - Real.log (1 + Real.sqrt (1+u^2))) (Set.Icc 0 1) := by
    apply ContinuousOn.neg
    apply ContinuousOn.log
    · fun_prop
    · intro x hx; have := Real.sqrt_nonneg (1+x^2); linarith
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => - Real.log (1 + Real.sqrt (1+u^2)))
        ((fun x : ℝ => -x/(Real.sqrt (1+x^2)*(1+Real.sqrt (1+x^2)))) x) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have h := si_hasDerivAt_neg_log x hx0
    simp only []
    rw [← si_hkey x (ne_of_gt hx0)]
    exact h
  have hint : IntervalIntegrable
      (fun x : ℝ => -x/(Real.sqrt (1+x^2)*(1+Real.sqrt (1+x^2)))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x; positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (0:ℝ) ≤ 1 by norm_num)
      hcont hderiv hint]
  rw [si_arsinh_eq_log]
  norm_num
  ring

/-! ### D6: `|∫₁^∞ (1/√(c+u²) - 1/u)(√(1+u²))⁻¹| ≤ c/6` -/
lemma si_integrableOn_second (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹)
      (Set.Ioi 1) := by
  have hgint : MeasureTheory.Integrable (fun u : ℝ => c/2 * u^(-4:ℝ))
      (MeasureTheory.volume.restrict (Set.Ioi 1)) := by
    have h := (integrableOn_Ioi_rpow_of_lt (a:=-4) (c:=1) (by norm_num) (by norm_num : (0:ℝ)<1))
    exact h.integrable.const_mul (c/2)
  have hcont : ContinuousOn
      (fun u : ℝ => (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹) (Set.Ioi 1) := by
    have hf : ContinuousOn (fun u:ℝ => 1/Real.sqrt (c+u^2)) (Set.Ioi 1) := by
      apply ContinuousOn.div continuousOn_const (by fun_prop) (fun u hu => by positivity)
    have hg : ContinuousOn (fun u:ℝ => 1/u) (Set.Ioi 1) := by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
        (fun u hu => ne_of_gt (lt_trans one_pos hu))
    have hh : ContinuousOn (fun u:ℝ => (Real.sqrt (1+u^2))⁻¹) (Set.Ioi 1) := by
      apply ContinuousOn.inv₀ (by fun_prop) (fun u hu => by positivity)
    exact (hf.sub hg).mul hh
  refine MeasureTheory.Integrable.mono' hgint
    (ContinuousOn.aestronglyMeasurable hcont measurableSet_Ioi) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1:ℝ) < u := hu
  have hu0 : 0 < u := lt_trans one_pos hu1
  have hsq2 : u < Real.sqrt (c+u^2) := by rw [Real.lt_sqrt (le_of_lt hu0)]; nlinarith
  have hlt : 1/Real.sqrt (c+u^2) - 1/u < 0 := by
    rw [sub_neg]; exact one_div_lt_one_div_of_lt hu0 hsq2
  have hkey : 1/u - 1/Real.sqrt (c+u^2) = c/(u*Real.sqrt (c+u^2)*(Real.sqrt (c+u^2)+u)) := by
    field_simp
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ c+u^2)]
  rw [Real.norm_eq_abs, abs_of_neg (mul_neg_of_neg_of_pos hlt (by positivity))]
  rw [show -((1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹)
        = (1/u - 1/Real.sqrt (c+u^2)) * (Real.sqrt (1+u^2))⁻¹ by ring]
  rw [hkey, si_rpow_neg_four c u hu0]
  have hA : c/(u*Real.sqrt (c+u^2)*(Real.sqrt (c+u^2)+u)) ≤ c/(2*u^3) := by
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have h1 : u*u ≤ u*Real.sqrt (c+u^2) := mul_le_mul_of_nonneg_left (le_of_lt hsq2) hu0.le
    have h2 : 2*u ≤ Real.sqrt (c+u^2)+u := by linarith
    calc 2*u^3 = (u*u)*(2*u) := by ring
      _ ≤ (u*Real.sqrt (c+u^2))*(Real.sqrt (c+u^2)+u) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = u*Real.sqrt (c+u^2)*(Real.sqrt (c+u^2)+u) := by ring
  have hB : (Real.sqrt (1+u^2))⁻¹ ≤ 1/u := by
    rw [one_div, inv_le_inv₀ (by positivity : 0 < Real.sqrt (1+u^2)) hu0]
    rw [Real.le_sqrt (le_of_lt hu0) (by positivity)]; linarith
  calc c/(u*Real.sqrt (c+u^2)*(Real.sqrt (c+u^2)+u)) * (Real.sqrt (1+u^2))⁻¹
      ≤ (c/(2*u^3)) * (1/u) := mul_le_mul hA hB (by positivity) (by positivity)
    _ = c/(2*u^4) := by ring

lemma si_second_integral_bound (c : ℝ) (hc : 0 < c) :
    |∫ u in Set.Ioi 1, (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹| ≤ c/6 := by
  have hgint : MeasureTheory.Integrable (fun u : ℝ => c/2 * u^(-4:ℝ))
      (MeasureTheory.volume.restrict (Set.Ioi 1)) := by
    have h := (integrableOn_Ioi_rpow_of_lt (a:=-4) (c:=1) (by norm_num) (by norm_num : (0:ℝ)<1))
    exact h.integrable.const_mul (c/2)
  have hbound : ∀ u ∈ Set.Ioi 1,
      ‖(1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹‖ ≤ c/2 * u^(-4:ℝ) := by
    intro u hu
    have hu1 : (1:ℝ) < u := hu
    have hu0 : 0 < u := lt_trans one_pos hu1
    have hsq2 : u < Real.sqrt (c+u^2) := by rw [Real.lt_sqrt (le_of_lt hu0)]; nlinarith
    have hlt : 1/Real.sqrt (c+u^2) - 1/u < 0 := by
      rw [sub_neg]; exact one_div_lt_one_div_of_lt hu0 hsq2
    have hkey : 1/u - 1/Real.sqrt (c+u^2) = c/(u*Real.sqrt (c+u^2)*(Real.sqrt (c+u^2)+u)) := by
      field_simp
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ c+u^2)]
    rw [Real.norm_eq_abs, abs_of_neg (mul_neg_of_neg_of_pos hlt (by positivity))]
    rw [show -((1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹)
          = (1/u - 1/Real.sqrt (c+u^2)) * (Real.sqrt (1+u^2))⁻¹ by ring]
    rw [hkey, si_rpow_neg_four c u hu0]
    have hA : c/(u*Real.sqrt (c+u^2)*(Real.sqrt (c+u^2)+u)) ≤ c/(2*u^3) := by
      apply div_le_div_of_nonneg_left hc.le (by positivity)
      have h1 : u*u ≤ u*Real.sqrt (c+u^2) := mul_le_mul_of_nonneg_left (le_of_lt hsq2) hu0.le
      have h2 : 2*u ≤ Real.sqrt (c+u^2)+u := by linarith
      calc 2*u^3 = (u*u)*(2*u) := by ring
        _ ≤ (u*Real.sqrt (c+u^2))*(Real.sqrt (c+u^2)+u) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = u*Real.sqrt (c+u^2)*(Real.sqrt (c+u^2)+u) := by ring
    have hB : (Real.sqrt (1+u^2))⁻¹ ≤ 1/u := by
      rw [one_div, inv_le_inv₀ (by positivity : 0 < Real.sqrt (1+u^2)) hu0]
      rw [Real.le_sqrt (le_of_lt hu0) (by positivity)]; linarith
    calc c/(u*Real.sqrt (c+u^2)*(Real.sqrt (c+u^2)+u)) * (Real.sqrt (1+u^2))⁻¹
        ≤ (c/(2*u^3)) * (1/u) := mul_le_mul hA hB (by positivity) (by positivity)
      _ = c/(2*u^4) := by ring
  calc |∫ u in Set.Ioi 1, (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹|
      = ‖∫ u in Set.Ioi 1, (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∫ u in Set.Ioi 1,
          ‖(1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ u in Set.Ioi 1, c/2 * u^(-4:ℝ) := by
        apply MeasureTheory.integral_mono_ae (si_integrableOn_second c hc).norm hgint
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
        exact hbound u hu
    _ = c/6 := by
        rw [MeasureTheory.integral_const_mul,
            integral_Ioi_rpow_of_lt (a:=-4) (c:=1) (by norm_num) (by norm_num : (0:ℝ)<1)]
        norm_num
        ring

/-! ### D5: bound on the difference of the two `Corr` integrals -/
lemma si_corr_diff_bound (c : ℝ) (hc : 0 < c) (hc4 : c ≤ 1 / 4) :
    |(∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2))
      - (∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/u)| ≤ c/4 + c/8 * Real.log (1/c) := by
  have hcpos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsc1 : Real.sqrt c ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have hfcont : Continuous (fun u : ℝ => ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2)) := by
    apply Continuous.div
    · apply Continuous.sub
      · apply Continuous.inv₀ (by fun_prop) (fun u => by positivity)
      · fun_prop
    · fun_prop
    · intro u; positivity
  have hgeq : (fun u : ℝ => ((Real.sqrt (1+u^2))⁻¹ - 1)/u)
      = fun u : ℝ => -u/(Real.sqrt (1+u^2)*(1+Real.sqrt (1+u^2))) := by
    funext u; rcases eq_or_ne u 0 with h|h
    · subst h; simp
    · exact si_hkey u h
  have hgcont : Continuous (fun u : ℝ => ((Real.sqrt (1+u^2))⁻¹ - 1)/u) := by
    rw [hgeq]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro u; positivity
  have hfint : IntervalIntegrable (fun u : ℝ => ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2))
      volume 0 1 := hfcont.intervalIntegrable 0 1
  have hgint : IntervalIntegrable (fun u : ℝ => ((Real.sqrt (1+u^2))⁻¹ - 1)/u)
      volume 0 1 := hgcont.intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hfint hgint]
  have hFcont : Continuous (fun u : ℝ =>
      ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2) - ((Real.sqrt (1+u^2))⁻¹ - 1)/u) :=
    hfcont.sub hgcont
  have hH : ∀ u : ℝ, 0 < u → u ≤ 1 → |(Real.sqrt (1+u^2))⁻¹ - 1| ≤ u^2/2 := by
    intro u hu0 hu1
    have hsqrt1 : (1:ℝ) ≤ Real.sqrt (1+u^2) := by rw [Real.one_le_sqrt]; nlinarith [sq_nonneg u]
    have hle1 : (Real.sqrt (1+u^2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt1
    rw [abs_of_nonpos (by linarith)]
    have hkey : 1 - (Real.sqrt (1+u^2))⁻¹
        = u^2/(Real.sqrt (1+u^2)*(Real.sqrt (1+u^2)+1)) := by
      have h1 : Real.sqrt (1+u^2) ≠ 0 := by positivity
      have h2 : Real.sqrt (1+u^2)+1 ≠ 0 := by positivity
      field_simp
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1+u^2)]
    rw [show -((Real.sqrt (1+u^2))⁻¹ - 1) = 1 - (Real.sqrt (1+u^2))⁻¹ by ring, hkey]
    have hm : (2:ℝ) ≤ Real.sqrt (1+u^2)*(Real.sqrt (1+u^2)+1) := by
      have := mul_le_mul hsqrt1 (show (1:ℝ)+1 ≤ Real.sqrt (1+u^2)+1 by linarith)
        (by norm_num) (by positivity)
      linarith
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hm
  have hK1 : ∀ u : ℝ, 0 < u → |1/Real.sqrt (c+u^2) - 1/u| ≤ 1/u := by
    intro u hu0
    have hle : 1/Real.sqrt (c+u^2) - 1/u ≤ 0 := by
      rw [sub_nonpos, div_le_div_iff₀ (by positivity) hu0, one_mul, one_mul,
          Real.le_sqrt (le_of_lt hu0) (by positivity)]
      linarith
    rw [abs_of_nonpos hle, neg_sub]
    have : (0:ℝ) ≤ 1/Real.sqrt (c+u^2) := by positivity
    linarith
  have hK2 : ∀ u : ℝ, 0 < u → |1/Real.sqrt (c+u^2) - 1/u| ≤ c/(2*u^3) := by
    intro u hu0
    have hle : 1/Real.sqrt (c+u^2) - 1/u ≤ 0 := by
      rw [sub_nonpos, div_le_div_iff₀ (by positivity) hu0, one_mul, one_mul,
          Real.le_sqrt (le_of_lt hu0) (by positivity)]
      linarith
    rw [abs_of_nonpos hle, neg_sub]
    have hkey : 1/u - 1/Real.sqrt (c+u^2) = c/(u*Real.sqrt (c+u^2)*(Real.sqrt (c+u^2)+u)) := by
      field_simp
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ c+u^2)]
    rw [hkey]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have h1 : u*u ≤ u*Real.sqrt (c+u^2) := by
      apply mul_le_mul_of_nonneg_left _ hu0.le
      rw [Real.le_sqrt (le_of_lt hu0) (by positivity)]; linarith
    have h2 : 2*u ≤ Real.sqrt (c+u^2)+u := by
      have : u ≤ Real.sqrt (c+u^2) := by rw [Real.le_sqrt (le_of_lt hu0) (by positivity)]; linarith
      linarith
    calc 2*u^3 = (u*u)*(2*u) := by ring
      _ ≤ (u*Real.sqrt (c+u^2))*(Real.sqrt (c+u^2)+u) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = u*Real.sqrt (c+u^2)*(Real.sqrt (c+u^2)+u) := by ring
  have heq : ∀ u : ℝ, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2) - ((Real.sqrt (1+u^2))⁻¹ - 1)/u
      = ((Real.sqrt (1+u^2))⁻¹ - 1) * (1/Real.sqrt (c+u^2) - 1/u) := by intro u; ring
  have hb1 : ∀ u ∈ Set.Icc (0:ℝ) (Real.sqrt c),
      |((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2) - ((Real.sqrt (1+u^2))⁻¹ - 1)/u| ≤ u/2 := by
    intro u hu
    rcases eq_or_ne u 0 with h|h
    · subst h; simp
    · have hu0 : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm h)
      have hu1 : u ≤ 1 := le_trans hu.2 hsc1
      rw [heq u, abs_mul]
      calc |(Real.sqrt (1+u^2))⁻¹ - 1| * |1/Real.sqrt (c+u^2) - 1/u|
          ≤ (u^2/2) * (1/u) := mul_le_mul (hH u hu0 hu1) (hK1 u hu0) (abs_nonneg _) (by positivity)
        _ = u/2 := by field_simp
  have hb2 : ∀ u ∈ Set.Icc (Real.sqrt c) 1,
      |((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2) - ((Real.sqrt (1+u^2))⁻¹ - 1)/u| ≤ c/(4*u) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hcpos hu.1
    have hu1 : u ≤ 1 := hu.2
    rw [heq u, abs_mul]
    calc |(Real.sqrt (1+u^2))⁻¹ - 1| * |1/Real.sqrt (c+u^2) - 1/u|
        ≤ (u^2/2) * (c/(2*u^3)) := mul_le_mul (hH u hu0 hu1) (hK2 u hu0) (abs_nonneg _) (by positivity)
      _ = c/(4*u) := by field_simp; norm_num
  have hFint0 : IntervalIntegrable
      (fun u : ℝ => |((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2) - ((Real.sqrt (1+u^2))⁻¹ - 1)/u|)
      volume 0 (Real.sqrt c) := (hFcont.intervalIntegrable 0 (Real.sqrt c)).abs
  have hFint1 : IntervalIntegrable
      (fun u : ℝ => |((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2) - ((Real.sqrt (1+u^2))⁻¹ - 1)/u|)
      volume (Real.sqrt c) 1 := (hFcont.intervalIntegrable (Real.sqrt c) 1).abs
  calc |∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2)
        - ((Real.sqrt (1+u^2))⁻¹ - 1)/u|
      ≤ ∫ u in (0:ℝ)..1,
          |((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2) - ((Real.sqrt (1+u^2))⁻¹ - 1)/u| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ = (∫ u in (0:ℝ)..Real.sqrt c,
          |((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2) - ((Real.sqrt (1+u^2))⁻¹ - 1)/u|)
        + (∫ u in (Real.sqrt c)..1,
          |((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2) - ((Real.sqrt (1+u^2))⁻¹ - 1)/u|) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hFint0 hFint1]
    _ ≤ (∫ u in (0:ℝ)..Real.sqrt c, u/2) + (∫ u in (Real.sqrt c)..1, c/(4*u)) := by
        apply add_le_add
        · apply intervalIntegral.integral_mono_on hcpos.le hFint0
            (Continuous.intervalIntegrable (by fun_prop) 0 (Real.sqrt c))
          intro u hu; exact hb1 u hu
        · apply intervalIntegral.integral_mono_on hsc1 hFint1
            (ContinuousOn.intervalIntegrable (by
              apply ContinuousOn.div continuousOn_const
              · fun_prop
              · intro u hu
                rw [Set.uIcc_of_le hsc1] at hu
                exact ne_of_gt (mul_pos (by norm_num) (lt_of_lt_of_le hcpos hu.1))))
          intro u hu; exact hb2 u hu
    _ = c/4 + c/8 * Real.log (1/c) := by
        have h1 : (∫ u in (0:ℝ)..Real.sqrt c, u/2) = c/4 := by
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
              (f := fun u : ℝ => u^2/4) (f' := fun u : ℝ => u/2) (fun x _ => by
                refine ((hasDerivAt_pow 2 x).div_const 4).congr_deriv ?_
                push_cast
                ring)
              (Continuous.intervalIntegrable (by fun_prop) 0 (Real.sqrt c))]
          rw [Real.sq_sqrt hc.le]
          ring
        have hint3 : IntervalIntegrable (fun u : ℝ => 1/u) volume (Real.sqrt c) 1 := by
          apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div continuousOn_const continuousOn_id
          intro u hu
          rw [Set.uIcc_of_le hsc1] at hu
          exact ne_of_gt (lt_of_lt_of_le hcpos hu.1)
        have h2 : (∫ u in (Real.sqrt c)..1, c/(4*u)) = c/8 * Real.log (1/c) := by
          rw [show (fun u : ℝ => c/(4*u)) = (fun u : ℝ => c/4 * (1/u)) by funext u; ring]
          rw [intervalIntegral.integral_const_mul]
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
              (f := Real.log) (f' := fun u : ℝ => 1/u) (fun x hx => by
                have hx0 : 0 < x := by
                  rw [Set.uIcc_of_le hsc1] at hx
                  exact lt_of_lt_of_le hcpos hx.1
                simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx0))
              hint3]
          rw [Real.log_one, Real.log_sqrt hc.le, one_div, Real.log_inv]
          ring
        rw [h1, h2]

/-! ### D1: the `sinh` substitution -/
lemma si_sinh_integral_changeOfVariables (c : ℝ) (hc : 0 < c) :
    (∫ v in Set.Ioi 0, (c + (Real.sinh v)^2)^(-(1:ℝ)/2))
    = ∫ u in Set.Ioi 0, (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹ := by
  have himg : Real.sinh '' Set.Ioi 0 = Set.Ioi 0 := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Real.sinh_pos_iff).mpr hx
    · intro hy
      obtain ⟨x, hx⟩ := Real.sinh_surjective y
      refine ⟨x, ?_, hx⟩
      rw [← hx] at hy
      exact (Real.sinh_pos_iff).mp hy
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Set.Ioi 0)
      (f := Real.sinh) (f' := Real.cosh) measurableSet_Ioi
      (fun x _ => (Real.hasDerivAt_sinh x).hasDerivWithinAt)
      (fun x _ y _ hxy => Real.sinh_inj.mp hxy)
      (fun u => (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹)
  rw [himg] at h
  rw [h]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change (c + (Real.sinh x)^2)^(-(1:ℝ)/2)
      = |Real.cosh x| • ((Real.sqrt (1+(Real.sinh x)^2))⁻¹ * (Real.sqrt (c+(Real.sinh x)^2))⁻¹)
  rw [smul_eq_mul, abs_of_pos (Real.cosh_pos x)]
  have hcosh : Real.sqrt (1+(Real.sinh x)^2) = Real.cosh x := by
    rw [add_comm 1, ← Real.cosh_sq, Real.sqrt_sq_eq_abs, abs_of_pos (Real.cosh_pos x)]
  rw [hcosh, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.cosh_pos x)), one_mul]
  rw [show (c + (Real.sinh x)^2)^(-(1:ℝ)/2) = ((c + (Real.sinh x)^2)^((1:ℝ)/2))⁻¹ by
        rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (by positivity)]]
  rw [Real.sqrt_eq_rpow]

/-! ### Integrability of the substitution integrand -/
lemma si_G_integrableOn (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹) (Set.Ioi 0) := by
  have hGcont : Continuous (fun u : ℝ => (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹) := by
    apply Continuous.mul
    · apply Continuous.inv₀ (by fun_prop) (fun u => by positivity)
    · apply Continuous.inv₀ (by fun_prop) (fun u => by positivity)
  have h1 : IntegrableOn (fun u : ℝ => (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹)
      (Set.Icc 0 1) := by
    refine IntegrableOn.of_bound ?_ hGcont.aestronglyMeasurable (1/Real.sqrt c) ?_
    · rw [Real.volume_Icc]; norm_num
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_inv, ← one_div]
      apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hc)
      have hle1 : (1:ℝ) ≤ Real.sqrt (1+u^2) := by rw [Real.one_le_sqrt]; nlinarith [sq_nonneg u]
      have hle2 : Real.sqrt c ≤ Real.sqrt (c+u^2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])
      have := mul_le_mul hle1 hle2 (by positivity) (by positivity)
      simpa using this
  have h2 : IntegrableOn (fun u : ℝ => (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹)
      (Set.Ioi 1) := by
    apply MeasureTheory.Integrable.mono'
      ((integrableOn_Ioi_rpow_of_lt (a:=-2) (c:=1) (by norm_num) (by norm_num : (0:ℝ)<1)).integrable)
    · exact ContinuousOn.aestronglyMeasurable hGcont.continuousOn measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := lt_trans one_pos hu
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (le_of_lt hu0), Real.rpow_natCast]
      have hle1 : u ≤ Real.sqrt (1+u^2) := by
        rw [Real.le_sqrt (le_of_lt hu0) (by positivity)]; linarith
      have hle2 : u ≤ Real.sqrt (c+u^2) := by
        rw [Real.le_sqrt (le_of_lt hu0) (by positivity)]; linarith
      have hA : (Real.sqrt (1+u^2))⁻¹ ≤ u⁻¹ := inv_anti₀ hu0 hle1
      have hB : (Real.sqrt (c+u^2))⁻¹ ≤ u⁻¹ := inv_anti₀ hu0 hle2
      have hm := mul_le_mul hA hB (by positivity) (by positivity)
      have huu : u⁻¹ * u⁻¹ = (u^2)⁻¹ := by rw [sq, mul_inv]
      rw [huu] at hm
      exact hm
  have h3 : IntegrableOn (fun u : ℝ => (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹)
      (Set.Ici 0) := by
    rw [← Set.Icc_union_Ioi_eq_Ici (show (0:ℝ) ≤ 1 by norm_num)]
    exact h1.union h2
  exact h3.mono_set Set.Ioi_subset_Ici_self

/-! ### The main asymptotic -/
theorem sinhIntegral_asymptotic (c : ℝ) (hc : 0 < c) (hc4 : c ≤ 1 / 4) :
    |2 * (∫ v in Set.Ioi 0, (c + (Real.sinh v) ^ 2) ^ (-(1 : ℝ) / 2)) - Real.log (16 / c)|
      ≤ 8 * c * Real.log (1 / c) + 8 * c := by
  have hcpos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  rw [si_sinh_integral_changeOfVariables c hc]
  have hGint0 : IntegrableOn (fun u : ℝ => (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹)
      (Set.Ioi 0) := si_G_integrableOn c hc
  have hsub := intervalIntegral.integral_Ioi_sub_Ioi
      (f := fun u : ℝ => (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹) hGint0
      (show (0:ℝ) ≤ 1 by norm_num)
  rw [show (∫ u in Set.Ioi 0, (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹)
      = (∫ u in (0:ℝ)..1, (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹)
      + (∫ u in Set.Ioi 1, (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹) from by linarith [hsub]]
  have hP1 : (∫ u in (0:ℝ)..1, (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹)
      = Real.arsinh (1/Real.sqrt c)
        + (∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2)) := by
    have hpt : ∀ u : ℝ, (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹
        = (Real.sqrt (c+u^2))⁻¹ + ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2) := by
      intro u; ring
    rw [intervalIntegral.integral_congr (fun u _ => hpt u)]
    rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by
          apply Continuous.inv₀ (by fun_prop) (fun u => by positivity)) 0 1)
        (Continuous.intervalIntegrable (by
          apply Continuous.div
          · apply Continuous.sub
            · apply Continuous.inv₀ (by fun_prop) (fun u => by positivity)
            · fun_prop
          · fun_prop
          · intro u; positivity) 0 1)]
    rw [si_integral_zero_one_inv_sqrt c hc]
  have hP2 : (∫ u in Set.Ioi 1, (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹)
      = Real.arsinh 1
        + (∫ u in Set.Ioi 1, (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹) := by
    have hpt : ∀ u : ℝ, (Real.sqrt (1+u^2))⁻¹ * (Real.sqrt (c+u^2))⁻¹
        = (u * Real.sqrt (1+u^2))⁻¹
          + (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹ := by
      intro u; ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u)]
    rw [MeasureTheory.integral_add si_integrableOn_inv_mul_sqrt (si_integrableOn_second c hc)]
    rw [si_integral_Ioi_one_inv_mul_sqrt]
  rw [hP1, hP2]
  have hC0 := si_corr_zero_value
  have h1 := si_arsinh_inv_sqrt_bound c hc hc4
  have h2 := si_corr_diff_bound c hc hc4
  have h3 := si_second_integral_bound c hc
  rw [hC0] at h2
  have heq : 2 * (Real.arsinh (1/Real.sqrt c)
        + (∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2))
        + (Real.arsinh 1 + (∫ u in Set.Ioi 1, (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹)))
      - Real.log (16 / c)
      = 2 * ((Real.arsinh (1/Real.sqrt c) - Real.log (2/Real.sqrt c))
        + ((∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2))
            - (Real.log 2 - Real.arsinh 1))
        + (∫ u in Set.Ioi 1, (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹)) := by
    have hlog1 : Real.log (16/c) = 2*Real.log (4/Real.sqrt c) := by
      rw [show (16:ℝ)/c = (4/Real.sqrt c)^2 by
            rw [div_pow, Real.sq_sqrt hc.le]; ring]
      rw [Real.log_pow]; ring
    have hlog2 : Real.log (4/Real.sqrt c) = Real.log (2/Real.sqrt c) + Real.log 2 := by
      rw [show (4:ℝ)/Real.sqrt c = (2/Real.sqrt c)*2 by ring]
      rw [Real.log_mul (by positivity) (by norm_num)]
    rw [hlog1, hlog2]; ring
  rw [heq, abs_mul]
  have hlg : 0 ≤ Real.log (1/c) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hc]; linarith
  have hinner : |(Real.arsinh (1/Real.sqrt c) - Real.log (2/Real.sqrt c))
        + ((∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2))
            - (Real.log 2 - Real.arsinh 1))
        + (∫ u in Set.Ioi 1, (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹)|
      ≤ c/4 + (c/4 + c/8 * Real.log (1/c)) + c/6 := by
    have htri1 : |(Real.arsinh (1/Real.sqrt c) - Real.log (2/Real.sqrt c))
          + ((∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2))
            - (Real.log 2 - Real.arsinh 1))|
        ≤ |Real.arsinh (1/Real.sqrt c) - Real.log (2/Real.sqrt c)|
          + |(∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2))
            - (Real.log 2 - Real.arsinh 1)| := abs_add_le _ _
    have htri2 : |(Real.arsinh (1/Real.sqrt c) - Real.log (2/Real.sqrt c))
          + ((∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2))
            - (Real.log 2 - Real.arsinh 1))
          + (∫ u in Set.Ioi 1, (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹)|
        ≤ |(Real.arsinh (1/Real.sqrt c) - Real.log (2/Real.sqrt c))
          + ((∫ u in (0:ℝ)..1, ((Real.sqrt (1+u^2))⁻¹ - 1)/Real.sqrt (c+u^2))
            - (Real.log 2 - Real.arsinh 1))|
          + |(∫ u in Set.Ioi 1, (1/Real.sqrt (c+u^2) - 1/u) * (Real.sqrt (1+u^2))⁻¹)| :=
        abs_add_le _ _
    linarith [htri1, htri2, h1, h2, h3]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [hinner, hlg, hc, hc4, Real.sqrt_nonneg c]

end

end Work.FIArea2
