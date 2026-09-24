import Mathlib

namespace Work.NumberTheory.Chen.BTermCount

open MeasureTheory intervalIntegral

/-- `log 2 < 6931471808/10^10` in rational form. -/
lemma log_two_lt_rat : Real.log 2 < 6931471808/10^10 := by
  have h := Real.log_two_lt_d9
  have heq : (0.6931471808 : ℝ) = 6931471808/10^10 := by norm_num
  linarith

/-- `log (1 + x) ≤ x - x²/2 + x³/3` for `x ≥ 0`. -/
lemma log_one_add_le_three {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x^2/2 + x^3/3 := by
  have hderiv : ∀ t : ℝ, -1 < t →
      deriv (fun s : ℝ => Real.log (1+s) - (s - s^2/2 + s^3/3)) t = 1/(1+t) - (1 - t + t^2) := by
    intro t ht
    have hne : (1:ℝ) + t ≠ 0 := ne_of_gt (show (0:ℝ) < 1 + t by linarith)
    have hlog : deriv (fun s : ℝ => Real.log (1+s)) t = 1/(1+t) := by
      have h : (fun s : ℝ => Real.log (1 + s)) = Real.log ∘ (fun s : ℝ => 1 + s) := rfl
      rw [h, Real.deriv_log_comp_eq_logDeriv (by fun_prop) hne]
      simp [logDeriv]
    have hpoly : deriv (fun s : ℝ => s - s^2/2 + s^3/3) t = 1 - t + t^2 := by
      have h1d : deriv (fun s : ℝ => s) t = 1 := by have h := hasDerivAt_id t; simpa using h.deriv
      have h2d : deriv (fun s : ℝ => s^2) t = 2*t := by
        have h := (hasDerivAt_id t).pow 2; simpa using h.deriv
      have h3d : deriv (fun s : ℝ => s^3) t = 3*t^2 := by
        have h := (hasDerivAt_id t).pow 3; simpa using h.deriv
      change deriv ((fun s : ℝ => s) - (fun s : ℝ => s^2/2) + (fun s : ℝ => s^3/3)) t = _
      rw [deriv_add (by fun_prop) (by fun_prop), deriv_sub (by fun_prop) (by fun_prop),
        deriv_div_const, deriv_div_const, h1d, h2d, h3d]
      ring
    have hd1 : DifferentiableAt ℝ (fun s : ℝ => Real.log (1+s)) t :=
      (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => 1 + s) t).log hne
    change deriv ((fun s : ℝ => Real.log (1+s)) - (fun s : ℝ => s - s^2/2 + s^3/3)) t = _
    rw [deriv_sub hd1 (by fun_prop), hlog, hpoly]
  have hanti : AntitoneOn (fun t : ℝ => Real.log (1+t) - (t - t^2/2 + t^3/3)) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · apply ContinuousOn.sub
      · apply ContinuousOn.log (by fun_prop)
        intro t ht
        have ht' : (0:ℝ) ≤ t := ht
        linarith
      · fun_prop
    · apply DifferentiableOn.sub
      · apply DifferentiableOn.log (by fun_prop)
        intro t ht
        rw [interior_Ici] at ht
        have ht' : (0:ℝ) < t := ht
        linarith
      · fun_prop
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : (0:ℝ) < t := ht
      rw [hderiv t (by linarith)]
      rw [show (1:ℝ)/(1+t) - (1 - t + t^2) = -(t^3/(1+t)) by field_simp; try ring]
      have : 0 ≤ t^3/(1+t) := by positivity
      linarith
  have h : (fun t : ℝ => Real.log (1+t) - (t - t^2/2 + t^3/3)) x
      ≤ (fun t : ℝ => Real.log (1+t) - (t - t^2/2 + t^3/3)) 0 :=
    hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  norm_num at h
  linarith

/-- `log (1 - x) ≤ -x - x²/2 - x³/3 - x⁴/4` for `0 ≤ x < 1`. -/
lemma log_one_sub_le_four {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x^2/2 - x^3/3 - x^4/4 := by
  have hderiv : ∀ t : ℝ, t < 1 →
      deriv (fun s : ℝ => Real.log (1-s) + s + s^2/2 + s^3/3 + s^4/4) t
        = -1/(1-t) + 1 + t + t^2 + t^3 := by
    intro t ht
    have hne : (1:ℝ) - t ≠ 0 := ne_of_gt (show (0:ℝ) < 1 - t by linarith)
    have hlog : deriv (fun s : ℝ => Real.log (1 - s)) t = -1/(1-t) := by
      have h : (fun s : ℝ => Real.log (1 - s)) = Real.log ∘ (fun s : ℝ => 1 - s) := rfl
      rw [h, Real.deriv_log_comp_eq_logDeriv (by fun_prop) hne]
      simp [logDeriv]
    have h1d : deriv (fun s : ℝ => s) t = 1 := by simp
    have h2d : deriv (fun s : ℝ => s^2/2) t = t := by rw [deriv_div_const]; simp
    have h3d : deriv (fun s : ℝ => s^3/3) t = t^2 := by rw [deriv_div_const]; simp
    have h4d : deriv (fun s : ℝ => s^4/4) t = t^3 := by rw [deriv_div_const]; simp
    have hd1 : DifferentiableAt ℝ (fun s : ℝ => Real.log (1-s)) t :=
      (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => 1 - s) t).log hne
    change deriv ((fun s : ℝ => Real.log (1-s)) + (fun s : ℝ => s) + (fun s : ℝ => s^2/2)
        + (fun s : ℝ => s^3/3) + (fun s : ℝ => s^4/4)) t = _
    rw [deriv_add (by fun_prop) (by fun_prop), deriv_add (by fun_prop) (by fun_prop),
        deriv_add (by fun_prop) (by fun_prop), deriv_add hd1 (by fun_prop),
        hlog, h1d, h2d, h3d, h4d]
  have hanti : AntitoneOn (fun t : ℝ => Real.log (1-t) + t + t^2/2 + t^3/3 + t^4/4) (Set.Ico 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 1)
    · have hlogc : ContinuousOn (fun t : ℝ => Real.log (1-t)) (Set.Ico 0 1) := by
        apply ContinuousOn.log (by fun_prop)
        intro t ht
        have ht1 : (0:ℝ) ≤ t := ht.1
        have ht2 : t < 1 := ht.2
        linarith
      exact ((((hlogc.add continuousOn_id).add (by fun_prop)).add (by fun_prop)).add (by fun_prop))
    · have hlogd : DifferentiableOn ℝ (fun t : ℝ => Real.log (1-t)) (interior (Set.Ico 0 1)) := by
        apply DifferentiableOn.log (by fun_prop)
        intro t ht
        rw [interior_Ico] at ht
        have ht2 : t < 1 := ht.2
        linarith
      exact ((((hlogd.add (by fun_prop)).add (by fun_prop)).add (by fun_prop)).add (by fun_prop))
    · intro t ht
      rw [interior_Ico] at ht
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := ht.2
      rw [hderiv t ht1]
      rw [show -1/(1-t) + 1 + t + t^2 + t^3 = -(t^4/(1-t)) by
        have hne : (1:ℝ) - t ≠ 0 := ne_of_gt (by linarith)
        field_simp
        ring]
      have h1t : (0:ℝ) < 1 - t := by linarith
      have : 0 ≤ t^4/(1-t) := by positivity
      linarith
  have h : (fun t : ℝ => Real.log (1-t) + t + t^2/2 + t^3/3 + t^4/4) x
      ≤ (fun t : ℝ => Real.log (1-t) + t + t^2/2 + t^3/3 + t^4/4) 0 :=
    hanti ⟨le_refl 0, by norm_num⟩ ⟨hx0, hx1⟩ hx0
  norm_num at h
  linarith

/-- `∫_a^b log u / u = (log b)²/2 - (log a)²/2` for `0 < a ≤ b`. -/
lemma integral_log_div_self (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, Real.log u / u) = (Real.log b)^2/2 - (Real.log a)^2/2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => (Real.log u)^2/2) (f' := fun u : ℝ => Real.log u/u)]
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hder : deriv (fun u : ℝ => (Real.log u)^2/2) x = Real.log x/x := by
      have h := (((Real.hasDerivAt_log hxne).pow 2).div_const 2).deriv
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
    have hdiff : DifferentiableAt ℝ (fun u : ℝ => (Real.log u)^2/2) x :=
      ((Real.differentiableAt_log hxne).pow 2).div_const 2
    simpa only [hder] using hdiff.hasDerivAt
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)

/-- `∫_a^b 1/u = log b - log a` for `0 < a ≤ b`. -/
lemma integral_inv_eq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, 1/u) = Real.log b - Real.log a := by
  rw [show (∫ u in a..b, 1/u) = ∫ u in a..b, u⁻¹ by simp only [one_div]]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.log) (f' := fun u : ℝ => u⁻¹)]
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le ha hx.1))
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)

theorem cbar_integral_le (β₀ : ℝ) (hβ₀ : (1:ℝ)/14 ≤ β₀) (hβ₁ : β₀ ≤ 1/3) :
    (∫ β in β₀..(1/3), Real.log (2 - 3 * β) / (β * (1 - β))) ≤ 0.75 := by
  have hU1 : (1:ℝ) ≤ 2 - 3*β₀ := by linarith
  have hU2 : 2 - 3*β₀ ≤ 25/14 := by linarith
  have hs1 : (3:ℝ)/14 ≤ 3*β₀ := by linarith
  have hs2 : 3*β₀ ≤ 1 := by linarith
  -- Step 1: change of variables β = (2 - u)/3
  have hmain : (∫ β in β₀..(1/3), Real.log (2 - 3 * β) / (β * (1 - β)))
      = ∫ u in 1..(2 - 3*β₀), (Real.log u / (2 - u) + Real.log u / (1 + u)) := by
    have hfun : Set.EqOn (fun β : ℝ => Real.log (2 - 3*β)/(β*(1-β)))
        (fun β => 3 * ((fun u : ℝ => Real.log u/(2-u) + Real.log u/(1+u)) (2 + (-3)*β)))
        (Set.uIcc β₀ (1/3)) := by
      intro β hβ
      rw [Set.uIcc_of_le hβ₁] at hβ
      have hβ0 : β ≠ 0 := by
        have : (0:ℝ) < β := by linarith [hβ.1, hβ₀]
        linarith
      have hβp : (1:ℝ) - β ≠ 0 := by
        have : β ≤ 1/3 := hβ.2
        linarith
      have h1 : (2:ℝ) + (-3)*β = 2 - 3*β := by ring
      beta_reduce
      rw [h1, show (2:ℝ) - (2 - 3*β) = 3*β by ring, show (1:ℝ) + (2 - 3*β) = 3*(1-β) by ring]
      field_simp
      ring
    rw [intervalIntegral.integral_congr hfun]
    rw [intervalIntegral.integral_comp_add_mul
      (f := fun u : ℝ => 3*(Real.log u/(2-u) + Real.log u/(1+u))) (show (-3:ℝ) ≠ 0 by norm_num) (2)]
    simp only [show (2:ℝ) + (-3) * (1/3) = 1 by norm_num,
      show (2:ℝ) + (-3) * β₀ = 2 - 3*β₀ by ring]
    rw [intervalIntegral.integral_symm, smul_eq_mul, intervalIntegral.integral_const_mul]
    ring
  rw [hmain]
  -- Step 2: split the integrand
  have hint_a : IntervalIntegrable (fun u : ℝ => Real.log u/(2-u)) volume 1 (2-3*β₀) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log continuousOn_id
      intro u hu
      rw [Set.uIcc_of_le hU1] at hu
      have huu : (0:ℝ) < u := by linarith [hu.1]
      exact ne_of_gt huu
    · fun_prop
    · intro u hu
      rw [Set.uIcc_of_le hU1] at hu
      have h1 : (1:ℝ) ≤ u := hu.1
      have h2 : u ≤ 2 - 3*β₀ := hu.2
      linarith
  have hint_b : IntervalIntegrable (fun u : ℝ => Real.log u/(1+u)) volume 1 (2-3*β₀) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log continuousOn_id
      intro u hu
      rw [Set.uIcc_of_le hU1] at hu
      have huu : (0:ℝ) < u := by linarith [hu.1]
      exact ne_of_gt huu
    · fun_prop
    · intro u hu
      rw [Set.uIcc_of_le hU1] at hu
      have : (1:ℝ) ≤ u := hu.1
      positivity
  have hsplit : (∫ u in 1..(2-3*β₀), (Real.log u/(2-u) + Real.log u/(1+u)))
      = (∫ u in 1..(2-3*β₀), Real.log u/(2-u)) + (∫ u in 1..(2-3*β₀), Real.log u/(1+u)) := by
    rw [intervalIntegral.integral_add hint_a hint_b]
  rw [hsplit]
  -- Step 3a: bound P1
  have hP1 : (∫ u in 1..(2-3*β₀), Real.log u/(1+u)) ≤ (25/39)*(2629/4116)^2/2 := by
    have hcd : ContinuousOn (fun u : ℝ => Real.log u / u) (Set.uIcc 1 (2-3*β₀)) := by
      apply ContinuousOn.div
      · apply ContinuousOn.log continuousOn_id
        intro u hu
        rw [Set.uIcc_of_le hU1] at hu
        have huu : (0:ℝ) < u := by linarith [hu.1]
        exact ne_of_gt huu
      · fun_prop
      · intro u hu
        rw [Set.uIcc_of_le hU1] at hu
        have huu : (0:ℝ) < u := by linarith [hu.1]
        exact ne_of_gt huu
    have hint_g : IntervalIntegrable (fun u : ℝ => (25/39)*(Real.log u/u)) volume 1 (2-3*β₀) :=
      (((continuousOn_const).mul hcd)).intervalIntegrable
    have hmono : (∫ u in 1..(2-3*β₀), Real.log u/(1+u))
        ≤ ∫ u in 1..(2-3*β₀), (25/39)*(Real.log u/u) := by
      apply intervalIntegral.integral_mono_on hU1 hint_b hint_g
      intro u hu
      have hu1 : (1:ℝ) ≤ u := hu.1
      have hu2 : u ≤ 2 - 3*β₀ := hu.2
      have hlu : 0 ≤ Real.log u := Real.log_nonneg hu1
      have hfrac : u/(1+u) ≤ 25/39 := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + u)]
        nlinarith [hu2]
      rw [show Real.log u/(1+u) = (u/(1+u))*(Real.log u/u) by field_simp; try ring]
      exact mul_le_mul_of_nonneg_right hfrac (div_nonneg hlu (by linarith))
    have hlogU_le : Real.log (2-3*β₀) ≤ 2629/4116 := by
      have h2 : Real.log (25/14) ≤ 2629/4116 := by
        have h := log_one_add_le_three (show (0:ℝ) ≤ 11/14 by norm_num)
        have heq : (1:ℝ) + 11/14 = 25/14 := by norm_num
        rw [heq] at h
        convert h using 1 <;> norm_num
      have hle := Real.log_le_log (by linarith : (0:ℝ) < 2 - 3*β₀) hU2
      linarith
    have hlogU_nn : 0 ≤ Real.log (2-3*β₀) := Real.log_nonneg hU1
    calc (∫ u in 1..(2-3*β₀), Real.log u/(1+u))
        ≤ ∫ u in 1..(2-3*β₀), (25/39)*(Real.log u/u) := hmono
      _ = (25/39) * (∫ u in 1..(2-3*β₀), Real.log u/u) := by
            rw [intervalIntegral.integral_const_mul]
      _ = (25/39) * ((Real.log (2-3*β₀))^2/2 - (Real.log 1)^2/2) := by
            rw [integral_log_div_self 1 (2-3*β₀) (by norm_num) hU1]
      _ = (25/39) * ((Real.log (2-3*β₀))^2/2) := by rw [Real.log_one]; ring
      _ ≤ (25/39) * ((2629/4116)^2/2) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact pow_le_pow_left₀ hlogU_nn hlogU_le 2
      _ = (25/39)*(2629/4116)^2/2 := by ring
  -- Step 3b: bound P2
  have hP2 : (∫ u in 1..(2-3*β₀), Real.log u/(2-u))
      ≤ (6931471808/10^10)*(2*(6931471808/10^10) + 1/6)
        - (11/28 + 187/3136 + 2717/197568 + 38335/9834496) := by
    -- change of variables u = 2 - y
    have hcv : (∫ u in 1..(2-3*β₀), Real.log u/(2-u)) = ∫ y in (3*β₀)..1, Real.log (2-y)/y := by
      rw [show (fun u : ℝ => Real.log u/(2-u)) = fun u => (fun x : ℝ => Real.log (2-x)/x) (2-u)
          from by funext u; simp only; rw [show (2:ℝ) - (2-u) = u by ring]]
      rw [intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => Real.log (2-x)/x) (2)]
      rw [show (2:ℝ) - (2 - 3*β₀) = 3*β₀ by ring]
      norm_num
    rw [hcv]
    -- integrand nonnegative, so bound by the integral over [3/14, 1]
    have hintf : IntervalIntegrable (fun y : ℝ => Real.log (2-y)/y) volume ((3:ℝ)/14) 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div
      · apply ContinuousOn.log (by fun_prop)
        intro y hy
        rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/14) ≤ 1)] at hy
        have : y ≤ 1 := hy.2
        linarith
      · fun_prop
      · intro y hy
        rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/14) ≤ 1)] at hy
        have : (3:ℝ)/14 ≤ y := hy.1
        linarith
    have hmono2 : (∫ y in (3*β₀)..1, Real.log (2-y)/y) ≤ ∫ y in ((3:ℝ)/14)..1, Real.log (2-y)/y := by
      apply intervalIntegral.integral_mono_interval hs1 hs2 le_rfl _ hintf
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      have hy0 : 0 < y := by linarith [hy.1]
      exact div_nonneg (Real.log_nonneg (by linarith [hy.2])) (le_of_lt hy0)
    have h143 : Real.log (14/3) ≤ 2*(6931471808/10^10) + 1/6 := by
      have h2 : Real.log 2 ≤ 6931471808/10^10 := log_two_lt_rat.le
      have hmul : Real.log (14/3) = Real.log 4 + Real.log (7/6) := by
        rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (7:ℝ)/6 ≠ 0)]
        norm_num
      rw [hmul, Real.log_four_eq]
      have h76 : Real.log (7/6) ≤ 1/6 := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 7/6 by norm_num)
        linarith
      linarith
    have hlog143_nn : 0 ≤ Real.log (14/3) := Real.log_nonneg (by norm_num)
    have hc_nn : (0:ℝ) ≤ 6931471808/10^10 := by norm_num
    -- decompose log(2-y) = log 2 + log(1-y/2)
    have hdecomp : (∫ y in ((3:ℝ)/14)..1, Real.log (2-y)/y)
        = Real.log 2 * (∫ y in ((3:ℝ)/14)..1, 1/y)
          + ∫ y in ((3:ℝ)/14)..1, Real.log (1-y/2)/y := by
      have hpt : Set.EqOn (fun y : ℝ => Real.log (2-y)/y)
          (fun y => Real.log 2 * (1/y) + Real.log (1-y/2)/y) (Set.uIcc ((3:ℝ)/14) 1) := by
        intro y hy
        beta_reduce
        rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/14) ≤ 1)] at hy
        have hy0 : 0 < y := by linarith [hy.1]
        have hy2 : y ≤ 1 := hy.2
        have h1y : (0:ℝ) < 1 - y/2 := by linarith
        have hmul : Real.log (2-y) = Real.log 2 + Real.log (1-y/2) := by
          have h := Real.log_mul (show (2:ℝ) ≠ 0 by norm_num) (show (1:ℝ) - y/2 ≠ 0 by linarith)
          have heq : (2:ℝ) * (1 - y/2) = 2 - y := by ring
          rwa [heq] at h
        rw [hmul]
        field_simp
        try ring
      rw [intervalIntegral.integral_congr hpt]
      rw [intervalIntegral.integral_add _ _]
      · rw [intervalIntegral.integral_const_mul]
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.const_mul
        apply ContinuousOn.div continuousOn_const continuousOn_id
        intro y hy
        rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/14) ≤ 1)] at hy
        show y ≠ 0
        linarith [hy.1]
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div
        · apply ContinuousOn.log (by fun_prop)
          intro y hy
          rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/14) ≤ 1)] at hy
          have : y ≤ 1 := hy.2
          linarith
        · fun_prop
        · intro y hy
          rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/14) ≤ 1)] at hy
          show y ≠ 0
          linarith [hy.1]
    have hinv : (∫ y in ((3:ℝ)/14)..1, 1/y) = Real.log (14/3) := by
      rw [integral_inv_eq ((3:ℝ)/14) 1 (by norm_num) (by norm_num),
        Real.log_one, zero_sub, ← Real.log_inv]
      congr 1
      norm_num
    have hpoly : (∫ y in ((3:ℝ)/14)..1, Real.log (1-y/2)/y)
        ≤ -(11/28 + 187/3136 + 2717/197568 + 38335/9834496) := by
      have hpolyint : (∫ y in ((3:ℝ)/14)..1, (-1/2 - y/8 - y^2/24 - y^3/64))
          = -(11/28 + 187/3136 + 2717/197568 + 38335/9834496) := by
        rw [show (fun y : ℝ => -1/2 - y/8 - y^2/24 - y^3/64)
            = (fun y : ℝ => (-1/2)*y^0 + (-1/8)*y^1 + (-1/24)*y^2 + (-1/64)*y^3)
            from by funext y; ring]
        rw [intervalIntegral.integral_add
              (Continuous.intervalIntegrable (by fun_prop) _ _)
              (Continuous.intervalIntegrable (by fun_prop) _ _)]
        rw [intervalIntegral.integral_add
              (Continuous.intervalIntegrable (by fun_prop) _ _)
              (Continuous.intervalIntegrable (by fun_prop) _ _)]
        rw [intervalIntegral.integral_add
              (Continuous.intervalIntegrable (by fun_prop) _ _)
              (Continuous.intervalIntegrable (by fun_prop) _ _)]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          integral_pow, integral_pow, integral_pow, integral_pow]
        norm_num
      rw [← hpolyint]
      refine intervalIntegral.integral_mono_on (by norm_num : ((3:ℝ)/14) ≤ 1) ?_ ?_ ?_
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div
        · apply ContinuousOn.log (by fun_prop)
          intro y hy
          rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/14) ≤ 1)] at hy
          have : y ≤ 1 := hy.2
          linarith
        · fun_prop
        · intro y hy
          rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/14) ≤ 1)] at hy
          show y ≠ 0
          linarith [hy.1]
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
      · intro y hy
        have hy0 : 0 < y := by linarith [hy.1]
        have hy2 : y ≤ 1 := hy.2
        have hx0 : 0 ≤ y/2 := by linarith
        have hx1 : y/2 < 1 := by linarith
        have h := log_one_sub_le_four hx0 hx1
        have h2 : -(y/2) - (y/2)^2/2 - (y/2)^3/3 - (y/2)^4/4
            = (-1/2 - y/8 - y^2/24 - y^3/64) * y := by ring
        rw [h2] at h
        rw [div_le_iff₀ hy0]
        exact h
    calc (∫ y in (3*β₀)..1, Real.log (2-y)/y)
        ≤ ∫ y in ((3:ℝ)/14)..1, Real.log (2-y)/y := hmono2
      _ = Real.log 2 * (∫ y in ((3:ℝ)/14)..1, 1/y)
            + ∫ y in ((3:ℝ)/14)..1, Real.log (1-y/2)/y := hdecomp
      _ = Real.log 2 * Real.log (14/3)
            + ∫ y in ((3:ℝ)/14)..1, Real.log (1-y/2)/y := by rw [hinv]
      _ ≤ Real.log 2 * Real.log (14/3)
            + (-(11/28 + 187/3136 + 2717/197568 + 38335/9834496)) := by linarith [hpoly]
      _ ≤ (6931471808/10^10)*(2*(6931471808/10^10) + 1/6)
            - (11/28 + 187/3136 + 2717/197568 + 38335/9834496) := by
            have hprod : Real.log 2 * Real.log (14/3)
                ≤ (6931471808/10^10)*(2*(6931471808/10^10) + 1/6) :=
              mul_le_mul (log_two_lt_rat.le) h143 hlog143_nn hc_nn
            linarith
  have hconst : (25/39)*(2629/4116)^2/2
      + ((6931471808/10^10)*(2*(6931471808/10^10) + 1/6)
        - (11/28 + 187/3136 + 2717/197568 + 38335/9834496)) ≤ (0.75:ℝ) := by norm_num
  linarith [hP1, hP2, hconst]
