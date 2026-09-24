import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.cbar_integral_le
import Submission.Work.NumberTheory.Chen.BTermCount.cbar_integral_le_relaxed
import Submission.Work.NumberTheory.Chen.BTermCount.cbarSharpDefs

set_option linter.unusedVariables false

namespace Work.NumberTheory.Chen.BTermCount

open MeasureTheory intervalIntegral

/-- The BJS integrand `β ↦ log (2 - 3β)/(β (1 - β))`, packaged so that it can be passed around
as a whole. -/
private noncomputable def cbarI (β : ℝ) : ℝ := Real.log (2 - 3*β)/(β*(1-β))

/-- On `[7/100, 1/10]` the BJS integrand is at most `10`: there `2 - 3β ≤ 179/100` so that
`log (2 - 3β) ≤ 13/20`, while `10 β (1 - β) ≥ 13/20`. -/
private lemma cbarI_le_ten {β : ℝ} (hβ7 : (7:ℝ)/100 ≤ β) (hβ10 : β ≤ 1/10) :
    cbarI β ≤ 10 := by
  have hlog179 : Real.log (179/100) ≤ 13/20 := by
    have hmul : Real.log (179/100) = Real.log 2 + Real.log (1 - 21/200) := by
      have h := Real.log_mul (show (2:ℝ) ≠ 0 by norm_num) (show (1:ℝ) - 21/200 ≠ 0 by norm_num)
      have heq : (2:ℝ) * (1 - 21/200) = 179/100 := by norm_num
      rw [heq] at h; exact h
    have hsub : Real.log (1 - 21/200) ≤ -(21/200) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 - 21/200 by norm_num)
      linarith
    have h3 : Real.log 2 < 6931471808/10^10 := log_two_lt_rat
    have h4 : (6931471808:ℝ)/10^10 + -(21/200) ≤ 13/20 := by norm_num
    linarith
  have hden : (0:ℝ) < β*(1-β) := by nlinarith
  have hnum : Real.log (2 - 3*β) ≤ 13/20 := by
    have h1 : (2:ℝ) - 3*β ≤ 179/100 := by linarith
    have h2 : (0:ℝ) < 2 - 3*β := by linarith
    exact le_trans (Real.log_le_log h2 h1) hlog179
  have hbig : (13:ℝ)/20 ≤ 10*(β*(1-β)) := by nlinarith
  show Real.log (2 - 3*β)/(β*(1-β)) ≤ 10
  rw [div_le_iff₀ hden]
  linarith

/-- Change of variables `β = (2 - u)/3` in the BJS integral: for `1/14 ≤ β₀ ≤ 1/3`,
`∫_{β₀}^{1/3} log (2 - 3β)/(β(1-β)) dβ = ∫_1^{2 - 3β₀} (log u/(2-u) + log u/(1+u)) du`. -/
private lemma cbarI_change (β₀ : ℝ) (hβ₀ : (1:ℝ)/14 ≤ β₀) (hβ₁ : β₀ ≤ 1/3) :
    (∫ β in β₀..(1/3), cbarI β)
      = ∫ u in (1:ℝ)..(2 - 3*β₀), (Real.log u/(2-u) + Real.log u/(1+u)) := by
  show (∫ β in β₀..(1/3), Real.log (2 - 3*β)/(β*(1-β)))
      = ∫ u in (1:ℝ)..(2 - 3*β₀), (Real.log u/(2-u) + Real.log u/(1+u))
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

/-- The `P1` piece: `∫_1^{17/10} log u/(1+u) du ≤ (17/54) cbarHalfC3^2 - (25/594) cbarHalfLb1^2`. -/
private lemma cbarP1_le_aux :
    (∫ u in (1:ℝ)..(17/10), Real.log u/(1+u))
      ≤ (17/54)*cbarHalfC3^2 - (25/594)*cbarHalfLb1^2 := by
  have hII1 : IntervalIntegrable (fun u : ℝ => Real.log u/(1+u)) volume 1 (6/5) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 6/5)]
    apply ContinuousOn.div
    · apply ContinuousOn.log continuousOn_id
      intro u hu
      exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u)
    · fun_prop
    · intro u hu; exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < 1 + u)
  have hII2 : IntervalIntegrable (fun u : ℝ => Real.log u/(1+u)) volume (6/5) (17/10) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : ((6:ℝ)/5) ≤ 17/10)]
    apply ContinuousOn.div
    · apply ContinuousOn.log continuousOn_id
      intro u hu
      exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u)
    · fun_prop
    · intro u hu; exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < 1 + u)
  have hIIg1 : IntervalIntegrable (fun u : ℝ => (6/11)*(Real.log u/u)) volume 1 (6/5) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 6/5)]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div
    · apply ContinuousOn.log continuousOn_id
      intro u hu
      exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u)
    · fun_prop
    · intro u hu; exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u)
  have hIIg2 : IntervalIntegrable (fun u : ℝ => (17/27)*(Real.log u/u)) volume (6/5) (17/10) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : ((6:ℝ)/5) ≤ 17/10)]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div
    · apply ContinuousOn.log continuousOn_id
      intro u hu
      exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u)
    · fun_prop
    · intro u hu; exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u)
  have hsplit : (∫ u in (1:ℝ)..(17/10), Real.log u/(1+u))
      = (∫ u in (1:ℝ)..(6/5), Real.log u/(1+u)) + (∫ u in (6/5)..(17/10), Real.log u/(1+u)) :=
    (intervalIntegral.integral_add_adjacent_intervals hII1 hII2).symm
  have hb1 : (∫ u in (1:ℝ)..(6/5), Real.log u/(1+u)) ≤ (3/11)*(Real.log (6/5))^2 := by
    have hm : (∫ u in (1:ℝ)..(6/5), Real.log u/(1+u))
        ≤ ∫ u in (1:ℝ)..(6/5), (6/11)*(Real.log u/u) := by
      apply intervalIntegral.integral_mono_on (by norm_num : (1:ℝ) ≤ 6/5) hII1 hIIg1
      intro u hu
      have hu1 : (1:ℝ) ≤ u := hu.1
      have hu2 : u ≤ 6/5 := hu.2
      have hfrac : u/(1+u) ≤ 6/11 := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + u)]
        nlinarith
      have hlu : 0 ≤ Real.log u := Real.log_nonneg hu1
      rw [show Real.log u/(1+u) = (u/(1+u))*(Real.log u/u) by field_simp; try ring]
      exact mul_le_mul_of_nonneg_right hfrac (div_nonneg hlu (by linarith))
    have hcalc : (∫ u in (1:ℝ)..(6/5), (6/11)*(Real.log u/u)) = (3/11)*(Real.log (6/5))^2 := by
      rw [intervalIntegral.integral_const_mul,
        integral_log_div_self 1 (6/5) (by norm_num) (by norm_num), Real.log_one]
      ring
    linarith [hm, hcalc.le]
  have hb2 : (∫ u in (6/5)..(17/10), Real.log u/(1+u))
      ≤ (17/54)*((Real.log (17/10))^2 - (Real.log (6/5))^2) := by
    have hm : (∫ u in (6/5)..(17/10), Real.log u/(1+u))
        ≤ ∫ u in (6/5)..(17/10), (17/27)*(Real.log u/u) := by
      apply intervalIntegral.integral_mono_on (by norm_num : ((6:ℝ)/5) ≤ 17/10) hII2 hIIg2
      intro u hu
      have hu1 : ((6:ℝ)/5) ≤ u := hu.1
      have hu2 : u ≤ 17/10 := hu.2
      have hfrac : u/(1+u) ≤ 17/27 := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + u)]
        nlinarith
      have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
      rw [show Real.log u/(1+u) = (u/(1+u))*(Real.log u/u) by field_simp; try ring]
      exact mul_le_mul_of_nonneg_right hfrac (div_nonneg hlu (by linarith))
    have hcalc : (∫ u in (6/5)..(17/10), (17/27)*(Real.log u/u))
        = (17/54)*((Real.log (17/10))^2 - (Real.log (6/5))^2) := by
      rw [intervalIntegral.integral_const_mul,
        integral_log_div_self (6/5) (17/10) (by norm_num) (by norm_num)]
      ring
    linarith [hm, hcalc.le]
  have hB2 : (Real.log (17/10))^2 ≤ cbarHalfC3^2 :=
    pow_le_pow_left₀ cbarHalf_log_seventeen_tenths_nonneg cbarHalf_log_seventeen_tenths_le 2
  have hA2 : cbarHalfLb1^2 ≤ (Real.log (6/5))^2 :=
    pow_le_pow_left₀ cbarHalfLb1_nonneg cbarHalfLb1_le_log 2
  linarith [hsplit, hb1, hb2, hB2, hA2]

/-- The `P2` piece: `∫_1^{17/10} log u/(2-u) du ≤ cbarHalfC1*cbarHalfC2 - cbarS`. -/
private lemma cbarP2_le_aux :
    (∫ u in (1:ℝ)..(17/10), Real.log u/(2-u)) ≤ cbarHalfC1*cbarHalfC2 - cbarS := by
  have hcv : (∫ u in (1:ℝ)..(17/10), Real.log u/(2-u))
      = ∫ y in ((3:ℝ)/10)..1, Real.log (2-y)/y := by
    rw [show (fun u : ℝ => Real.log u/(2-u))
        = fun u => (fun x : ℝ => Real.log (2-x)/x) (2-u) from by
      funext u; simp only; rw [show (2:ℝ) - (2-u) = u by ring]]
    rw [intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => Real.log (2-x)/x) (2)]
    norm_num
  rw [hcv]
  have hii1 : IntervalIntegrable (fun y : ℝ => Real.log 2 * (1/y)) volume ((3:ℝ)/10) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.const_mul
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro y hy
    rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/10) ≤ 1)] at hy
    exact ne_of_gt (by linarith [hy.1] : (0:ℝ) < y)
  have hii2 : IntervalIntegrable (fun y : ℝ => Real.log (1-y/2)/y) volume ((3:ℝ)/10) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro y hy
      rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/10) ≤ 1)] at hy
      linarith [hy.2]
    · fun_prop
    · intro y hy
      rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/10) ≤ 1)] at hy
      exact ne_of_gt (by linarith [hy.1] : (0:ℝ) < y)
  have hdecomp : (∫ y in ((3:ℝ)/10)..1, Real.log (2-y)/y)
      = Real.log 2 * (∫ y in ((3:ℝ)/10)..1, 1/y)
        + ∫ y in ((3:ℝ)/10)..1, Real.log (1-y/2)/y := by
    have hpt : Set.EqOn (fun y : ℝ => Real.log (2-y)/y)
        (fun y => Real.log 2 * (1/y) + Real.log (1-y/2)/y) (Set.uIcc ((3:ℝ)/10) 1) := by
      intro y hy
      beta_reduce
      rw [Set.uIcc_of_le (by norm_num : ((3:ℝ)/10) ≤ 1)] at hy
      have hy0 : 0 < y := by linarith [hy.1]
      have hy2 : y ≤ 1 := hy.2
      have h1y : (0:ℝ) < 1 - y/2 := by linarith
      have hmul : Real.log (2-y) = Real.log 2 + Real.log (1-y/2) := by
        have h := Real.log_mul (show (2:ℝ) ≠ 0 by norm_num) (show (1:ℝ) - y/2 ≠ 0 by linarith)
        have heq : (2:ℝ) * (1 - y/2) = 2 - y := by ring
        rwa [heq] at h
      rw [hmul]
      field_simp; try ring
    rw [intervalIntegral.integral_congr hpt]
    rw [intervalIntegral.integral_add hii1 hii2]
    rw [intervalIntegral.integral_const_mul]
  have hinv : (∫ y in ((3:ℝ)/10)..1, 1/y) = Real.log (10/3) := by
    rw [integral_inv_eq ((3:ℝ)/10) 1 (by norm_num) (by norm_num), Real.log_one, zero_sub,
      ← Real.log_inv]
    congr 1
    norm_num
  have hseries : (∫ y in ((3:ℝ)/10)..1, Real.log (1-y/2)/y) ≤ -cbarS := by
    have hpt : ∀ y ∈ Set.Icc ((3:ℝ)/10) 1,
        Real.log (1-y/2)/y
          ≤ ∑ m ∈ Finset.range 10, -(y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1))) := by
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      have hy1 : y ≤ 1 := hy.2
      have hz0 : 0 ≤ y/2 := by linarith
      have hz1 : y/2 < 1 := by linarith
      have htr := cbarHalf_log_trunc (y/2) hz0 hz1 10
      have hsplit : (∑ m ∈ Finset.range 10, (y/2)^(m+1)/((m:ℝ)+1))
          = y * (∑ m ∈ Finset.range 10, (y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1)))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [div_pow, div_div, show y^(m+1) = y^m * y by rw [pow_succ], mul_div_assoc,
          mul_comm ((2:ℝ)^(m+1)) ((m:ℝ)+1)]
        ring
      rw [hsplit] at htr
      have hgoal : Real.log (1-y/2)/y
          ≤ -(∑ m ∈ Finset.range 10, (y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1)))) := by
        have h := div_le_div_of_nonneg_right htr (le_of_lt hy0)
        rwa [show (-(y * (∑ m ∈ Finset.range 10, (y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1))))))/y
              = -(∑ m ∈ Finset.range 10, (y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1)))) by
            have hyne : y ≠ 0 := ne_of_gt hy0
            field_simp; try ring] at h
      simpa only [Finset.sum_neg_distrib] using hgoal
    have hII : ∀ m ∈ Finset.range 10,
        IntervalIntegrable (fun y : ℝ => -(y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1)))) volume ((3:ℝ)/10) 1 := by
      intro m hm
      apply ContinuousOn.intervalIntegrable
      fun_prop
    have hIIlog : IntervalIntegrable (fun y : ℝ => Real.log (1-y/2)/y) volume ((3:ℝ)/10) 1 := hii2
    have hIIsum : IntervalIntegrable
        (fun y : ℝ => ∑ m ∈ Finset.range 10, -(y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1))))
        volume ((3:ℝ)/10) 1 := by
      apply ContinuousOn.intervalIntegrable
      fun_prop
    have hterm : ∀ m ∈ Finset.range 10,
        (∫ y in ((3:ℝ)/10)..1, -(y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1))))
          = -((1 - (3/10:ℝ)^(m+1))/((2:ℝ)^(m+1) * ((m:ℝ)+1)^2)) := by
      intro m hm
      rw [show (fun y : ℝ => -(y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1))))
            = fun y => (-(1/(((m:ℝ)+1)*(2:ℝ)^(m+1)))) * y^m from by
        funext y; field_simp; try ring]
      rw [intervalIntegral.integral_const_mul, integral_pow, one_pow]
      field_simp; try ring
    calc (∫ y in ((3:ℝ)/10)..1, Real.log (1-y/2)/y)
        ≤ (∫ y in ((3:ℝ)/10)..1,
            ∑ m ∈ Finset.range 10, -(y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1)))) :=
          intervalIntegral.integral_mono_on (by norm_num) hIIlog hIIsum hpt
      _ = ∑ m ∈ Finset.range 10,
            (∫ y in ((3:ℝ)/10)..1, -(y^m/(((m:ℝ)+1)*(2:ℝ)^(m+1)))) :=
          intervalIntegral.integral_finset_sum hII
      _ = ∑ m ∈ Finset.range 10,
            -((1 - (3/10:ℝ)^(m+1))/((2:ℝ)^(m+1) * ((m:ℝ)+1)^2)) :=
          Finset.sum_congr rfl hterm
      _ = -cbarS := by
          rw [cbarS, Finset.sum_neg_distrib]
  rw [hdecomp, hinv]
  have hprod : Real.log 2 * Real.log (10/3) ≤ cbarHalfC1 * cbarHalfC2 :=
    mul_le_mul cbarHalf_log_two_lt.le cbarHalf_log_ten_thirds_le
      cbarHalf_log_ten_thirds_nonneg cbarHalfC1_nonneg
  linarith [hprod, hseries]

/-- The sharp bound for the full BJS integral over the sift range `[1/10, 1/3]`. -/
private lemma cbarI_ten_le : (∫ β in ((1:ℝ)/10)..(1/3), cbarI β) ≤ (0.496 : ℝ) := by
  rw [cbarI_change (1/10) (by norm_num) (by norm_num)]
  have h17 : (2:ℝ) - 3*(1/10) = 17/10 := by norm_num
  rw [h17]
  have hint_a : IntervalIntegrable (fun u : ℝ => Real.log u/(2-u)) volume 1 (17/10) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 17/10)]
    apply ContinuousOn.div
    · apply ContinuousOn.log continuousOn_id
      intro u hu
      exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u)
    · fun_prop
    · intro u hu
      exact ne_of_gt (by linarith [hu.2] : (0:ℝ) < 2 - u)
  have hint_b : IntervalIntegrable (fun u : ℝ => Real.log u/(1+u)) volume 1 (17/10) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 17/10)]
    apply ContinuousOn.div
    · apply ContinuousOn.log continuousOn_id
      intro u hu
      exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < u)
    · fun_prop
    · intro u hu
      exact ne_of_gt (by linarith [hu.1] : (0:ℝ) < 1 + u)
  rw [intervalIntegral.integral_add hint_a hint_b]
  linarith [cbarP2_le_aux, cbarP1_le_aux, cbarSharp_cert]

/-- **Sharp BJS integral bound at the sift limit `1/10`, quantitative version.** For `0 ≤ δ ≤ 1/700`,
`0 < β₀` with `1/10 − δ ≤ β₀` and `β₀ ≤ b ≤ 1/3`,
`∫_{β₀}^{b} log(2−3β)/(β(1−β)) dβ ≤ 0.496 + 10δ`.

The sharp value is `∫_{1/10}^{1/3} log(2−3β)/(β(1−β)) dβ = 0.490995…`, so `0.496` has 1 % of slack; the
`10δ` pays for the extra piece `[1/10−δ, 1/10]`.

PROOF SKETCH. Let `I = ∫_{1/10}^{1/3} log(2−3β)/(β(1−β)) dβ`. By monotonicity in the endpoints and
`∫_{1/10−δ}^{1/10} ≤ 10δ`, it suffices to prove `I ≤ 0.496`. For the tail: on `[1/10−δ, 1/10]` one has
`2−3β ≤ 179/100` (as `β ≥ 1/10 − 1/700 > 7/100`) and `10·β(1−β) ≥ 13/20` (as `β(1−β) ≥ 0.0888 > 0.065`),
whence `Real.log (2−3β) ≤ 13/20` and the integrand is `≤ 10`; NOTE the existing private
`cbarIntegrand_le_ten` is stated only on `[7/100, 1/14]` and does not literally cover `[1/10−δ,1/10]`,
so re-derive the same bound on the correct range (max of the integrand there is `≈ 6.0`).
Substituting `β = (2−u)/3` exactly as the `hmain` block of `cbar_integral_le` does gives
`I = ∫_1^{17/10} (log u/(2−u) + log u/(1+u)) du = P2 + P1`.
* `P2`: substitute `u = 2−y` (the `hcv` block of `cbar_integral_le`), giving
  `P2 = ∫_{3/10}^1 log(2−y)/y dy = log 2 · log(10/3) + ∫_{3/10}^1 log(1−y/2)/y dy` (its `hdecomp`),
  and then, using `log(1−z) ≤ -∑_{n=1}^{10} z^n/n` (truncation of `-log(1−z) = ∑_{n≥1} z^n/n`, applied
  with `z = y/2 ∈ [0,1/2]`; a short auxiliary fact, which may be proved inline in this file) and
  `∫_{3/10}^1 y^{n-1} dy = (1−(3/10)^n)/n`, get `P2 ≤ log 2 · log(10/3) − S`,
  where `S := ∑_{n=1}^{10} (1−(3/10)^n)/(2^n n²)`.
* `P1`: split `[1,17/10] = [1,6/5] ∪ [6/5,17/10]`. On the first piece `1/(1+u) ≤ (6/11)/u` (since
  `u ≤ 6/5`) and on the second `1/(1+u) ≤ (17/27)/u` (since `u ≤ 17/10`); with
  `∫_a^c log u/u du = ((log c)² − (log a)²)/2` (existing `integral_log_div_self`) this gives
  `P1 ≤ (17/54)·(log(17/10))² − (25/594)·(log(6/5))²`.
* Logarithm bounds: `log 2 < c1 := 6931471808/10^10` (Mathlib `Real.log_two_lt_d9`);
  `log(6/5) = -log(1−1/6) ≥ lb1 := ∑_{m=1}^{10} (1/6)^m/m` and
  `log(20/17) = -log(1−3/20) ≥ lb2 := ∑_{m=1}^{10} (3/20)^m/m` (both by the same truncation fact);
  hence `log(17/10) = log 2 − log(20/17) ≤ c1 − lb2 =: c3` and
  `log(10/3) = 2 log 2 − log(6/5) ≤ 2c1 − lb1 =: c2`.
* Final certificate (rational, `norm_num`): `c1·c2 − S + (17/54)c3² − (25/594)lb1² = 0.49557408… ≤ 0.496`. -/
theorem cbar_integral_le_half_sharp {β₀ b δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/700)
    (hβ₀ : (1:ℝ)/10 - δ ≤ β₀) (hβ₀0 : 0 < β₀) (hb : b ≤ 1/3) (hb0 : β₀ ≤ b) :
    (∫ β in β₀..b, Real.log (2 - 3 * β) / (β * (1 - β))) ≤ 0.496 + 10 * δ := by
  change (∫ β in β₀..b, cbarI β) ≤ 0.496 + 10 * δ
  have hβ₀7 : (7:ℝ)/100 ≤ β₀ := by linarith
  have hβ₀3 : β₀ ≤ 1/3 := le_trans hb0 hb
  have hnn : ∀ β ∈ Set.Icc ((7:ℝ)/100) (1/3), 0 ≤ cbarI β := by
    intro β hβ
    have hβ7 : (7:ℝ)/100 ≤ β := hβ.1
    have hβ3 : β ≤ 1/3 := hβ.2
    have hden : (0:ℝ) < β*(1-β) := by nlinarith
    show 0 ≤ Real.log (2 - 3*β)/(β*(1-β))
    exact div_nonneg (Real.log_nonneg (by linarith)) (le_of_lt hden)
  have hII : ∀ a c : ℝ, (7:ℝ)/100 ≤ a → a ≤ c → c ≤ 1/3 →
      IntervalIntegrable cbarI volume a c := by
    intro a c ha hac hc
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hac]
    show ContinuousOn (fun β : ℝ => Real.log (2 - 3*β)/(β*(1-β))) (Set.Icc a c)
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro β hβ
      have : β ≤ 1/3 := le_trans hβ.2 hc
      linarith
    · fun_prop
    · intro β hβ
      have h1 : (7:ℝ)/100 ≤ β := le_trans ha hβ.1
      have h2 : β ≤ 1/3 := le_trans hβ.2 hc
      exact ne_of_gt (by nlinarith)
  have hmonoR : ∀ a c : ℝ, (7:ℝ)/100 ≤ a → a ≤ b → b ≤ c → c ≤ 1/3 →
      (∫ β in a..b, cbarI β) ≤ ∫ β in a..c, cbarI β := by
    intro a c ha hab hbc hc
    have h1 : (∫ β in a..b, cbarI β) + (∫ β in b..c, cbarI β) = ∫ β in a..c, cbarI β :=
      intervalIntegral.integral_add_adjacent_intervals (hII a b ha hab (le_trans hbc hc))
        (hII b c (le_trans ha hab) hbc hc)
    have h2 : 0 ≤ ∫ β in b..c, cbarI β :=
      intervalIntegral.integral_nonneg hbc
        (fun u hu => hnn u ⟨le_trans (le_trans ha hab) hu.1, le_trans hu.2 hc⟩)
    linarith
  have hmonoL : ∀ a c : ℝ, (7:ℝ)/100 ≤ a → a ≤ c → c ≤ b → b ≤ 1/3 →
      (∫ β in c..b, cbarI β) ≤ ∫ β in a..b, cbarI β := by
    intro a c ha hac hcb hb3
    have h1 : (∫ β in a..c, cbarI β) + (∫ β in c..b, cbarI β) = ∫ β in a..b, cbarI β :=
      intervalIntegral.integral_add_adjacent_intervals (hII a c ha hac (le_trans hcb hb3))
        (hII c b (le_trans ha hac) hcb hb3)
    have h2 : 0 ≤ ∫ β in a..c, cbarI β :=
      intervalIntegral.integral_nonneg hac
        (fun u hu => hnn u ⟨le_trans ha hu.1, le_trans (le_trans hu.2 hcb) hb3⟩)
    linarith
  rcases lt_or_ge β₀ ((1:ℝ)/10) with hβ₀lt | hβ₀ge
  · have htail : (∫ β in β₀..((1:ℝ)/10), cbarI β) ≤ 10*δ := by
      have hta : (∫ β in β₀..((1:ℝ)/10), cbarI β) ≤ ∫ β in β₀..((1:ℝ)/10), (10:ℝ) := by
        apply intervalIntegral.integral_mono_on (le_of_lt hβ₀lt)
          (hII β₀ (1/10) hβ₀7 (le_of_lt hβ₀lt) (by norm_num)) intervalIntegrable_const
        intro x hx
        exact cbarI_le_ten (le_trans hβ₀7 hx.1) hx.2
      rw [intervalIntegral.integral_const] at hta
      simp only [smul_eq_mul] at hta
      have h10δ : ((1:ℝ)/10 - β₀) ≤ δ := by linarith
      linarith
    rcases lt_or_ge b ((1:ℝ)/10) with hblt | hbge
    · have h1 := hmonoR β₀ (1/10) hβ₀7 hb0 (le_of_lt hblt) (by norm_num)
      linarith
    · have hadj : (∫ β in β₀..((1:ℝ)/10), cbarI β) + (∫ β in ((1:ℝ)/10)..b, cbarI β)
            = ∫ β in β₀..b, cbarI β :=
        intervalIntegral.integral_add_adjacent_intervals
          (hII β₀ (1/10) hβ₀7 (le_of_lt hβ₀lt) (by norm_num))
          (hII (1/10) b (by norm_num) hbge hb)
      have h2 : (∫ β in ((1:ℝ)/10)..b, cbarI β) ≤ (0.496 : ℝ) := by
        have h3 := hmonoR ((1:ℝ)/10) (1/3) (by norm_num) hbge hb le_rfl
        linarith [h3, cbarI_ten_le]
      linarith
  · have h1 : (∫ β in β₀..b, cbarI β) ≤ ∫ β in ((1:ℝ)/10)..b, cbarI β :=
      hmonoL ((1:ℝ)/10) β₀ (by norm_num) hβ₀ge hb0 hb
    have h2 : (∫ β in ((1:ℝ)/10)..b, cbarI β) ≤ (0.496 : ℝ) := by
      have h3 := hmonoR ((1:ℝ)/10) (1/3) (by norm_num) (le_trans hβ₀ge hb0) hb le_rfl
      linarith [h3, cbarI_ten_le]
    linarith

end Work.NumberTheory.Chen.BTermCount
