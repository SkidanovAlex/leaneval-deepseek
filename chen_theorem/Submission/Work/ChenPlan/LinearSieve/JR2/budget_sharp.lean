import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.errH_sharp_bounds
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_le_decay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile

namespace Work.ChenPlan.LinearSieve.JR2

open MeasureTheory Set
open Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

/-! ## §0  Two elementary one-sided exponential bounds

`exp_le_two_add` is the only place where the region `[2,3]` of the transport budget and the
clamped budget `s ≤ 3` differ from the cruder transport inequalities: it says that on `[0,1]`
the exponential is dominated by the tangent-plus-`u²/2` chord `1 + u + u²/2 + (2/9)u³`, and in
particular by `2 + u` and by `s` (with `s = 2 + u`). -/

/-- `e^u ≤ 2 + u` for `u ∈ [0,1]` (Taylor with cubic remainder `Real.exp_bound'`). -/
lemma exp_le_two_add {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : Real.exp u ≤ 2 + u := by
  have hb := Real.exp_bound' (x := u) h0 h1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  nlinarith [hb, h0, h1, sq_nonneg u]

/-- `35/99 ≤ e^{-1}`, since `e < 2.7182818286 < 99/35`. -/
lemma exp_neg_one_ge : (35:ℝ)/99 ≤ Real.exp (-1) := by
  have he : Real.exp 1 < 99/35 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h := (inv_le_inv₀ (by norm_num : (0:ℝ) < 99/35) (Real.exp_pos 1)).mpr he.le
  rw [Real.exp_neg]
  have h35 : ((99:ℝ)/35)⁻¹ = 35/99 := by norm_num
  rwa [h35] at h

/-! ## §1  The three region cores of the transport budget

With the region-splitting bounds of `errH_sharp_bounds`, claim (1) of `budget_sharp` reduces to
three purely exponential inequalities, proved here by multiplying through by `100·s·e^{s-1}`
respectively `100·s·e^{s-2}` and using `e ≤ 3`. -/

/-- `[2,3]`-region core: `e^{-2}(3.94-s)` beats `ε e^{-2} + (1+ε)·e^{-2}(3.94-s)/s` at `ε = 1/100`.
The binding case is `s = 2` (ratio `0.9997`); the proof writes `s = 2+h`, `h ∈ [0,1]`, where the
inequality becomes `(9897/50 - 100h) e^h ≤ 198 + 99h`, i.e. (since `9897/50 = 198 - 3/50` and
`198 - 100h ≥ 0`) `(198-100h)e^h ≤ 198+99h`, which follows from the cubic upper bound
`e^h ≤ 1+h+h²/2+(2/9)h³` because that bound gives `(198-100h)e^h ≤ 198+98h-h²-6h³-(200/9)h⁴`. -/
lemma core_23 (s : ℝ) (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
    (1/100)*Real.exp (-2) + (101/100)*(Real.exp (-2)*(197/50 - s))/s
      ≤ (99/100)*Real.exp (-s) := by
  have h0 : (0:ℝ) ≤ s - 2 := by linarith
  have h1 : s - 2 ≤ 1 := by linarith
  have hs0 : (0:ℝ) < s := by linarith
  have he2 : (0:ℝ) < Real.exp (-2) := Real.exp_pos _
  have hU : Real.exp (s - 2) ≤ 1 + (s-2) + (s-2)^2/2 + (2/9)*(s-2)^3 := by
    have h := Real.exp_bound' (x := s-2) h0 h1 (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    linarith [h]
  have hA : (0:ℝ) ≤ 198 - 100*(s-2) := by linarith
  have hpoly : (198 - 100*(s-2)) * (1 + (s-2) + (s-2)^2/2 + (2/9)*(s-2)^3)
      ≤ 198 + 99*(s-2) := by
    nlinarith [h0, sq_nonneg (s-2), pow_nonneg h0 3, pow_nonneg h0 4]
  have hkey : (9897/50 - 100*(s-2)) * Real.exp (s-2) ≤ 198 + 99*(s-2) := by
    have hle : (9897/50 - 100*(s-2)) ≤ 198 - 100*(s-2) := by norm_num
    have h4 : (9897/50 - 100*(s-2)) * Real.exp (s-2) ≤ (198 - 100*(s-2)) * Real.exp (s-2) :=
      mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    have h5 : (198 - 100*(s-2)) * Real.exp (s-2)
        ≤ (198 - 100*(s-2)) * (1 + (s-2) + (s-2)^2/2 + (2/9)*(s-2)^3) :=
      mul_le_mul_of_nonneg_left hU hA
    linarith [h4, h5, hpoly]
  have hkey' : (19897/50 - 100*s) * Real.exp (s-2) ≤ 99*s := by
    have h := hkey
    rw [show (9897:ℝ)/50 - 100*(s-2) = 19897/50 - 100*s by ring,
        show (198:ℝ) + 99*(s-2) = 99*s by ring] at h
    exact h
  have heq1 : (1/100)*Real.exp (-2) + (101/100)*(Real.exp (-2)*(197/50 - s))/s
      = Real.exp (-2) * ((1/100) + (101/100)*(197/50-s)/s) := by
    field_simp
  have heq2 : (99/100)*Real.exp (-s) = Real.exp (-2) * ((99/100)*Real.exp (-(s-2))) := by
    rw [show Real.exp (-s) = Real.exp (-2) * Real.exp (-(s-2)) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  rw [heq1, heq2]
  refine mul_le_mul_of_nonneg_left ?_ he2.le
  have hA2 : (1/100) + (101/100)*(197/50-s)/s = (s + 101*(197/50-s))/(100*s) := by
    field_simp
  have hB2 : (99/100)*Real.exp (-(s-2)) = (99*s)/(100*s*Real.exp (s-2)) := by
    rw [Real.exp_neg]
    field_simp
  rw [hA2, hB2, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [show s + 101*(197/50 - s) = 19897/50 - 100*s by ring]
  have hmul := mul_le_mul_of_nonneg_right hkey' (by positivity : (0:ℝ) ≤ 100*s)
  nlinarith [hmul]

/-- `[3,4]`-region core: `e^{-(s-1)}` beats the transported budget at `ε = 1/100`, because
multiplying by `100 s e^{s-1}` turns it into `s + 101 ≤ 297 e^{-1}`, with `s ≤ 4`. -/
lemma core_34 (s : ℝ) (hs3 : 3 ≤ s) (hs4 : s ≤ 4) :
    (1/100)*Real.exp (-(s-1)) + (101/100)*Real.exp (-(s-1))/s
      ≤ (99/100)*(3*Real.exp (-s)/s) := by
  have hs0 : (0:ℝ) < s := by linarith
  have hE : (0:ℝ) < Real.exp (-(s-1)) := Real.exp_pos _
  have hkey : s + 101 ≤ 297 * Real.exp (-1) := by
    have h1 : s + 101 ≤ 105 := by linarith
    have h2 : (105:ℝ) ≤ 297 * Real.exp (-1) := by nlinarith [exp_neg_one_ge]
    linarith
  have hEexp : Real.exp (-s) = Real.exp (-(s-1)) * Real.exp (-1) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hEexp]
  have hfac : (1/100)*Real.exp (-(s-1)) + (101/100)*Real.exp (-(s-1))/s
      = Real.exp (-(s-1)) * ((1/100) + (101/100)/s) := by field_simp
  rw [hfac]
  have hfac2 : (99/100)*(3*(Real.exp (-(s-1))*Real.exp (-1))/s)
      = Real.exp (-(s-1)) * ((99/100)*(3*Real.exp (-1)/s)) := by ring
  rw [hfac2]
  refine mul_le_mul_of_nonneg_left ?_ hE.le
  have hA : (1/100) + (101/100)/s = (s+101)/(100*s) := by field_simp
  have hB : (99/100)*(3*Real.exp (-1)/s) = (297*Real.exp (-1))/(100*s) := by
    field_simp
    try norm_num
  rw [hA, hB, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right hkey (by positivity : (0:ℝ) ≤ 100*s)
  nlinarith [hmul]

/-- `[4,∞)`-region core: same reduction, now `s + 101 ≤ 99 e^{-1}(s-1)`, which holds at `s = 4`
and has positive slope in `s`. -/
lemma core_4inf (s : ℝ) (hs4 : 4 ≤ s) :
    (1/100)*(3*Real.exp (-(s-1))/(s-1)) + (101/100)*(3*Real.exp (-(s-1))/(s-1))/s
      ≤ (99/100)*(3*Real.exp (-s)/s) := by
  have hD : (0:ℝ) < s - 1 := by linarith
  have hs0 : (0:ℝ) < s := by linarith
  have hc : (0:ℝ) ≤ 99*Real.exp (-1) - 1 := by nlinarith [exp_neg_one_ge]
  have hbase : (0:ℝ) ≤ 297*Real.exp (-1) - 105 := by nlinarith [exp_neg_one_ge]
  have hkey : s + 101 ≤ 99*Real.exp (-1)*(s-1) := by
    have hmm : (0:ℝ) ≤ (99*Real.exp (-1) - 1) * (s - 4) := mul_nonneg hc (by linarith)
    nlinarith [hmm, hbase]
  have hE : (0:ℝ) < Real.exp (-(s-1)) := Real.exp_pos _
  have hEexp : Real.exp (-s) = Real.exp (-(s-1)) * Real.exp (-1) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hEexp]
  have hfac : (1/100)*(3*Real.exp (-(s-1))/(s-1)) + (101/100)*(3*Real.exp (-(s-1))/(s-1))/s
      = 3*Real.exp (-(s-1)) * ((1/100)/(s-1) + (101/100)/((s-1)*s)) := by
    field_simp
  rw [hfac]
  have hfac2 : (99/100)*(3*(Real.exp (-(s-1))*Real.exp (-1))/s)
      = 3*Real.exp (-(s-1)) * ((99/100)*Real.exp (-1)/s) := by ring
  rw [hfac2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hA : (1/100)/(s-1) + (101/100)/((s-1)*s) = (s+101)/(100*(s-1)*s) := by field_simp
  have hB : (99/100)*Real.exp (-1)/s = (99*Real.exp (-1)*(s-1))/(100*(s-1)*s) := by
    field_simp
    try ring
  rw [hA, hB, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right hkey (by positivity : (0:ℝ) ≤ 100*(s-1)*s)
  nlinarith [hmul]

/-! ## §2  The four parts of `budget_sharp` -/

/-- Part (1): the "budget_main" transport of the sharp layer induction. -/
theorem budget_sharp_1 :
    ∀ s ε : ℝ, 2 ≤ s → 0 ≤ ε → ε ≤ 1/100 →
       ε * errH (s-1) + (1 + ε) * (∫ t in Set.Ioi s, errH (t-1)) / s
         ≤ (99/100) * errH s := by
  intro s ε hs2 hε0 hε1
  have hs0 : (0:ℝ) < s := by linarith
  have hnn : (0:ℝ) ≤ ∫ u in Set.Ioi (s-1), errH u :=
    setIntegral_nonneg_of_ae (Filter.Eventually.of_forall errH_nonneg)
  rw [setIntegral_Ioi_comp_sub errH s 1]
  rcases le_or_gt s 3 with hs3 | hs3
  · -- `2 ≤ s ≤ 3`
    have e1 : errH (s-1) = Real.exp (-2) := errH_of_le_two (by linarith)
    have e2 : errH s = Real.exp (-s) := errH_eq_exp_neg hs2 hs3
    have hI : (∫ u in Set.Ioi (s-1), errH u) ≤ Real.exp (-2)*(197/50 - s) := by
      have h := errH_sharp_bounds.2.1 s hs2 hs3
      rwa [show (3.94:ℝ) = 197/50 by norm_num] at h
    rw [e1, e2]
    have hY : (0:ℝ) ≤ Real.exp (-2)*(197/50 - s)/s :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith)) hs0.le
    have hXY : (∫ u in Set.Ioi (s-1), errH u)/s ≤ Real.exp (-2)*(197/50 - s)/s :=
      div_le_div_of_nonneg_right hI hs0.le
    have h2 : (1+ε) * (∫ u in Set.Ioi (s-1), errH u)/s
        ≤ (101/100)*(Real.exp (-2)*(197/50 - s))/s := by
      calc (1+ε) * (∫ u in Set.Ioi (s-1), errH u)/s
          = (1+ε) * ((∫ u in Set.Ioi (s-1), errH u)/s) := mul_div_assoc _ _ _
        _ ≤ (101/100) * ((∫ u in Set.Ioi (s-1), errH u)/s) :=
            mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hnn hs0.le)
        _ ≤ (101/100) * (Real.exp (-2)*(197/50 - s)/s) :=
            mul_le_mul_of_nonneg_left hXY (by norm_num)
        _ = (101/100)*(Real.exp (-2)*(197/50 - s))/s := (mul_div_assoc _ _ _).symm
    have h1 : ε * Real.exp (-2) ≤ (1/100)*Real.exp (-2) :=
      mul_le_mul_of_nonneg_right hε1 (Real.exp_pos _).le
    exact le_trans (add_le_add h1 h2) (core_23 s hs2 hs3)
  · by_cases hs4 : s ≤ 4
    · -- `3 < s ≤ 4`
      have e1 : errH (s-1) = Real.exp (-(s-1)) := errH_eq_exp_neg (by linarith) (by linarith)
      have e2 : errH s = 3*Real.exp (-s)/s := errH_of_ge_three (le_of_lt hs3)
      have hI : (∫ u in Set.Ioi (s-1), errH u) ≤ Real.exp (-(s-1)) :=
        errH_sharp_bounds.2.2.1 s (le_of_lt hs3) hs4
      rw [e1, e2]
      have hXY : (∫ u in Set.Ioi (s-1), errH u)/s ≤ Real.exp (-(s-1))/s :=
        div_le_div_of_nonneg_right hI hs0.le
      have h2 : (1+ε) * (∫ u in Set.Ioi (s-1), errH u)/s
          ≤ (101/100)*Real.exp (-(s-1))/s := by
        calc (1+ε) * (∫ u in Set.Ioi (s-1), errH u)/s
            = (1+ε) * ((∫ u in Set.Ioi (s-1), errH u)/s) := mul_div_assoc _ _ _
          _ ≤ (101/100) * ((∫ u in Set.Ioi (s-1), errH u)/s) :=
              mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hnn hs0.le)
          _ ≤ (101/100) * (Real.exp (-(s-1))/s) := mul_le_mul_of_nonneg_left hXY (by norm_num)
          _ = (101/100)*Real.exp (-(s-1))/s := (mul_div_assoc _ _ _).symm
      have h1 : ε * Real.exp (-(s-1)) ≤ (1/100)*Real.exp (-(s-1)) :=
        mul_le_mul_of_nonneg_right hε1 (Real.exp_pos _).le
      exact le_trans (add_le_add h1 h2) (core_34 s (le_of_lt hs3) hs4)
    · -- `s > 4`
      have hs4' : 4 < s := not_le.mp hs4
      have e1 : errH (s-1) = 3*Real.exp (-(s-1))/(s-1) := errH_of_ge_three (by linarith)
      have e2 : errH s = 3*Real.exp (-s)/s := errH_of_ge_three (by linarith)
      have hI : (∫ u in Set.Ioi (s-1), errH u) ≤ 3*Real.exp (-(s-1))/(s-1) :=
        errH_sharp_bounds.2.2.2.1 s (le_of_lt hs4')
      rw [e1, e2]
      have hZ : (0:ℝ) ≤ 3*Real.exp (-(s-1))/(s-1) :=
        div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (by linarith)
      have hXY : (∫ u in Set.Ioi (s-1), errH u)/s ≤ (3*Real.exp (-(s-1))/(s-1))/s :=
        div_le_div_of_nonneg_right hI hs0.le
      have h2 : (1+ε) * (∫ u in Set.Ioi (s-1), errH u)/s
          ≤ (101/100)*(3*Real.exp (-(s-1))/(s-1))/s := by
        calc (1+ε) * (∫ u in Set.Ioi (s-1), errH u)/s
            = (1+ε) * ((∫ u in Set.Ioi (s-1), errH u)/s) := mul_div_assoc _ _ _
          _ ≤ (101/100) * ((∫ u in Set.Ioi (s-1), errH u)/s) :=
              mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hnn hs0.le)
          _ ≤ (101/100) * ((3*Real.exp (-(s-1))/(s-1))/s) :=
              mul_le_mul_of_nonneg_left hXY (by norm_num)
          _ = (101/100)*(3*Real.exp (-(s-1))/(s-1))/s := (mul_div_assoc _ _ _).symm
      have h1 : ε * (3*Real.exp (-(s-1))/(s-1)) ≤ (1/100)*(3*Real.exp (-(s-1))/(s-1)) :=
        mul_le_mul_of_nonneg_right hε1 hZ
      exact le_trans (add_le_add h1 h2) (core_4inf s (le_of_lt hs4'))

/-- Part (2): the clamped budget for `s ≤ 3`. -/
theorem budget_sharp_2 :
    ∀ s ε : ℝ, 1 ≤ s → s ≤ 3 → 0 ≤ ε → ε ≤ 1/100 →
       (1+ε)^2 * ((47/50) * Real.exp (-2)) / s
         + (1+ε) * (3/s) * ε * errH 2
         ≤ (99/100) * errH s := by
  intro s ε hs1 hs3 hε0 hε1
  have hs0 : (0:ℝ) < s := by linarith
  have he2 : errH 2 = Real.exp (-2) := errH_of_le_two le_rfl
  have hsq : (1+ε)^2 ≤ (101/100)^2 := by nlinarith [hε0, hε1]
  have hT1 : (1+ε)^2 * ((47/50) * Real.exp (-2)) / s
      ≤ ((101/100)^2 * ((47/50) * Real.exp (-2)))/s :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (by positivity)) hs0.le
  have hT2 : (1+ε) * (3/s) * ε * errH 2 ≤ 3*(101/100)*(1/100)*Real.exp (-2)/s := by
    rw [he2]
    rw [show (1+ε) * (3/s) * ε * Real.exp (-2) = ((1+ε)*3*ε*Real.exp (-2))/s by ring]
    refine div_le_div_of_nonneg_right ?_ hs0.le
    have h3 : (1+ε)*3*ε ≤ 3*(101/100)*(1/100) := by nlinarith [hε0, hε1]
    exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  have htotal : (1+ε)^2 * ((47/50) * Real.exp (-2)) / s + (1+ε) * (3/s) * ε * errH 2
      ≤ ((101/100)^2 * ((47/50) * Real.exp (-2))
          + 3*(101/100)*(1/100)*Real.exp (-2))/s := by
    rw [add_div]
    exact add_le_add hT1 hT2
  have hKle : (101/100)^2 * ((47/50) * Real.exp (-2)) + 3*(101/100)*(1/100)*Real.exp (-2)
      ≤ (99/100) * Real.exp (-2) := by nlinarith [Real.exp_pos (-2)]
  rcases le_or_gt s 2 with hs2 | hs2
  · rw [errH_of_le_two hs2]
    calc (1+ε)^2 * ((47/50) * Real.exp (-2)) / s + (1+ε) * (3/s) * ε * errH 2
        ≤ ((101/100)^2 * ((47/50) * Real.exp (-2))
            + 3*(101/100)*(1/100)*Real.exp (-2))/s := htotal
      _ ≤ (101/100)^2 * ((47/50) * Real.exp (-2)) + 3*(101/100)*(1/100)*Real.exp (-2) :=
          div_le_self (by positivity) hs1
      _ ≤ (99/100) * Real.exp (-2) := hKle
  · have hs2' : 2 ≤ s := le_of_lt hs2
    rw [errH_eq_exp_neg hs2' hs3]
    have hexp : Real.exp (s-2) ≤ s := by
      have h := exp_le_two_add (show (0:ℝ) ≤ s-2 by linarith) (show s-2 ≤ 1 by linarith)
      linarith
    have hinv : s⁻¹ ≤ Real.exp (-(s-2)) := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ hs0 (Real.exp_pos _)).mpr hexp
    have hmain : Real.exp (-2)/s ≤ Real.exp (-2)*Real.exp (-(s-2)) := by
      rw [div_le_iff₀ hs0]
      have h2 : (1:ℝ) ≤ s * Real.exp (-(s-2)) := by
        have h3 := mul_le_mul_of_nonneg_left hinv hs0.le
        rw [mul_inv_cancel₀ (ne_of_gt hs0)] at h3
        exact h3
      nlinarith [h2, Real.exp_pos (-2)]
    calc (1+ε)^2 * ((47/50) * Real.exp (-2)) / s + (1+ε) * (3/s) * ε * errH 2
        ≤ ((101/100)^2 * ((47/50) * Real.exp (-2))
            + 3*(101/100)*(1/100)*Real.exp (-2))/s := htotal
      _ ≤ ((99/100)*Real.exp (-2))/s := div_le_div_of_nonneg_right hKle hs0.le
      _ ≤ (99/100)*(Real.exp (-2)*Real.exp (-(s-2))) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hmain (by norm_num)
      _ = (99/100)*Real.exp (-s) := by
          rw [show Real.exp (-s) = Real.exp (-2)*Real.exp (-(s-2)) by
            rw [← Real.exp_add]; congr 1; ring]

/-- Part (3): the profile budget for the even/odd-parent cases. -/
theorem budget_sharp_3 :
    ∀ (m : ℕ) (s : ℝ), 2 ≤ m → 2 ≤ s →
       profC (m-1) s + profC (m-2) (s-1)
         ≤ 990 * (99/100:ℝ)^(m-2) * errH s := by
  intro m s hm hs
  have hs1 : (1:ℝ) ≤ s := by linarith
  have hs'1 : (1:ℝ) ≤ s - 1 := by linarith
  have h1 := profC_le_decay (m-1) s hs1
  have h2 := profC_le_decay (m-2) (s-1) hs'1
  have htr := errH_sharp_bounds.2.2.2.2.2 s hs
  have hpow : (97/100:ℝ)^(m-1) = (97/100)^(m-2) * (97/100) := by
    have : m - 1 = (m - 2) + 1 := by omega
    rw [this, pow_succ]
  have he := errH_nonneg s
  have hD : (0:ℝ) ≤ (97/100:ℝ)^(m-2) := by positivity
  have hE : (0:ℝ) ≤ (99/100:ℝ)^(m-2) := by positivity
  have hDE : (97/100:ℝ)^(m-2) ≤ (99/100:ℝ)^(m-2) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hcoef : 20 * ((97/100:ℝ) + 4*Real.exp 1/3) ≤ 100 := by
    have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    nlinarith [he3]
  calc profC (m-1) s + profC (m-2) (s-1)
      ≤ 20*(97/100)^(m-1)*errH s + 20*(97/100)^(m-2)*((4*Real.exp 1/3)*errH s) := by
        refine add_le_add h1 ?_
        exact le_trans h2 (mul_le_mul_of_nonneg_left htr (by positivity))
    _ = (97/100:ℝ)^(m-2) * (20*((97/100) + 4*Real.exp 1/3)) * errH s := by
        rw [hpow]; ring
    _ ≤ (99/100:ℝ)^(m-2) * 100 * errH s := by
        have h20 : (0:ℝ) ≤ 20*((97/100:ℝ) + 4*Real.exp 1/3) := by positivity
        have hstep1 : (97/100:ℝ)^(m-2) * (20*((97/100) + 4*Real.exp 1/3)) * errH s
            ≤ (99/100:ℝ)^(m-2) * (20*((97/100) + 4*Real.exp 1/3)) * errH s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDE h20) he
        have hstep2 : (99/100:ℝ)^(m-2) * (20*((97/100) + 4*Real.exp 1/3)) * errH s
            ≤ (99/100:ℝ)^(m-2) * 100 * errH s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hE) he
        linarith [hstep1, hstep2]
    _ ≤ 990 * (99/100:ℝ)^(m-2) * errH s := by
        have hnn : (0:ℝ) ≤ (99/100:ℝ)^(m-2) * errH s := mul_nonneg hE he
        nlinarith [hnn]

/-- Part (4): the profile budget for the clamped case. -/
theorem budget_sharp_4 :
    ∀ (m : ℕ) (ε s : ℝ), 3 ≤ m → Odd m → 1 ≤ s → s ≤ 3 → 0 ≤ ε → ε ≤ 1/100 →
       (2+ε) * profC (m-1) s
         + (1+ε) * (3/s) * profC (m-2) 2
         ≤ 990 * (99/100:ℝ)^(m-2) * errH s := by
  intro m ε s hm hmodd hs1 hs3 hε0 hε1
  have hs0 : (0:ℝ) < s := by linarith
  have h1 := profC_le_decay (m-1) s hs1
  have h2 := profC_le_decay (m-2) 2 (by norm_num)
  have hpow : (97/100:ℝ)^(m-1) = (97/100)^(m-2) * (97/100) := by
    have : m - 1 = (m - 2) + 1 := by omega
    rw [this, pow_succ]
  have herr2 : errH 2 = Real.exp (-2) := errH_of_le_two le_rfl
  have herr3 : errH 3 = Real.exp (-3) := errH_eq_exp_neg (by norm_num) le_rfl
  have hmono := errH_sharp_bounds.1 s 3 hs3
  have hlow : Real.exp (-3) ≤ errH s := by rw [← herr3]; exact hmono
  have hshift : errH 2 ≤ Real.exp 1 * errH s := by
    rw [herr2, show Real.exp (-2) = Real.exp 1 * Real.exp (-3) by
      rw [← Real.exp_add]; congr 1; norm_num]
    exact mul_le_mul_of_nonneg_left hlow (Real.exp_pos 1).le
  have hc1 : 2 + ε ≤ 201/100 := by linarith
  have hc2 : (1+ε)*(3/s) ≤ 303/100 := by
    have h3s : 3/s ≤ 3 := by rw [div_le_iff₀ hs0]; linarith
    calc (1+ε)*(3/s) ≤ (101/100)*3 :=
          mul_le_mul (by linarith) h3s (by positivity) (by norm_num)
      _ = 303/100 := by norm_num
  have hE : (0:ℝ) ≤ (99/100:ℝ)^(m-2) := by positivity
  have hD : (0:ℝ) ≤ (97/100:ℝ)^(m-2) := by positivity
  have he := errH_nonneg s
  have hpn1 : (0:ℝ) ≤ profC (m-1) s := profC_nonneg _ _
  have hDE : (97/100:ℝ)^(m-2) ≤ (99/100:ℝ)^(m-2) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hcoef : 20 * ((201/100:ℝ)*(97/100) + (303/100)*Real.exp 1) ≤ 240 := by
    have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    nlinarith [he3]
  -- term-by-term bounds
  have hA : (2+ε) * profC (m-1) s ≤ (201/100) * (20*(97/100)^(m-1)*errH s) :=
    mul_le_mul hc1 h1 hpn1 (by positivity : (0:ℝ) ≤ 201/100)
  have hB : (1+ε) * (3/s) * profC (m-2) 2
      ≤ (303/100) * (20*(97/100)^(m-2)*(Real.exp 1 * errH s)) := by
    have h20 : (0:ℝ) ≤ 20*(97/100:ℝ)^(m-2) := by positivity
    have hstep : (1+ε) * (3/s) * profC (m-2) 2
        ≤ (303/100) * (20*(97/100:ℝ)^(m-2)*errH 2) :=
      mul_le_mul hc2 h2 (profC_nonneg _ _) (by positivity)
    have hstep2 : (303/100) * (20*(97/100:ℝ)^(m-2)*errH 2)
        ≤ (303/100) * (20*(97/100:ℝ)^(m-2)*(Real.exp 1 * errH s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hshift h20) (by norm_num)
    linarith [hstep, hstep2]
  have hsum : (2+ε) * profC (m-1) s + (1+ε) * (3/s) * profC (m-2) 2
      ≤ (97/100:ℝ)^(m-2) * (20*((201/100)*(97/100) + (303/100)*Real.exp 1)) * errH s := by
    have hA' : (201/100) * (20*(97/100)^(m-1)*errH s)
        = 20*(201/100)*(97/100)^(m-2)*(97/100)*errH s := by rw [hpow]; ring
    have hB' : (303/100) * (20*(97/100)^(m-2)*(Real.exp 1 * errH s))
        = 20*(303/100)*(97/100)^(m-2)*Real.exp 1*errH s := by ring
    rw [hA'] at hA
    rw [hB'] at hB
    linarith [hA, hB]
  calc (2+ε) * profC (m-1) s + (1+ε) * (3/s) * profC (m-2) 2
      ≤ (97/100:ℝ)^(m-2) * (20*((201/100)*(97/100) + (303/100)*Real.exp 1)) * errH s := hsum
    _ ≤ (99/100:ℝ)^(m-2) * 240 * errH s := by
        have h20 : (0:ℝ) ≤ 20*((201/100:ℝ)*(97/100) + (303/100)*Real.exp 1) := by positivity
        have hstep1 : (97/100:ℝ)^(m-2) * (20*((201/100)*(97/100) + (303/100)*Real.exp 1)) * errH s
            ≤ (99/100:ℝ)^(m-2) * (20*((201/100)*(97/100) + (303/100)*Real.exp 1)) * errH s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDE h20) he
        have hstep2 : (99/100:ℝ)^(m-2) * (20*((201/100)*(97/100) + (303/100)*Real.exp 1)) * errH s
            ≤ (99/100:ℝ)^(m-2) * 240 * errH s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hE) he
        linarith [hstep1, hstep2]
    _ ≤ 990 * (99/100:ℝ)^(m-2) * errH s := by
        have hnn : (0:ℝ) ≤ (99/100:ℝ)^(m-2) * errH s := mul_nonneg hE he
        nlinarith [hnn]

/-- **The four arithmetic budgets of the sharp layer induction** (C = 1000, ρ = 99/100).

* (1) the "budget_main" transport: at a state with parameter `s ≥ 2`, the excess
  `ε·errH (s-1)` of the top of the Abel staircase plus the transported error
  `(1+ε)·(1/s)·∫_{Ioi s} errH (t-1) dt` is at most `(99/100)·errH s`
  (region splitting `[2,3]`, `[3,4]`, `[4,∞)` with `errH_sharp_bounds`, i.e. the bounds
  `e^{-2}(3.94-s)`, `e^{-(s-1)}`, `3e^{-(s-1)}/(s-1)` and `errH (s-1) ≤ (4e/3) errH s`);
* (2) the clamped budget `s ≤ 3`: `(1+ε)^2·(47/50)e^{-2}/s + (1+ε)(3/s)·ε·errH 2 ≤ (99/100) errH s`
  (uses `∫_{Ioi 2} errH ≤ (47/50)e^{-2}` and `errH s ≥ e^{-s}` there; note both terms carry the
  `1/s`);
* (3) the profile budget for the even/odd-parent cases: `profC (m-1) s + profC (m-2) (s-1)`
  is at most `990·(99/100)^{m-2}·errH s` for `m ≥ 2`, `s ≥ 2` (from `profC_le_decay`,
  `profC j σ ≤ 20·(97/100)^j errH σ`, and `errH (s-1) ≤ (4e/3) errH s`; note `990 = 1000·99/100`,
  which is exactly the slack the induction leaves in that slot);
* (4) the profile budget for the clamped case: `(2+ε) profC (m-1) s + (1+ε)(3/s) profC (m-2) 2`
  is at most `990·(99/100)^{m-2}·errH s` for odd `m ≥ 3`, `1 ≤ s ≤ 3` (same inputs, plus
  `errH 2 ≤ e·errH s` for `s ≤ 3`).

All four are elementary real-analysis/numerics statements (region splitting + Taylor/exponential
bounds); the binding cases are `s = 2` in (1) (ratio `0.9997` against the provable bound
`e^{-2}(3.94-s)`, `0.9902` against the exact integral) and `s = 1` in (2) (ratio `0.9992`), while
(3),(4) hold with a factor-5 margin from `profC_le_decay` alone. -/
theorem budget_sharp :
    (∀ s ε : ℝ, 2 ≤ s → 0 ≤ ε → ε ≤ 1/100 →
       ε * Work.NumberTheory.Chen.APSwitchUpper.errH (s-1)
         + (1 + ε) * (∫ t in Set.Ioi s, Work.NumberTheory.Chen.APSwitchUpper.errH (t-1)) / s
         ≤ (99/100) * Work.NumberTheory.Chen.APSwitchUpper.errH s)
  ∧ (∀ s ε : ℝ, 1 ≤ s → s ≤ 3 → 0 ≤ ε → ε ≤ 1/100 →
       (1+ε)^2 * ((47/50) * Real.exp (-2)) / s
         + (1+ε) * (3/s) * ε * Work.NumberTheory.Chen.APSwitchUpper.errH 2
         ≤ (99/100) * Work.NumberTheory.Chen.APSwitchUpper.errH s)
  ∧ (∀ (m : ℕ) (s : ℝ), 2 ≤ m → 2 ≤ s →
       Work.NumberTheory.Chen.APSwitchUpper.profC (m-1) s
         + Work.NumberTheory.Chen.APSwitchUpper.profC (m-2) (s-1)
         ≤ 990 * (99/100:ℝ)^(m-2) * Work.NumberTheory.Chen.APSwitchUpper.errH s)
  ∧ (∀ (m : ℕ) (ε s : ℝ), 3 ≤ m → Odd m → 1 ≤ s → s ≤ 3 → 0 ≤ ε → ε ≤ 1/100 →
       (2+ε) * Work.NumberTheory.Chen.APSwitchUpper.profC (m-1) s
         + (1+ε) * (3/s) * Work.NumberTheory.Chen.APSwitchUpper.profC (m-2) 2
         ≤ 990 * (99/100:ℝ)^(m-2) * Work.NumberTheory.Chen.APSwitchUpper.errH s) :=
  ⟨budget_sharp_1, budget_sharp_2, budget_sharp_3, budget_sharp_4⟩

end

end Work.ChenPlan.LinearSieve.JR2
