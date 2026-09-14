import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators

namespace Commons.Analysis.LogClaim

/-- Lower bound on `exp x` from truncating the Taylor series at order 10 (for `|x| ≤ 1`). -/
private lemma exp_ge_sum_sub_rem (x : ℝ) (hx : |x| ≤ 1) :
    (∑ m ∈ Finset.range 10, x ^ m / (m.factorial : ℝ)) -
      |x| ^ 10 * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * (10 : ℝ))) ≤ Real.exp x := by
  have h := Real.exp_bound (x := x) hx (by norm_num : 0 < (10 : ℕ))
  have hlow := (abs_sub_le_iff.mp h).2
  nlinarith

private lemma exp_ge_low (x : ℝ) (hx : |x| ≤ 1) {M : ℝ}
    (hM : M ≤ (∑ m ∈ Finset.range 10, x ^ m / (m.factorial : ℝ)) -
      |x| ^ 10 * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * (10 : ℝ)))) : M ≤ Real.exp x := by
  have h := exp_ge_sum_sub_rem x hx
  linarith

private lemma sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  exact pow_le_pow_left₀ ha hab 2

/-- `exp (-2y) ≤ 1 - y` for `0 ≤ y ≤ 1/2`. -/
private lemma exp_neg_two_mul_le_sub_one {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    Real.exp (-2 * y) ≤ 1 - y := by
  have h1my : 0 < 1 - y := by linarith
  have h1py : 0 ≤ 1 + y := by linarith
  have h1 : 1 + y ≤ Real.exp y := by simpa [add_comm] using Real.add_one_le_exp y
  have h2 : (1 + y) ^ 2 ≤ (Real.exp y) ^ 2 := pow_le_pow_left₀ h1py h1 2
  have h2' : (1 + y) ^ 2 ≤ Real.exp (2 * y) := by
    calc
      (1 + y) ^ 2 ≤ (Real.exp y) ^ 2 := h2
      _ = Real.exp (2 * y) := (Real.exp_nat_mul y 2).symm
  have hy2 : y ^ 2 ≤ y / 2 := by
    have hprod : y * (y - 1 / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy0 (sub_nonpos.mpr hy1)
    nlinarith
  have hgood : 0 ≤ 1 - y - y ^ 2 := by nlinarith
  have hprod2 : 0 ≤ y * (1 - y - y ^ 2) := mul_nonneg hy0 hgood
  have hbig : 1 ≤ (1 - y) * (1 + y) ^ 2 := by
    nlinarith [hprod2]
  have hdiv : (1 - y)⁻¹ ≤ (1 + y) ^ 2 := by
    -- equivalently 1 ≤ (1 - y) * (1 + y)^2
    have hb : 1 ≤ (1 + y) ^ 2 * (1 - y) := by nlinarith [hbig]
    have : 1 / (1 - y) ≤ (1 + y) ^ 2 := (div_le_iff₀ h1my).2 hb
    simpa using this
  have hle3 : (1 - y)⁻¹ ≤ Real.exp (2 * y) := le_trans hdiv h2'
  have hanti : (Real.exp (2 * y))⁻¹ ≤ ((1 - y)⁻¹)⁻¹ :=
    inv_anti₀ (inv_pos.mpr h1my) hle3
  have hfin : (Real.exp (2 * y))⁻¹ ≤ 1 - y := by simpa using hanti
  simpa [show -2 * y = -(2 * y) by ring, Real.exp_neg] using hfin

-- numeric lemmas
private lemma exp_two_log2_z0 : (100/39 : ℝ) ≤ Real.exp (2 * (0.6931471803 : ℝ)^2) := by
  apply exp_ge_low (x := 2 * (0.6931471803 : ℝ)^2) (by norm_num)
  norm_num [Finset.sum_range_succ]

private lemma exp_two_log53_z0 : (5/3 : ℝ) ≤ Real.exp (2 * (0.5108256235 : ℝ)^2) := by
  apply exp_ge_low (x := 2 * (0.5108256235 : ℝ)^2) (by norm_num)
  norm_num [Finset.sum_range_succ]

private lemma exp_two_log32_z0 : (4/3 : ℝ) ≤ Real.exp (2 * (0.4054651077 : ℝ)^2) := by
  apply exp_ge_low (x := 2 * (0.4054651077 : ℝ)^2) (by norm_num)
  norm_num [Finset.sum_range_succ]

private lemma exp_two_log52_z0 : (5 : ℝ) ≤ Real.exp (2 * (0.9162907315 : ℝ)^2) := by
  have hy0 : (19/10 : ℝ) ≤ Real.exp (2 * (0.9162907315 : ℝ)^2 - 1) := by
    apply exp_ge_low (x := 2 * (0.9162907315 : ℝ)^2 - 1) (by norm_num)
    norm_num [Finset.sum_range_succ]
  have hprod : (5 : ℝ) ≤ (2.7182818283 : ℝ) * (19/10 : ℝ) := by norm_num
  have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have hmul : (2.7182818283 : ℝ) * (19/10 : ℝ) ≤ Real.exp 1 * Real.exp (2 * (0.9162907315 : ℝ)^2 - 1) := by
    exact mul_le_mul h1 hy0 (by norm_num) (Real.exp_pos 1).le
  have h5 : (5 : ℝ) ≤ Real.exp 1 * Real.exp (2 * (0.9162907315 : ℝ)^2 - 1) := by linarith
  rw [← Real.exp_add] at h5
  rw [show (1 + (2 * (0.9162907315 : ℝ)^2 - 1) : ℝ) = 2 * (0.9162907315 : ℝ)^2 by ring] at h5
  exact h5

private lemma exp_two_mul_log_ge_of_ge {c : ℝ} {a : ℝ} (ha : 0 ≤ a) (h : a ≤ Real.log c) :
    Real.exp (2 * a ^ 2) ≤ Real.exp (2 * (Real.log c) ^ 2) := by
  have hs : a ^ 2 ≤ (Real.log c) ^ 2 := sq_le_sq_of_nonneg ha h
  have hz : 2 * a ^ 2 ≤ 2 * (Real.log c) ^ 2 := by nlinarith
  exact Real.exp_le_exp.mpr hz

-- final numeric log lemmas
private lemma exp_two_log_two_ge : (100/39 : ℝ) ≤ Real.exp (2 * (Real.log 2)^2) := by
  exact exp_two_log2_z0.trans (exp_two_mul_log_ge_of_ge (c := (2:ℝ)) (a := (0.6931471803:ℝ)) (by norm_num) Real.log_two_gt_d9.le)

private lemma exp_two_log_five_thirds_ge : (5/3 : ℝ) ≤ Real.exp (2 * (Real.log (5/3))^2) := by
  have h : (0.5108256235 : ℝ) ≤ Real.log (5 / 3) := by
    have h1 : (1.6094379123 : ℝ) ≤ Real.log 5 := Real.log_five_gt_d9.le
    have h2 : Real.log 3 ≤ (1.0986122888 : ℝ) := Real.log_three_lt_d9.le
    have h' : (1.6094379123 - 1.0986122888 : ℝ) ≤ Real.log 5 - Real.log 3 := by linarith
    have hld : Real.log (5 / 3) = Real.log 5 - Real.log 3 := Real.log_div (by norm_num : (5:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)
    rw [hld]
    norm_num at h' ⊢
    exact h'
  exact exp_two_log53_z0.trans (exp_two_mul_log_ge_of_ge (c := (5/3:ℝ)) (a := (0.5108256235:ℝ)) (by norm_num) h)

private lemma exp_two_log_three_halves_ge : (4/3 : ℝ) ≤ Real.exp (2 * (Real.log (3/2))^2) := by
  have h : (0.4054651077 : ℝ) ≤ Real.log (3 / 2) := by
    have h1 : (1.0986122885 : ℝ) ≤ Real.log 3 := Real.log_three_gt_d9.le
    have h2 : Real.log 2 ≤ (0.6931471808 : ℝ) := Real.log_two_lt_d9.le
    have h' : (1.0986122885 - 0.6931471808 : ℝ) ≤ Real.log 3 - Real.log 2 := by linarith
    have hld : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)
    rw [hld]
    norm_num at h' ⊢
    exact h'
  exact exp_two_log32_z0.trans (exp_two_mul_log_ge_of_ge (c := (3/2:ℝ)) (a := (0.4054651077:ℝ)) (by norm_num) h)

private lemma exp_two_log_five_halves_ge : (5 : ℝ) ≤ Real.exp (2 * (Real.log (5/2))^2) := by
  have h : (0.9162907315 : ℝ) ≤ Real.log (5 / 2) := by
    have h1 : (1.6094379123 : ℝ) ≤ Real.log 5 := Real.log_five_gt_d9.le
    have h2 : Real.log 2 ≤ (0.6931471808 : ℝ) := Real.log_two_lt_d9.le
    have h' : (1.6094379123 - 0.6931471808 : ℝ) ≤ Real.log 5 - Real.log 2 := by linarith
    have hld : Real.log (5 / 2) = Real.log 5 - Real.log 2 := Real.log_div (by norm_num : (5:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)
    rw [hld]
    norm_num at h' ⊢
    exact h'
  exact exp_two_log52_z0.trans (exp_two_mul_log_ge_of_ge (c := (5/2:ℝ)) (a := (0.9162907315:ℝ)) (by norm_num) h)

private lemma exp_neg_two_log_two_le : Real.exp (-2 * (Real.log 2)^2) ≤ (39/100 : ℝ) := by
  have hge := exp_two_log_two_ge
  have hanti := inv_anti₀ (by norm_num : 0 < (100/39 : ℝ)) hge
  calc
    Real.exp (-2 * (Real.log 2)^2) = (Real.exp (2 * (Real.log 2)^2))⁻¹ := by
      rw [show -2 * (Real.log 2)^2 = -(2 * (Real.log 2)^2) by ring, Real.exp_neg]
    _ ≤ (100/39 : ℝ)⁻¹ := hanti
    _ = 39/100 := by norm_num

private lemma exp_neg_two_log_five_thirds_le : Real.exp (-2 * (Real.log (5/3))^2) ≤ (3/5 : ℝ) := by
  have hge := exp_two_log_five_thirds_ge
  have hanti := inv_anti₀ (by norm_num : 0 < (5/3 : ℝ)) hge
  calc
    Real.exp (-2 * (Real.log (5/3))^2) = (Real.exp (2 * (Real.log (5/3))^2))⁻¹ := by
      rw [show -2 * (Real.log (5/3))^2 = -(2 * (Real.log (5/3))^2) by ring, Real.exp_neg]
    _ ≤ (5/3 : ℝ)⁻¹ := hanti
    _ = 3/5 := by norm_num

private lemma exp_neg_two_log_three_halves_le : Real.exp (-2 * (Real.log (3/2))^2) ≤ (3/4 : ℝ) := by
  have hge := exp_two_log_three_halves_ge
  have hanti := inv_anti₀ (by norm_num : 0 < (4/3 : ℝ)) hge
  calc
    Real.exp (-2 * (Real.log (3/2))^2) = (Real.exp (2 * (Real.log (3/2))^2))⁻¹ := by
      rw [show -2 * (Real.log (3/2))^2 = -(2 * (Real.log (3/2))^2) by ring, Real.exp_neg]
    _ ≤ (4/3 : ℝ)⁻¹ := hanti
    _ = 3/4 := by norm_num

private lemma exp_neg_two_log_five_halves_le : Real.exp (-2 * (Real.log (5/2))^2) ≤ (1/5 : ℝ) := by
  have hge := exp_two_log_five_halves_ge
  have hanti := inv_anti₀ (by norm_num : 0 < (5 : ℝ)) hge
  calc
    Real.exp (-2 * (Real.log (5/2))^2) = (Real.exp (2 * (Real.log (5/2))^2))⁻¹ := by
      rw [show -2 * (Real.log (5/2))^2 = -(2 * (Real.log (5/2))^2) by ring, Real.exp_neg]
    _ ≤ (5 : ℝ)⁻¹ := hanti
    _ = 1/5 := by norm_num


/-- For `2 ≤ x`, the sum of the two Gaussian-type terms is < 1. -/
private lemma lt_one_of_two_le (x : ℝ) (hx : 2 ≤ x) :
    Real.exp (-2 * (Real.log x) ^ 2) + Real.exp (-2 * (Real.log (x / (x - 1))) ^ 2) < 1 := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : 0 < x := by linarith
  have hxsub : 0 < x - 1 := by linarith
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hxsubne : x - 1 ≠ 0 := ne_of_gt hxsub
  by_cases h25 : x ≤ 5 / 2
  · -- case 2 ≤ x ≤ 5/2
    have hlog2le : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (x := (2 : ℝ)) (y := x) (by norm_num : (0 : ℝ) < 2) hx
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hsqA : (Real.log 2) ^ 2 ≤ (Real.log x) ^ 2 := sq_le_sq_of_nonneg hlog2pos.le hlog2le
    have hmulA : 2 * (Real.log 2) ^ 2 ≤ 2 * (Real.log x) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsqA (by norm_num)
    have hAneg : -2 * (Real.log x) ^ 2 ≤ -2 * (Real.log 2) ^ 2 := by linarith
    have hA : Real.exp (-2 * (Real.log x) ^ 2) ≤ Real.exp (-2 * (Real.log 2) ^ 2) :=
      Real.exp_le_exp.mpr hAneg
    have hA' : Real.exp (-2 * (Real.log x) ^ 2) ≤ 39 / 100 := le_trans hA exp_neg_two_log_two_le
    -- B side: x/(x-1) ≥ 5/3
    have hratio : (5 / 3 : ℝ) ≤ x / (x - 1) := (le_div_iff₀ hxsub).2 (by nlinarith)
    have hpos53 : 0 < (5 / 3 : ℝ) := by norm_num
    have hlog53le : Real.log (5 / 3) ≤ Real.log (x / (x - 1)) :=
      Real.log_le_log (x := (5 / 3 : ℝ)) (y := x / (x - 1)) hpos53 hratio
    have hlog53pos : 0 < Real.log (5 / 3) := Real.log_pos (by norm_num : (1 : ℝ) < 5 / 3)
    have hsqB : (Real.log (5 / 3)) ^ 2 ≤ (Real.log (x / (x - 1))) ^ 2 :=
      sq_le_sq_of_nonneg hlog53pos.le hlog53le
    have hmulB : 2 * (Real.log (5 / 3)) ^ 2 ≤ 2 * (Real.log (x / (x - 1))) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsqB (by norm_num)
    have hBneg : -2 * (Real.log (x / (x - 1))) ^ 2 ≤ -2 * (Real.log (5 / 3)) ^ 2 := by linarith
    have hB : Real.exp (-2 * (Real.log (x / (x - 1))) ^ 2) ≤
        Real.exp (-2 * (Real.log (5 / 3)) ^ 2) := Real.exp_le_exp.mpr hBneg
    have hB' : Real.exp (-2 * (Real.log (x / (x - 1))) ^ 2) ≤ 3 / 5 :=
      le_trans hB exp_neg_two_log_five_thirds_le
    nlinarith
  · have h25le : (5 / 2 : ℝ) ≤ x := (lt_of_not_ge h25).le
    by_cases h3 : x ≤ 3
    · -- case 5/2 ≤ x ≤ 3
      have hlog52le : Real.log (5 / 2) ≤ Real.log x :=
        Real.log_le_log (x := (5 / 2 : ℝ)) (y := x) (by norm_num : (0 : ℝ) < 5 / 2) h25le
      have hlog52pos : 0 < Real.log (5 / 2) := Real.log_pos (by norm_num : (1 : ℝ) < 5 / 2)
      have hsqA : (Real.log (5 / 2)) ^ 2 ≤ (Real.log x) ^ 2 :=
        sq_le_sq_of_nonneg hlog52pos.le hlog52le
      have hmulA : 2 * (Real.log (5 / 2)) ^ 2 ≤ 2 * (Real.log x) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsqA (by norm_num)
      have hAneg : -2 * (Real.log x) ^ 2 ≤ -2 * (Real.log (5 / 2)) ^ 2 := by linarith
      have hA : Real.exp (-2 * (Real.log x) ^ 2) ≤ Real.exp (-2 * (Real.log (5 / 2)) ^ 2) :=
        Real.exp_le_exp.mpr hAneg
      have hA' : Real.exp (-2 * (Real.log x) ^ 2) ≤ 1 / 5 :=
        le_trans hA exp_neg_two_log_five_halves_le
      -- B side: x/(x-1) ≥ 3/2
      have hratio : (3 / 2 : ℝ) ≤ x / (x - 1) := (le_div_iff₀ hxsub).2 (by nlinarith)
      have hpos32 : 0 < (3 / 2 : ℝ) := by norm_num
      have hlog32le : Real.log (3 / 2) ≤ Real.log (x / (x - 1)) :=
        Real.log_le_log (x := (3 / 2 : ℝ)) (y := x / (x - 1)) hpos32 hratio
      have hlog32pos : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)
      have hsqB : (Real.log (3 / 2)) ^ 2 ≤ (Real.log (x / (x - 1))) ^ 2 :=
        sq_le_sq_of_nonneg hlog32pos.le hlog32le
      have hmulB : 2 * (Real.log (3 / 2)) ^ 2 ≤ 2 * (Real.log (x / (x - 1))) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsqB (by norm_num)
      have hBneg : -2 * (Real.log (x / (x - 1))) ^ 2 ≤ -2 * (Real.log (3 / 2)) ^ 2 := by linarith
      have hB : Real.exp (-2 * (Real.log (x / (x - 1))) ^ 2) ≤
          Real.exp (-2 * (Real.log (3 / 2)) ^ 2) := Real.exp_le_exp.mpr hBneg
      have hB' : Real.exp (-2 * (Real.log (x / (x - 1))) ^ 2) ≤ 3 / 4 :=
        le_trans hB exp_neg_two_log_three_halves_le
      nlinarith
    · -- case x ≥ 3: tail estimate A + B < 1/x^2 + (1 - 1/x^2) = 1
      have h3lt : (3 : ℝ) < x := lt_of_not_ge h3
      have h3le : (3 : ℝ) ≤ x := le_of_lt h3lt
      have hlog3le : Real.log 3 ≤ Real.log x :=
        Real.log_le_log (x := (3 : ℝ)) (y := x) (by norm_num : (0 : ℝ) < 3) h3le
      have hlog3gt1 : (1 : ℝ) < Real.log 3 := by
        have h1 := Real.log_three_gt_d9
        norm_num at h1
        linarith
      have hlogxpos : 0 < Real.log x := Real.log_pos hx1
      have hdif : 0 ≤ Real.log x - Real.log 3 := sub_nonneg.mpr hlog3le
      have hm1 : 0 ≤ Real.log x * (Real.log x - Real.log 3) :=
        mul_nonneg hlogxpos.le hdif
      have hneg1 : -2 * (Real.log x) ^ 2 ≤ -2 * Real.log 3 * Real.log x := by
        nlinarith [hm1]
      have hA1 : Real.exp (-2 * (Real.log x) ^ 2) ≤ Real.exp (-2 * Real.log 3 * Real.log x) :=
        Real.exp_le_exp.mpr hneg1
      have hlt1 : -2 * Real.log 3 * Real.log x < -2 * Real.log x := by
        have hm2 : 0 < (Real.log 3 - 1) * Real.log x :=
          mul_pos (sub_pos.mpr hlog3gt1) hlogxpos
        nlinarith [hm2]
      have hlt2 : Real.exp (-2 * Real.log 3 * Real.log x) < Real.exp (-2 * Real.log x) :=
        Real.exp_lt_exp.mpr hlt1
      have hA2 : Real.exp (-2 * (Real.log x) ^ 2) < Real.exp (-2 * Real.log x) :=
        lt_of_le_of_lt hA1 hlt2
      -- exp(-2 log x) = 1/x^2
      have hE : Real.exp (-2 * Real.log x) = 1 / x ^ 2 := by
        have harg : -2 * Real.log x = (((2 : ℕ) : ℝ) * (-Real.log x)) := by ring
        rw [harg]
        rw [Real.exp_nat_mul (-Real.log x) 2]
        rw [Real.exp_neg, Real.exp_log hx0]
        field_simp [hxne]
      have hA3 : Real.exp (-2 * (Real.log x) ^ 2) < 1 / x ^ 2 := by
        rwa [hE] at hA2
      -- B side: s = log(x/(x-1)) ≥ 1/x, hence exp(-2s^2) ≤ exp(-2/x^2)
      have hX : 0 < x / (x - 1) := div_pos hx0 hxsub
      have hlog : 1 - (x / (x - 1))⁻¹ ≤ Real.log (x / (x - 1)) :=
        Real.one_sub_inv_le_log_of_pos hX
      have hsimpl : 1 - (x / (x - 1))⁻¹ = 1 / x := by
        field_simp [hxne, hxsubne]
        ring
      have hzge : (1 / x : ℝ) ≤ Real.log (x / (x - 1)) := by
        rwa [hsimpl] at hlog
      have hsqz : (1 / x) ^ 2 ≤ (Real.log (x / (x - 1))) ^ 2 :=
        sq_le_sq_of_nonneg (by positivity) hzge
      have hzneg : -2 * (Real.log (x / (x - 1))) ^ 2 ≤ -2 * (1 / x) ^ 2 := by
        have hm : 2 * (1 / x) ^ 2 ≤ 2 * (Real.log (x / (x - 1))) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hsqz (by norm_num)
        linarith
      have hB : Real.exp (-2 * (Real.log (x / (x - 1))) ^ 2) ≤ Real.exp (-2 * (1 / x) ^ 2) :=
        Real.exp_le_exp.mpr hzneg
      have hyy : (1 / x) ^ 2 = 1 / x ^ 2 := by ring
      have hB' : Real.exp (-2 * (Real.log (x / (x - 1))) ^ 2) ≤ Real.exp (-2 * (1 / x ^ 2)) := by
        simpa [hyy] using hB
      have hy0 : 0 ≤ 1 / x ^ 2 := by positivity
      have hy1 : 1 / x ^ 2 ≤ 1 / 2 := by
        have hx2 : 9 ≤ x ^ 2 := by nlinarith [sq_le_sq_of_nonneg (by norm_num : 0 ≤ (3:ℝ)) h3le]
        have : 1 / x ^ 2 ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num : 0 < (9 : ℝ)) hx2
        linarith
      have hC : Real.exp (-2 * (1 / x ^ 2)) ≤ 1 - 1 / x ^ 2 :=
        exp_neg_two_mul_le_sub_one hy0 hy1
      have hB'' : Real.exp (-2 * (Real.log (x / (x - 1))) ^ 2) ≤ 1 - 1 / x ^ 2 :=
        le_trans hB' hC
      nlinarith

/-- The requested inequality: `e^{-2 log^2 x} + e^{-2 log^2(x/(x-1))} < 1` for `x > 1`. -/
lemma exp_neg_two_log_sq_add_lt_one (x : ℝ) (hx : 1 < x) :
    Real.exp (-2 * (Real.log x) ^ 2) + Real.exp (-2 * (Real.log (x / (x - 1))) ^ 2) < 1 := by
  by_cases hxle2 : x ≤ 2
  · -- x ∈ (1, 2]: use symmetry x ↦ x/(x-1) ≥ 2
    set y : ℝ := x / (x - 1)
    have hxsub : 0 < x - 1 := by linarith
    have hx0 : 0 < x := by linarith
    have hxsubne : x - 1 ≠ 0 := ne_of_gt hxsub
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hy2 : 2 ≤ y := by
      dsimp [y]
      rw [le_div_iff₀ hxsub]
      nlinarith
    have hmain := lt_one_of_two_le y hy2
    have hyid : y / (y - 1) = x := by
      dsimp [y]
      have hy1 : y - 1 ≠ 0 := by
        dsimp [y]
        nlinarith
      field_simp [hxsubne, hxne, hy1]
      ring
    have hlogy : Real.log y = Real.log (x / (x - 1)) := by dsimp [y]
    have hlogyid : Real.log (y / (y - 1)) = Real.log x := by rw [hyid]
    rw [hlogy, hlogyid] at hmain
    simpa [add_comm] using hmain
  · -- x ≥ 2
    exact lt_one_of_two_le x (lt_of_not_ge hxle2).le


end Commons.Analysis.LogClaim