import Mathlib

namespace Work.FIArea6b

/-- Auxiliary algebraic step: if `0 < 1 + a - a/b` (with `a² + b² = 1`, `a ≥ 0`, `b > 0`)
then the vector `(1 + a - a/b, 1 - b)` has squared norm at most `1`. -/
private lemma key_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a^2 + b^2 = 1)
    (hc1 : 0 < 1 + a - a/b) :
    (1 + a - a/b)^2 + (1-b)^2 ≤ 1 := by
  have hb1 : b ≤ 1 := by nlinarith [hab, sq_nonneg a, hb]
  have hbmul : b * (1 + a - a/b) = b + a*b - a := by
    field_simp
  have hcond : 0 ≤ b + a*b - a := by
    have := mul_pos hb hc1
    rw [hbmul] at this
    exact le_of_lt this
  -- `2*a*b + b - 1 ≥ 0`, which is `b - (a-b)^2 ≥ 0`
  have hf : 0 ≤ 2*a*b + b - 1 := by
    have ha2 : a^2 ≤ 1 := by nlinarith [hab, sq_nonneg b]
    have hf_eq : 2*a*b + b - 1 = b - (a-b)^2 := by nlinarith [hab]
    rw [hf_eq]
    rcases le_or_gt b a with hba | hlt
    · -- `b ≤ a`: use the hypothesis `a - b ≤ a*b`
      have hab_ge : a - b ≤ a*b := by linarith [hcond]
      have h1 : 0 ≤ a - b := by linarith
      have hpos_ab : 0 ≤ a*b := by linarith
      have hsq1 : (a-b)^2 ≤ (a*b)^2 := by
        rw [sq_le_sq, abs_of_nonneg h1, abs_of_nonneg hpos_ab]; exact hab_ge
      have hsq2 : (a*b)^2 ≤ b^2 := by nlinarith [ha2, sq_nonneg b]
      nlinarith [hsq1, hsq2, hb1, hb]
    · -- `a < b`: then `0 ≤ b - a ≤ b`
      have h1 : 0 ≤ b - a := by linarith [hlt.le]
      have hsame : (a-b)^2 = (b-a)^2 := by ring
      have hsq : (b-a)^2 ≤ b^2 := by
        rw [sq_le_sq, abs_of_nonneg h1, abs_of_nonneg (le_of_lt hb)]
        linarith [ha]
      nlinarith [hsq, hsame, hb1, hb]
  -- identity: b² * ((1+a-a/b)² + (1-b)² - 1) = (b-1) * (2ab + b - 1)
  have hstep : b^2 * ((1 + a - a/b)^2 + (1-b)^2 - 1)
      = (b + a*b - a)^2 + b^2*(1-b)^2 - b^2 := by
    nlinarith [hbmul]
  have hdiff : (b + a*b - a)^2 + b^2*(1-b)^2 - b^2 - (b-1)*(2*a*b+b-1)
      = (b-1)^2*(a^2+b^2-1) := by ring
  have hz : a^2+b^2-1 = 0 := by linarith
  rw [hz, mul_zero] at hdiff
  have hpoly : b^2 * ((1 + a - a/b)^2 + (1-b)^2 - 1) = (b-1)*(2*a*b+b-1) := by
    rw [hstep]; linarith [hdiff]
  have hRHS : (b-1)*(2*a*b+b-1) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact hf
  have hLe : b^2 * ((1+a-a/b)^2+(1-b)^2-1) ≤ 0 := by rw [hpoly]; exact hRHS
  have hb2pos : 0 < b^2 := pow_pos hb 2
  have hfin : (1+a-a/b)^2+(1-b)^2-1 ≤ 0 := by
    have hLe' : b^2 * ((1+a-a/b)^2+(1-b)^2-1) ≤ b^2 * 0 := by rw [mul_zero]; exact hLe
    exact (mul_le_mul_iff_of_pos_left hb2pos).mp hLe'
  linarith

theorem aux_lem_Q (a b d K R : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a^2 + b^2 = 1)
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hKd : K^2 + d^2 = (2*R)^2) (hd : 0 ≤ d) :
    (1 + a - a/b)*d + (1-b)*K ≤ 2*R := by
  have hK_le : K ≤ 2*R := by nlinarith [hKd, sq_nonneg d, hK, hR]
  rcases le_or_gt (1 + a - a/b) 0 with hc1 | hc1
  · -- coefficient of `d` is nonpositive
    have h1 : (1 + a - a/b)*d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc1 hd
    have h2 : (1-b)*K ≤ K := by
      have : (1-b)*K ≤ 1*K := mul_le_mul_of_nonneg_right (by linarith) hK
      linarith
    linarith
  · -- coefficient of `d` is positive: Cauchy–Schwarz
    have hkey : (1 + a - a/b)^2 + (1-b)^2 ≤ 1 := key_sq a b ha hb hab hc1
    have hid : ((1+a-a/b)*d + (1-b)*K)^2 + ((1+a-a/b)*K - (1-b)*d)^2
        = ((1+a-a/b)^2 + (1-b)^2)*(d^2+K^2) := by ring
    have hdK : d^2 + K^2 = (2*R)^2 := by linarith [hKd]
    have hsq : ((1+a-a/b)*d + (1-b)*K)^2 ≤ (2*R)^2 := by
      have hprod : ((1+a-a/b)^2 + (1-b)^2)*(d^2+K^2) ≤ 1*(d^2+K^2) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
      have hprod2 : 1*(d^2+K^2) = (2*R)^2 := by rw [hdK]; ring
      nlinarith [hid, sq_nonneg ((1+a-a/b)*K - (1-b)*d), hprod, hprod2]
    have hle := sq_le_sq.mp hsq
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2*R)] at hle
    linarith [le_abs_self ((1+a-a/b)*d + (1-b)*K)]

end Work.FIArea6b
