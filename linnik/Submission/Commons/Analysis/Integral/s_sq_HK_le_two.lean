import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Integral

private lemma sq_le_of_le_sixth {s : ℝ} (hs0 : 0 ≤ s) (hs6 : s ≤ 1/6) : s^2 ≤ 1/36 := by
  have h1 : (0:ℝ) ≤ 1/6 - s := by linarith
  have h2 : (0:ℝ) ≤ 1/6 + s := by linarith
  nlinarith [mul_nonneg h1 h2]

private lemma div_sq_add_sq_sq_le_inv_cube {x s : ℝ} (hx : 0 < x) :
    x / ((x^2 + s^2)^2) ≤ 1 / x^3 := by
  have hxs : x^2 ≤ x^2 + s^2 := by nlinarith [sq_nonneg s]
  have h4 : x^4 ≤ (x^2+s^2)^2 := by
    have h := pow_le_pow_left₀ (sq_nonneg x) hxs 2
    nlinarith [h]
  have hx4 : 0 < x^4 := by positivity
  have h1 : x / ((x^2+s^2)^2) ≤ x / x^4 :=
    div_le_div_of_nonneg_left (le_of_lt hx) hx4 h4
  have h2 : x / x^4 = 1 / x^3 := by field_simp
  rw [h2] at h1
  exact h1

private lemma term1 {β s : ℝ} (hβ1 : β < 1) (hs0 : 0 < s) (hs6 : s ≤ 1/6) :
    s^2 * ((26/5) * ((3/2 - β) / (((3/2 - β)^2 + s^2)^2))) ≤ 52/45 := by
  have ha : (1/2:ℝ) ≤ 3/2 - β := by linarith
  have hapos : 0 < 3/2 - β := by linarith
  have hA1 : (3/2-β)/(((3/2-β)^2+s^2)^2) ≤ 1/(3/2-β)^3 :=
    div_sq_add_sq_sq_le_inv_cube hapos
  have hA2 : (1:ℝ)/(3/2-β)^3 ≤ 8 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (3/2-β)^3)]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) ha 3
    nlinarith [h]
  have hA : (3/2-β)/(((3/2-β)^2+s^2)^2) ≤ 8 := le_trans hA1 hA2
  have hsle : s^2 ≤ 1/36 := sq_le_of_le_sixth (le_of_lt hs0) hs6
  calc s^2 * ((26/5) * ((3/2 - β) / (((3/2 - β)^2 + s^2)^2)))
      = (26/5) * (s^2 * ((3/2 - β) / (((3/2 - β)^2 + s^2)^2))) := by ring
    _ ≤ (26/5) * (s^2 * 8) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hA (sq_nonneg s)
    _ = (26/5) * 8 * s^2 := by ring
    _ ≤ (26/5) * 8 * (1/36) := by
        apply mul_le_mul_of_nonneg_left hsle (by norm_num)
    _ = 52/45 := by norm_num

private lemma term2 {β s : ℝ} (hβ0 : 0 < β) (hs0 : 0 < s) (hs6 : s ≤ 1/6) :
    s^2 * ((26/5) * ((1 + β) / (((1 + β)^2 + s^2)^2))) ≤ 13/90 := by
  have hb1 : (1:ℝ) ≤ 1 + β := by linarith
  have hbpos : 0 < 1 + β := by linarith
  have hB1 : (1+β)/(((1+β)^2+s^2)^2) ≤ 1/(1+β)^3 :=
    div_sq_add_sq_sq_le_inv_cube hbpos
  have hB2 : (1:ℝ)/(1+β)^3 ≤ 1 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+β)^3)]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hb1 3
    nlinarith [h]
  have hB : (1+β)/(((1+β)^2+s^2)^2) ≤ 1 := le_trans hB1 hB2
  have hsle : s^2 ≤ 1/36 := sq_le_of_le_sixth (le_of_lt hs0) hs6
  calc s^2 * ((26/5) * ((1 + β) / (((1 + β)^2 + s^2)^2)))
      = (26/5) * (s^2 * ((1 + β) / (((1 + β)^2 + s^2)^2))) := by ring
    _ ≤ (26/5) * (s^2 * 1) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hB (sq_nonneg s)
    _ = (26/5) * 1 * s^2 := by ring
    _ ≤ (26/5) * 1 * (1/36) := by
        apply mul_le_mul_of_nonneg_left hsle (by norm_num)
    _ = 13/90 := by norm_num

private lemma term3 {β s : ℝ} (hβ1 : β < 1) (hs0 : 0 < s) (hs6 : s ≤ 1/6) :
    s^2 * (((2-β)^2-β^2)/(((2-β)^2+s^2)^2)) ≤ 1/36 := by
  have hc1 : (1:ℝ) ≤ 2 - β := by linarith
  have hc2_1 : (1:ℝ) ≤ (2-β)^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hc1 2
    simpa using h
  have hd0 : 0 ≤ (2-β)^2 - β^2 := by nlinarith [hβ1]
  have hdc : (2-β)^2 - β^2 ≤ (2-β)^2 := by nlinarith [sq_nonneg β]
  have hcs : (2-β)^2 ≤ (2-β)^2 + s^2 := by nlinarith [sq_nonneg s]
  have hc4le : (2-β)^4 ≤ ((2-β)^2+s^2)^2 := by
    have h := pow_le_pow_left₀ (sq_nonneg (2-β)) hcs 2
    nlinarith [h]
  have hA3 : ((2-β)^2-β^2)/(((2-β)^2+s^2)^2) ≤ 1 := by
    have h := div_le_div₀ (by positivity : (0:ℝ) ≤ (2-β)^2) hdc
                (by positivity : (0:ℝ) < (2-β)^4) hc4le
    have heq : (2-β)^2/(2-β)^4 = 1/(2-β)^2 := by field_simp
    have hle : (1:ℝ)/(2-β)^2 ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (2-β)^2)]
      nlinarith [hc2_1]
    rw [heq] at h
    linarith [h, hle]
  have hsle : s^2 ≤ 1/36 := sq_le_of_le_sixth (le_of_lt hs0) hs6
  calc s^2 * (((2-β)^2-β^2)/(((2-β)^2+s^2)^2))
      ≤ s^2 * 1 := mul_le_mul_of_nonneg_left hA3 (sq_nonneg s)
    _ = s^2 := by ring
    _ ≤ 1/36 := hsle

private lemma term4 {β s : ℝ} (hβ1 : β < 1) (hs0 : 0 < s) (hs6 : s ≤ 1/6) :
    s^2 * (((2-β)^2-β^2)^2/(2*((2-β)^2+s^2)^3)) ≤ 1/72 := by
  have hc1 : (1:ℝ) ≤ 2 - β := by linarith
  have hc2_1 : (1:ℝ) ≤ (2-β)^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hc1 2
    simpa using h
  have hd0 : 0 ≤ (2-β)^2 - β^2 := by nlinarith [hβ1]
  have hdc : (2-β)^2 - β^2 ≤ (2-β)^2 := by nlinarith [sq_nonneg β]
  have hcs : (2-β)^2 ≤ (2-β)^2 + s^2 := by nlinarith [sq_nonneg s]
  have hd2 : ((2-β)^2-β^2)^2 ≤ (2-β)^4 := by
    have h := pow_le_pow_left₀ hd0 hdc 2
    nlinarith [h]
  have hmul6 : 2*(2-β)^6 ≤ 2*((2-β)^2+s^2)^3 := by
    have h := pow_le_pow_left₀ (sq_nonneg (2-β)) hcs 3
    nlinarith [h]
  have hA4 : ((2-β)^2-β^2)^2/(2*((2-β)^2+s^2)^3) ≤ 1/2 := by
    have h := div_le_div₀ (by positivity : (0:ℝ) ≤ (2-β)^4) hd2
                (by positivity : (0:ℝ) < 2*(2-β)^6) hmul6
    have heq : (2-β)^4/(2*(2-β)^6) = 1/(2*(2-β)^2) := by field_simp
    have hle : (1:ℝ)/(2*(2-β)^2) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(2-β)^2)]
      nlinarith [hc2_1]
    rw [heq] at h
    linarith [h, hle]
  have hsle : s^2 ≤ 1/36 := sq_le_of_le_sixth (le_of_lt hs0) hs6
  calc s^2 * (((2-β)^2-β^2)^2/(2*((2-β)^2+s^2)^3))
      ≤ s^2 * (1/2) := mul_le_mul_of_nonneg_left hA4 (sq_nonneg s)
    _ ≤ (1/36) * (1/2) := mul_le_mul_of_nonneg_right hsle (by norm_num)
    _ = 1/72 := by norm_num

private lemma term5 {β s : ℝ} (hβ1 : β < 1) (hs0 : 0 < s) (hs6 : s ≤ 1/6) :
    s^2 * (3*((2-β)^2-β^2)^3/(8*((2-β)^2+s^2)^4)) ≤ 1/96 := by
  have hc1 : (1:ℝ) ≤ 2 - β := by linarith
  have hc2_1 : (1:ℝ) ≤ (2-β)^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hc1 2
    simpa using h
  have hd0 : 0 ≤ (2-β)^2 - β^2 := by nlinarith [hβ1]
  have hdc : (2-β)^2 - β^2 ≤ (2-β)^2 := by nlinarith [sq_nonneg β]
  have hcs : (2-β)^2 ≤ (2-β)^2 + s^2 := by nlinarith [sq_nonneg s]
  have hd3 : 3*((2-β)^2-β^2)^3 ≤ 3*(2-β)^6 := by
    have h := pow_le_pow_left₀ hd0 hdc 3
    nlinarith [h]
  have hmul8 : 8*(2-β)^8 ≤ 8*((2-β)^2+s^2)^4 := by
    have h := pow_le_pow_left₀ (sq_nonneg (2-β)) hcs 4
    nlinarith [h]
  have hA5 : 3*((2-β)^2-β^2)^3/(8*((2-β)^2+s^2)^4) ≤ 3/8 := by
    have h := div_le_div₀ (by positivity : (0:ℝ) ≤ 3*(2-β)^6) hd3
                (by positivity : (0:ℝ) < 8*(2-β)^8) hmul8
    have heq : 3*(2-β)^6/(8*(2-β)^8) = 3/(8*(2-β)^2) := by field_simp
    have hle : (3:ℝ)/(8*(2-β)^2) ≤ 3/8 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 8*(2-β)^2)]
      nlinarith [hc2_1]
    rw [heq] at h
    linarith [h, hle]
  have hsle : s^2 ≤ 1/36 := sq_le_of_le_sixth (le_of_lt hs0) hs6
  calc s^2 * (3*((2-β)^2-β^2)^3/(8*((2-β)^2+s^2)^4))
      ≤ s^2 * (3/8) := mul_le_mul_of_nonneg_left hA5 (sq_nonneg s)
    _ ≤ (1/36) * (3/8) := mul_le_mul_of_nonneg_right hsle (by norm_num)
    _ = 1/96 := by norm_num

private lemma term6 {β s : ℝ} (hβ1 : β < 1) (hs0 : 0 < s) (hs6 : s ≤ 1/6) :
    s^2 * (1/(2*(2-β)^2)) ≤ 1/72 := by
  have hc1 : (1:ℝ) ≤ 2 - β := by linarith
  have hc2_1 : (1:ℝ) ≤ (2-β)^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hc1 2
    simpa using h
  have hA6 : (1:ℝ)/(2*(2-β)^2) ≤ 1/2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(2-β)^2)]
    nlinarith [hc2_1]
  have hsle : s^2 ≤ 1/36 := sq_le_of_le_sixth (le_of_lt hs0) hs6
  calc s^2 * (1/(2*(2-β)^2))
      ≤ s^2 * (1/2) := mul_le_mul_of_nonneg_left hA6 (sq_nonneg s)
    _ ≤ (1/36) * (1/2) := mul_le_mul_of_nonneg_right hsle (by norm_num)
    _ = 1/72 := by norm_num

private lemma term7 {β s : ℝ} (hβ0 : 0 < β) (hs0 : 0 < s) (hsβ : s ≤ β) :
    s^2 * (1/(2*β^2)) ≤ 1/2 := by
  have hβ2pos : (0:ℝ) < 2*β^2 := by positivity
  have hs2β2 : s^2 ≤ β^2 := by
    have h := pow_le_pow_left₀ (le_of_lt hs0) hsβ 2
    simpa using h
  have heq : s^2 * (1/(2*β^2)) = s^2/(2*β^2) := by rw [mul_one_div]
  rw [heq, div_le_iff₀ hβ2pos]
  nlinarith [hs2β2]

theorem s_sq_HK_le_two {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hsβ : s ≤ β) (hs6 : s ≤ 1/6) :
    s^2*((26/5)*((3/2-β)/(((3/2-β)^2+s^2)^2) + (1+β)/(((1+β)^2+s^2)^2))
      + ((2-β)^2-β^2)/(((2-β)^2+s^2)^2)
      + ((2-β)^2-β^2)^2/(2*((2-β)^2+s^2)^3)
      + 3*((2-β)^2-β^2)^3/(8*((2-β)^2+s^2)^4)
      + 1/(2*(2-β)^2) + 1/(2*β^2)) ≤ 2 := by
  have h1 := term1 hβ1 hs0 hs6
  have h2 := term2 hβ0 hs0 hs6
  have h3 := term3 hβ1 hs0 hs6
  have h4 := term4 hβ1 hs0 hs6
  have h5 := term5 hβ1 hs0 hs6
  have h6 := term6 hβ1 hs0 hs6
  have h7 := term7 hβ0 hs0 hsβ
  have hsplit : s^2*((26/5)*((3/2-β)/(((3/2-β)^2+s^2)^2) + (1+β)/(((1+β)^2+s^2)^2))
      + ((2-β)^2-β^2)/(((2-β)^2+s^2)^2)
      + ((2-β)^2-β^2)^2/(2*((2-β)^2+s^2)^3)
      + 3*((2-β)^2-β^2)^3/(8*((2-β)^2+s^2)^4)
      + 1/(2*(2-β)^2) + 1/(2*β^2))
      = s^2 * ((26/5) * ((3/2-β)/(((3/2-β)^2+s^2)^2)))
        + s^2 * ((26/5) * ((1+β)/(((1+β)^2+s^2)^2)))
        + s^2 * (((2-β)^2-β^2)/(((2-β)^2+s^2)^2))
        + s^2 * (((2-β)^2-β^2)^2/(2*((2-β)^2+s^2)^3))
        + s^2 * (3*((2-β)^2-β^2)^3/(8*((2-β)^2+s^2)^4))
        + s^2 * (1/(2*(2-β)^2))
        + s^2 * (1/(2*β^2)) := by ring
  rw [hsplit]
  have hsum : ((52/45:ℝ) + 13/90 + 1/36 + 1/72 + 1/96 + 1/72 + 1/2) ≤ 2 := by norm_num
  have hs := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6) h7
  linarith [hs, hsum]

end Commons.Analysis.Integral