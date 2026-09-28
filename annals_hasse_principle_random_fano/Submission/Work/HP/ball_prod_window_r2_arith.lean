import Mathlib

namespace Work.HP

lemma ball_prod_window_r2_arith (a b Ksmall X Y p q : ℝ)
    (hKsmall : 0 < Ksmall) (ha : 0 < a) (hb : 0 < b)
    (hp : 0 < p) (hpa : p ≤ 2 * a) (hq : 0 < q) (hqb : q ≤ 2 * b)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    Ksmall * (X ^ 2 / (a * b) + X / a + 1) * (Ksmall * Y ^ 2 / (a * b)) ≤
      Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / (p ^ 2 * q ^ 2) + 8 * X * Y ^ 2 / (p ^ 2 * q)
        + 4 * Y ^ 2 / (p * q)) := by
  -- Key polynomial consequences of `p ≤ 2a`, `q ≤ 2b`.
  have hp2 : p ^ 2 ≤ 4 * a ^ 2 := by nlinarith [sq_nonneg (2 * a - p), hpa, hp]
  have hq2 : q ^ 2 ≤ 4 * b ^ 2 := by nlinarith [sq_nonneg (2 * b - q), hqb, hq]
  have hpq : p * q ≤ 4 * a * b := by
    nlinarith [sq_nonneg (2 * a - p), sq_nonneg (2 * b - q), hpa, hqb, hp, hq, ha, hb]
  have hp2q : p ^ 2 * q ≤ 8 * a ^ 2 * b := by
    have h : p ^ 2 * q ≤ (4 * a ^ 2) * (2 * b) :=
      mul_le_mul hp2 hqb (le_of_lt hq) (by positivity)
    nlinarith [h]
  have hpq2 : p ^ 2 * q ^ 2 ≤ 16 * a ^ 2 * b ^ 2 := by
    have h : p ^ 2 * q ^ 2 ≤ (4 * a ^ 2) * (4 * b ^ 2) :=
      mul_le_mul hp2 hq2 (by positivity) (by positivity)
    nlinarith [h]
  -- The core inequality, term by term after expanding over a common denominator.
  have hT : (X ^ 2 / (a * b) + X / a + 1) * (Y ^ 2 / (a * b)) ≤
      16 * X ^ 2 * Y ^ 2 / (p ^ 2 * q ^ 2) + 8 * X * Y ^ 2 / (p ^ 2 * q)
        + 4 * Y ^ 2 / (p * q) := by
    have e : (X ^ 2 / (a * b) + X / a + 1) * (Y ^ 2 / (a * b)) =
        X ^ 2 * Y ^ 2 / (a ^ 2 * b ^ 2) + X * Y ^ 2 / (a ^ 2 * b) + Y ^ 2 / (a * b) := by
      field_simp
    rw [e]
    have t1 : X ^ 2 * Y ^ 2 / (a ^ 2 * b ^ 2) ≤ 16 * X ^ 2 * Y ^ 2 / (p ^ 2 * q ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h := mul_le_mul_of_nonneg_left hpq2 (by positivity : (0:ℝ) ≤ X ^ 2 * Y ^ 2)
      nlinarith [h]
    have t2 : X * Y ^ 2 / (a ^ 2 * b) ≤ 8 * X * Y ^ 2 / (p ^ 2 * q) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h := mul_le_mul_of_nonneg_left hp2q (by positivity : (0:ℝ) ≤ X * Y ^ 2)
      nlinarith [h]
    have t3 : Y ^ 2 / (a * b) ≤ 4 * Y ^ 2 / (p * q) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h := mul_le_mul_of_nonneg_left hpq (by positivity : (0:ℝ) ≤ Y ^ 2)
      nlinarith [h]
    linarith
  have hK2 : (0:ℝ) ≤ Ksmall ^ 2 := by positivity
  calc Ksmall * (X ^ 2 / (a * b) + X / a + 1) * (Ksmall * Y ^ 2 / (a * b))
      = Ksmall ^ 2 * ((X ^ 2 / (a * b) + X / a + 1) * (Y ^ 2 / (a * b))) := by ring
    _ ≤ Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / (p ^ 2 * q ^ 2) + 8 * X * Y ^ 2 / (p ^ 2 * q)
          + 4 * Y ^ 2 / (p * q)) :=
        mul_le_mul_of_nonneg_left hT hK2

end Work.HP
