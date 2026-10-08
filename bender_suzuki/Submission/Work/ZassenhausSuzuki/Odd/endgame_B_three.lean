import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

/-- Auxiliary rational identity: after combining `(A-1)/(4A) + (Bb-1)/(4Bb)` into a
single fraction, the remaining computation only involves `Q`, the product
`p = A*Bb` and `MM`, subject to `p*MM = Q^2+1`. -/
private lemma arith2 {Q p MM : ℚ} (hQ1 : Q - 1 ≠ 0) (hp : p ≠ 0)
    (hM : p * MM = Q ^ 2 + 1) :
    Q ^ 2 * (Q - 1) * (Q ^ 2 + 1) - Q ^ 4
      - Q ^ 2 * (Q - 1) * (Q ^ 2 + 1) / (2 * (Q - 1)) * (Q - 2)
      - Q ^ 2 * (Q - 1) * (Q ^ 2 + 1) * (2 * p - (2 * Q + 2)) / (4 * p)
    = Q ^ 2 * (Q - 1) * (Q + 1) * (MM - 1) / 2 := by
  have hfrac : Q ^ 2 * (Q - 1) * (Q ^ 2 + 1) / (2 * (Q - 1)) = Q ^ 2 * (Q ^ 2 + 1) / 2 := by
    have h : (2 : ℚ) * (Q - 1) ≠ 0 := mul_ne_zero (by norm_num) hQ1
    rw [div_eq_iff h]; ring
  have hMM : MM - 1 = (Q ^ 2 + 1 - p) / p := by
    rw [eq_div_iff hp]
    linear_combination hM
  rw [hfrac, hMM]
  field_simp
  ring

/-- The pure rational arithmetic underlying `endgame_B_three`. -/
private lemma arith {Q A Bb MM P : ℚ}
    (hQ1 : Q - 1 ≠ 0) (hA : A ≠ 0) (hBb : Bb ≠ 0)
    (hP : P = Q ^ 2 * (Q - 1) * (Q ^ 2 + 1))
    (hsum : A + Bb = 2 * Q + 2)
    (hM : A * Bb * MM = Q ^ 2 + 1) :
    P - Q ^ 4 - P / (2 * (Q - 1)) * (Q - 2) - P / (4 * A) * (A - 1)
      - P / (4 * Bb) * (Bb - 1)
      = Q ^ 2 * (Q - 1) * (Q + 1) * (MM - 1) / 2 := by
  rw [hP]
  have hp : A * Bb ≠ 0 := mul_ne_zero hA hBb
  have hA2 : (Q ^ 2 * (Q - 1) * (Q ^ 2 + 1)) / (4 * A) * (A - 1)
      + (Q ^ 2 * (Q - 1) * (Q ^ 2 + 1)) / (4 * Bb) * (Bb - 1)
      = (Q ^ 2 * (Q - 1) * (Q ^ 2 + 1)) * (2 * (A * Bb) - (2 * Q + 2)) / (4 * (A * Bb)) := by
    rw [← hsum]
    field_simp
    ring
  have h2 := arith2 (Q := Q) (p := A * Bb) (MM := MM) hQ1 hp hM
  linarith [hA2, h2]

lemma endgame_B_three {q B a b M : ℕ} {m : ℕ → ℕ}
    (hq : 2 ≤ q) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm1 : m (q - 1) * (q - 1) * 2 = q ^ 2 * (q - 1) * (q ^ 2 + 1))
    (hma : m a * a * 4 = q ^ 2 * (q - 1) * (q ^ 2 + 1))
    (hmb : m b * b * 4 = q ^ 2 * (q - 1) * (q ^ 2 + 1))
    (hsum1 : (m (q - 1) : ℚ) * (((q - 1 : ℕ) : ℚ) - 1) + (m a : ℚ) * ((a : ℚ) - 1)
        + (m b : ℚ) * ((b : ℚ) - 1)
        = (q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℚ) - (q : ℚ) ^ 4 - (B : ℚ))
    (hsum : a + b = 2 * q + 2)
    (hM : a * b * M = q ^ 2 + 1) :
    (B : ℚ) = (q : ℚ) ^ 2 * ((q : ℚ) - 1) * ((q : ℚ) + 1) * ((M : ℚ) - 1) / 2 := by
  have h1q : 1 ≤ q := by omega
  have hC : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 := by rw [Nat.cast_sub h1q]; norm_num
  have hQ1 : (q : ℚ) - 1 ≠ 0 := by
    have h : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    linarith
  have hA0 : (a : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < (a : ℚ) := by
      have : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
      linarith
    exact ne_of_gt h
  have hBb0 : (b : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < (b : ℚ) := by
      have : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
      linarith
    exact ne_of_gt h
  have h2Q1 : (2 : ℚ) * ((q : ℚ) - 1) ≠ 0 := by
    have h : (0 : ℚ) < (q : ℚ) - 1 := by
      have : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
      linarith
    positivity
  have hm1q : (m (q - 1) : ℚ) * ((q - 1 : ℕ) : ℚ) * 2
      = ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ) := by
    exact_mod_cast hm1
  have hmaq : (m a : ℚ) * (a : ℚ) * 4 = ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ) := by
    exact_mod_cast hma
  have hmbq : (m b : ℚ) * (b : ℚ) * 4 = ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ) := by
    exact_mod_cast hmb
  rw [hC] at hm1q hsum1
  have hU : (m (q - 1) : ℚ)
      = ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ) / (2 * ((q : ℚ) - 1)) := by
    rw [eq_div_iff h2Q1]
    linear_combination hm1q
  have hV : (m a : ℚ) = ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ) / (4 * (a : ℚ)) := by
    rw [eq_div_iff (by exact mul_ne_zero (by norm_num) hA0)]
    linear_combination hmaq
  have hW : (m b : ℚ) = ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ) / (4 * (b : ℚ)) := by
    rw [eq_div_iff (by exact mul_ne_zero (by norm_num) hBb0)]
    linear_combination hmbq
  have hPq : ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ)
      = (q : ℚ) ^ 2 * ((q : ℚ) - 1) * ((q : ℚ) ^ 2 + 1) := by
    push_cast
    rw [hC]
  have hBexpr : (B : ℚ) = ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ) - (q : ℚ) ^ 4
      - ((m (q - 1) : ℚ) * ((q : ℚ) - 2) + (m a : ℚ) * ((a : ℚ) - 1)
          + (m b : ℚ) * ((b : ℚ) - 1)) := by
    linarith [hsum1]
  rw [hU, hV, hW, hPq] at hBexpr
  have hsumq : (a : ℚ) + (b : ℚ) = 2 * (q : ℚ) + 2 := by exact_mod_cast hsum
  have hMq : (a : ℚ) * (b : ℚ) * (M : ℚ) = (q : ℚ) ^ 2 + 1 := by exact_mod_cast hM
  have halg := arith (P := (q : ℚ) ^ 2 * ((q : ℚ) - 1) * ((q : ℚ) ^ 2 + 1))
    hQ1 hA0 hBb0 rfl hsumq hMq
  linarith [hBexpr, halg]

end Work.ZassenhausSuzuki.Odd
