import Mathlib

namespace Work.FIArea6b

/-- Purely algebraic core: with `a² + b² = 1`, `a,b ≥ 0` and `K² + d² = (2R)²`,
`K,d ≥ 0`, `R ≥ 0`, one has `(1-a)d + (1-b)K ≤ 2R`.
The proof is Cauchy–Schwarz combined with `a + b ≥ 1`. -/
theorem aux_lem_P (a b d K R : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2 + b^2 = 1)
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hKd : K^2 + d^2 = (2*R)^2) (hd : 0 ≤ d) :
    (1-a)*d + (1-b)*K ≤ 2*R := by
  have hab_ab : 0 ≤ a * b := mul_nonneg ha hb
  have hsum1 : 1 ≤ a + b := by nlinarith [sq_nonneg (a + b), hab_ab]
  -- Cauchy–Schwarz for the two vectors ((1-a), (1-b)) and (d, K)
  have hcs : ((1-a)*d + (1-b)*K)^2 ≤ ((1-a)^2 + (1-b)^2) * (d^2 + K^2) := by
    nlinarith [sq_nonneg ((1-a)*K - (1-b)*d)]
  have hc : (1-a)^2 + (1-b)^2 = 3 - 2*(a+b) := by nlinarith [hab]
  have h3 : 3 - 2*(a+b) ≤ 1 := by nlinarith [hsum1]
  have hkey : ((1-a)^2 + (1-b)^2) * (d^2 + K^2) ≤ (2*R)^2 := by
    rw [hc, add_comm (d^2) (K^2), hKd]
    have : (0:ℝ) ≤ (2*R)^2 := sq_nonneg _
    nlinarith [h3, this]
  have hS : ((1-a)*d + (1-b)*K)^2 ≤ (2*R)^2 := le_trans hcs hkey
  have ha1 : 0 ≤ 1 - a := by nlinarith [ha, hab, sq_nonneg b]
  have hb1 : 0 ≤ 1 - b := by nlinarith [hb, hab, sq_nonneg a]
  have hA : 0 ≤ (1-a)*d + (1-b)*K := add_nonneg (mul_nonneg ha1 hd) (mul_nonneg hb1 hK)
  nlinarith [hS, hA, hR]

end Work.FIArea6b
