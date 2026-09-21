import Mathlib
import Submission.Work.OddCurve.LowSlope.second_deriv_A_le_two
import Submission.Work.OddCurve.LowSlope.second_deriv_C_le
import Submission.Work.OddCurve.LowSlope.second_deriv_T2_le

/-!
# The numeric second-derivative core inequality

`second_deriv_core` is the purely algebraic estimate at the heart of the low-slope odd
reconstruction (`second_deriv_numeric`).  With `k₁ = 2n+1`, `k₂ = 2n+2`,
`E = R ^ k₂ + r ^ k₂ - 2`, `F = R ^ k₁ - r ^ k₁`, `p = 1 - 2|E|`, `q = 1 - 2|F|`,
it bounds the sum of the three terms

* `T₁ = (1 + r k₂/k₁) R² / (R ^ k₂ (R+r))`,
* `T₂ = (k₁ + k₂ r)(k₁ p + k₂ r q) / (k₂ k₁ R ^ (4n+1) (R+r)²)`,
* `T₃ = (k₁ + k₂ R)(k₁ p + k₂ R q) / (k₂ k₁² (R r) ^ (2n) (R+r)³)`

by `2 + 4/3 + 2/3 = 4`.  The three estimates are proved in the sibling files
`second_deriv_A_le_two.lean`, `second_deriv_T2_le.lean` and `second_deriv_C_le.lean`;
here we only add them up.  (Note `2 + 4/3 + 2/3 = 4` exactly.)
-/

namespace Work.OddCurve.LowSlope

theorem second_deriv_core (n : ℕ) (hn : 1 ≤ n) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (ha1 : 3 / 8 ≤ R ^ (2 * n + 2)) (ha2 : R ^ (2 * n + 2) ≤ 15 / 8)
    (hb1 : 3 / 8 ≤ r ^ (2 * n + 2)) (hb2 : r ^ (2 * n + 2) ≤ 15 / 8)
    (hm : |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2| ≤ 1 / 2)
    (hv : |R ^ (2 * n + 1) - r ^ (2 * n + 1)| ≤ 1 / 2) :
    let k1 : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    let k2 : ℝ := ((2 * n + 2 : ℕ) : ℝ)
    let p : ℝ := 1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|
    let q : ℝ := 1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|
    (1 + r * k2 / k1) * R ^ 2 / (R ^ (2 * n + 2) * (R + r))
      + (k1 + k2 * r) * (k1 * p + k2 * r * q)
          / (k2 * k1 * R ^ (4 * n + 1) * (R + r) ^ 2)
      + (k1 + k2 * R) * (k1 * p + k2 * R * q)
          / (k2 * k1 ^ 2 * (R * r) ^ (2 * n) * (R + r) ^ 3) ≤ 4 := by
  have hA := second_deriv_A_le_two n hn hR hr ha1 ha2 hb1 hb2 hm hv
  have hB := second_deriv_T2_le n hn hR hr ha1 ha2 hb1 hb2 hm hv
  have hC := second_deriv_C_le n hn hR hr ha1 ha2 hb1 hb2 hm hv
  dsimp only at hA hB hC ⊢
  linarith

end Work.OddCurve.LowSlope
