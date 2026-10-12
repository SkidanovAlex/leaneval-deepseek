import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- For `s, c ≥ 0` one has `s (√(s+1) - √c)² ≤ (s+1-c)²`.

Writing `A = √(s+1)`, `B = √c` (so `0 ≤ B`, `A² = s+1`), the right-hand side is
`(A² - B²)² = (A-B)²(A+B)²`, so it suffices to bound `s ≤ (A+B)²`.
Since `A ≤ A+B` with both nonnegative, `A² ≤ (A+B)²`, and `s ≤ A² = s+1`. -/
theorem mulSqrtSubSqLeSqB1 {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c) :
    s * (Real.sqrt (s + 1) - Real.sqrt c) ^ 2 ≤ (s + 1 - c) ^ 2 := by
  set A := Real.sqrt (s + 1) with hA
  set B := Real.sqrt c with hB
  have hA2 : A ^ 2 = s + 1 := by rw [hA]; exact Real.sq_sqrt (by linarith)
  have hB2 : B ^ 2 = c := by rw [hB]; exact Real.sq_sqrt hc
  have hA0 : 0 ≤ A := by rw [hA]; exact Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := by rw [hB]; exact Real.sqrt_nonneg _
  have hle : s ≤ (A + B) ^ 2 := by
    have h1 : A ^ 2 ≤ (A + B) ^ 2 := pow_le_pow_left₀ hA0 (by linarith) 2
    linarith
  calc s * (A - B) ^ 2 ≤ (A + B) ^ 2 * (A - B) ^ 2 :=
        mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = (s + 1 - c) ^ 2 := by
        have h : (A + B) ^ 2 * (A - B) ^ 2 = (A ^ 2 - B ^ 2) ^ 2 := by ring
        rw [h, hA2, hB2]

end Work.BoseFixB1S
