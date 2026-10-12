import Mathlib.Analysis.Real.Sqrt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7

/-- The elementary square-root estimate used in the dilute-Bose-gas energy bounds.

From `Q ≤ S * S * (M * W)` with `S, W ≥ 0` and `M * W ≥ 0` we get
`√Q * √W ≤ S * √M * W`. -/
theorem sqrt_mul_sqrt_le {S M W Q : ℝ} (hS : 0 ≤ S) (hW : 0 ≤ W) (hMW : 0 ≤ M * W)
    (h : Q ≤ S * S * (M * W)) :
    Real.sqrt Q * Real.sqrt W ≤ S * Real.sqrt M * W := by
  rcases hW.eq_or_lt with hW0 | hWpos
  · -- degenerate case `W = 0`: both sides vanish
    subst hW0
    simp
  · -- `W > 0`: then `M ≥ 0`, so `√(S²·(M·W)) = S·√(M·W)`
    have hM : 0 ≤ M := nonneg_of_mul_nonneg_left hMW hWpos
    have hSS : 0 ≤ S * S := mul_nonneg hS hS
    have hstep : Real.sqrt Q ≤ S * Real.sqrt (M * W) := by
      calc Real.sqrt Q ≤ Real.sqrt (S * S * (M * W)) := Real.sqrt_le_sqrt h
        _ = Real.sqrt (S * S) * Real.sqrt (M * W) := Real.sqrt_mul hSS (M * W)
        _ = S * Real.sqrt (M * W) := by rw [Real.sqrt_mul_self hS]
    have h2 : Real.sqrt Q * Real.sqrt W ≤ S * Real.sqrt (M * W) * Real.sqrt W :=
      mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg W)
    have hsqW : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW
    have h3 : S * Real.sqrt (M * W) * Real.sqrt W = S * Real.sqrt M * W := by
      rw [Real.sqrt_mul hM W]
      calc S * (Real.sqrt M * Real.sqrt W) * Real.sqrt W
          = S * Real.sqrt M * (Real.sqrt W * Real.sqrt W) := by ring
        _ = S * Real.sqrt M * W := by rw [hsqW]
    rwa [h3] at h2

end Work.BoseB7
