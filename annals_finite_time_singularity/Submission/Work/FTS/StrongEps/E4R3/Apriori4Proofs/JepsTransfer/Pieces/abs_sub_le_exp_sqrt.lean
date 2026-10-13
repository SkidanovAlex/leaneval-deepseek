import Mathlib.Analysis.Real.Sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

/-- Two nonnegative reals that are comparable up to a factor `E ≥ 1` are within
`(E - 1)·√(a·b)` of each other.  Elementary: if `b ≤ a ≤ E·b` then
`a - b ≤ (E - 1)·b ≤ (E - 1)·√(a·b)` (as `b ≤ √(a·b)` when `b ≤ a`); the other case is
symmetric. -/
theorem abs_sub_le_exp_sqrt {a b E : ℝ} (hE : 1 ≤ E) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : a ≤ E * b) (h2 : b ≤ E * a) :
    |a - b| ≤ (E - 1) * Real.sqrt (a * b) := by
  have hE1 : 0 ≤ E - 1 := by linarith
  have step : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ E * x →
      y - x ≤ (E - 1) * Real.sqrt (x * y) := by
    intro x y hx hxy hyE
    have hs : Real.sqrt (x * x) ≤ Real.sqrt (x * y) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hxy hx)
    have hxs : x ≤ Real.sqrt (x * y) := by rwa [Real.sqrt_mul_self hx] at hs
    calc y - x ≤ (E - 1) * x := by nlinarith [hyE]
      _ ≤ (E - 1) * Real.sqrt (x * y) := mul_le_mul_of_nonneg_left hxs hE1
  rcases le_total b a with hba | hab
  · have h := step b a hb hba h1
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)]
    simpa [mul_comm] using h
  · have h := step a b ha hab h2
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)]
    exact h

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
