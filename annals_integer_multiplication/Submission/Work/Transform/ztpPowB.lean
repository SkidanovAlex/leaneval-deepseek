import Mathlib

namespace Work.Transform

theorem ztpPowB (B : ℕ) : 8 * B ^ 2 + 12 * B ≤ 2 ^ B * 100 ^ 2 := by
  -- For `n ≥ 2` we argue by induction; the step needs `8n² - 4n - 20 ≥ 0`.
  have h : ∀ n ≥ 2, 8 * n ^ 2 + 12 * n ≤ 2 ^ n * 100 ^ 2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have h1 : 8 * (m + 1) ^ 2 + 12 * (m + 1) ≤ 2 * (8 * m ^ 2 + 12 * m) := by
        nlinarith
      calc 8 * (m + 1) ^ 2 + 12 * (m + 1) ≤ 2 * (8 * m ^ 2 + 12 * m) := h1
        _ ≤ 2 * (2 ^ m * 100 ^ 2) := by omega
        _ = 2 ^ (m + 1) * 100 ^ 2 := by rw [pow_succ]; ring
  rcases B with _ | _ | B
  · norm_num
  · norm_num
  · exact h (B + 2) (by omega)

end Work.Transform
