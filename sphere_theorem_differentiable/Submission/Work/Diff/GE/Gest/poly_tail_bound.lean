import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.Gest

/-- For `a > 0`, the cubic-minus-quartic `P * s^3 - a * s^4` is bounded above by the
explicit constant `27 * P^4 / (256 * a^3)`.  Equivalently, after multiplying by the
positive denominator `256 * a^3`, the claim is that
`27 * P^4 + 256 * a^4 * s^4 - 256 * a^3 * P * s^3 ≥ 0`,
which is the sum-of-squares identity
`(4*a*s - 3*P)^2 * ((4*a*s + P)^2 + 2*P^2) ≥ 0`. -/
lemma quartic_cubic_bound (a P s : ℝ) (ha : 0 < a) :
    P * s ^ 3 - a * s ^ 4 ≤ 27 * P ^ 4 / (256 * a ^ 3) := by
  have ha3 : (0 : ℝ) < 256 * a ^ 3 := by positivity
  rw [le_div_iff₀ ha3]
  have h1 : 0 ≤ (4 * a * s - 3 * P) ^ 2 * ((4 * a * s + P) ^ 2 + 2 * P ^ 2) := by
    apply mul_nonneg (sq_nonneg _); positivity
  have hid : (4 * a * s - 3 * P) ^ 2 * ((4 * a * s + P) ^ 2 + 2 * P ^ 2)
      = 27 * P ^ 4 + 256 * a ^ 4 * s ^ 4 - 256 * a ^ 3 * P * s ^ 3 := by ring
  nlinarith [h1, hid]

theorem poly_tail_bound (a b M : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 ≤ σ → b * σ ^ 3 + M * σ ^ 2 - a * σ ^ 4 ≤ C := by
  refine ⟨27 * (b + M) ^ 4 / (256 * a ^ 3), ?_, ?_⟩
  · have hbM : 0 ≤ b + M := add_nonneg hb hM
    positivity
  · intro σ hσ
    -- For `σ ≥ 1`, `M * σ^2 ≤ M * σ^3`, so the cubic terms combine
    -- into `(b + M) * σ^3`, which is the shape handled by `quartic_cubic_bound`.
    have hMs : M * σ ^ 2 ≤ M * σ ^ 3 := by
      have h23 : σ ^ 2 ≤ σ ^ 3 := pow_le_pow_right₀ hσ (by norm_num : (2 : ℕ) ≤ 3)
      exact mul_le_mul_of_nonneg_left h23 hM
    have h1 : b * σ ^ 3 + M * σ ^ 2 - a * σ ^ 4 ≤ (b + M) * σ ^ 3 - a * σ ^ 4 := by
      linarith only [hMs]
    have h2 : (b + M) * σ ^ 3 - a * σ ^ 4
        ≤ 27 * (b + M) ^ 4 / (256 * a ^ 3) := quartic_cubic_bound a (b + M) σ ha
    linarith only [h1, h2]

end Work.Diff.GE.Gest
