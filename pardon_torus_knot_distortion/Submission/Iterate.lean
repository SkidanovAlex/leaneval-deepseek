import Mathlib

/-!
# An abstract "shrinking invariant" contradiction

This is the combinatorial core of Pardon's proof: if a property `P` holds at scale
`ρ₀` (thought of as the radius of a large ball), is preserved by shrinking the
scale by a fixed factor `c` with `0 < c < 1` (each sweep-and-cut step produces a
strictly smaller ball), and can only hold at scales bounded below by `ρ_min > 0`
(the extrinsic systole of the embedded torus), then the three assumptions are
inconsistent.
-/

namespace Submission

/-- **Shrinking invariant contradiction.**  There is no property `P` of positive
scales which holds at `ρ₀ > 0`, is preserved under multiplication of the scale by
a fixed `c ∈ (0,1)`, and implies the lower bound `ρ_min > 0` on the scale. -/
theorem shrink_contradiction (P : ℝ → Prop) (ρ₀ c ρmin : ℝ) (hρ₀ : 0 < ρ₀)
    (hc : 0 < c) (hc1 : c < 1) (hmin : 0 < ρmin)
    (hstart : P ρ₀)
    (hshrink : ∀ ρ, 0 < ρ → P ρ → P (c * ρ))
    (hlower : ∀ ρ, 0 < ρ → P ρ → ρmin ≤ ρ) : False := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ρmin / ρ₀) (y := c) (by positivity) hc1
  have hPall : ∀ k : ℕ, P (c ^ k * ρ₀) := by
    intro k
    induction k with
    | zero => simpa using hstart
    | succ j ih =>
        have hpos : 0 < c ^ j * ρ₀ := mul_pos (pow_pos hc j) hρ₀
        have := hshrink (c ^ j * ρ₀) hpos ih
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using this
  have hP : P (c ^ n * ρ₀) := hPall n
  have hlt : c ^ n * ρ₀ < ρmin := by
    have := mul_lt_mul_of_pos_right hn hρ₀
    rwa [div_mul_cancel₀ _ (ne_of_gt hρ₀)] at this
  exact absurd (hlower _ (mul_pos (pow_pos hc n) hρ₀) hP) (not_le.mpr hlt)

end Submission
