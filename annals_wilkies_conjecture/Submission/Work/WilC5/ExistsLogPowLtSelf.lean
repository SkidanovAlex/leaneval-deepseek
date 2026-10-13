import Mathlib

namespace Work.WilC5

/-- For every exponent `k`, the power of the logarithm grows slower than the identity:
beyond some bound `N`, `(log x)^k < x`. -/
theorem ExistsLogPowLtSelf (k : ℕ) :
    ∃ N : ℕ, ∀ x : ℝ, (N : ℝ) < x → (Real.log x) ^ k < x := by
  have h : (fun x : ℝ => Real.log x ^ k) =o[Filter.atTop] id := Real.isLittleO_pow_log_id_atTop
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x ^ k‖ ≤ (1 / 2 : ℝ) * ‖x‖ :=
    h.bound (by norm_num)
  rw [Filter.eventually_atTop] at h1
  obtain ⟨a, ha⟩ := h1
  refine ⟨⌈a⌉₊, fun x hx => ?_⟩
  have hax : a ≤ x := le_trans (Nat.le_ceil a) (le_of_lt hx)
  have h2 := ha x hax
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h2
  have hxpos : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg _) hx
  have h3 : Real.log x ^ k ≤ (1 / 2 : ℝ) * x := by
    have := le_of_abs_le h2
    rwa [abs_of_pos hxpos] at this
  linarith

end Work.WilC5
