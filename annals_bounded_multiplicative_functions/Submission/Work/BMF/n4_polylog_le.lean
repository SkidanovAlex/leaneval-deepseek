import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **Polylogarithms are eventually smaller than any positive power.**  For every `A : ℕ` and
`a > 0`, `(log P)^A ≤ P^a` for all large `P`.  (Taking logarithms, this is
`A log log P ≤ a log P`, which holds since `log log P = o(log P)`, e.g. from
`log x ≤ x^ε/ε` with `ε = a/(2A)`.)  Used to absorb the `(log P)^{O(1)}` factors and the
`ω(q) ≤ log₂ q ≤ O(log log P)` factors in the final numerical comparison for N4. -/
theorem n4_polylog_le (A : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → (Real.log P) ^ A ≤ P ^ a := by
  rcases Nat.eq_zero_or_pos A with hA | hA
  · -- `A = 0`: the left-hand side is the constant `1`, and `P^a ≥ 1` for `P ≥ 1`.
    subst hA
    exact ⟨1, le_refl 1, fun P hP => by simpa using Real.one_le_rpow hP ha.le⟩
  · -- `A ≥ 1`: `log x = o(x^r)` with `r = a/A`, so `log x ≤ x^r` for large `x`, and
    -- `(log x)^A ≤ (x^r)^A = x^(r*A) = x^a`.
    have hApos : (0 : ℝ) < A := by exact_mod_cast hA
    set r : ℝ := a / A with hr
    have hrpos : 0 < r := div_pos ha hApos
    obtain ⟨C, hC⟩ := Filter.eventually_atTop.mp
      ((isLittleO_log_rpow_atTop hrpos).bound (show (0 : ℝ) < 1 by norm_num))
    refine ⟨max 1 C, le_max_left _ _, ?_⟩
    intro P hP
    have hP1 : 1 ≤ P := le_trans (le_max_left _ _) hP
    have hPC : C ≤ P := le_trans (le_max_right _ _) hP
    have hPnonneg : 0 ≤ P := le_trans zero_le_one hP1
    have hb := hC P hPC
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at hb
    -- `hb : |log P| ≤ |P^r|`, and both sides are nonnegative, so `log P ≤ P^r`
    have hlog : Real.log P ≤ P ^ r := by
      have h1 : Real.log P = |Real.log P| := (abs_of_nonneg (Real.log_nonneg hP1)).symm
      have h2 : |P ^ r| = P ^ r := abs_of_nonneg (Real.rpow_nonneg hPnonneg r)
      linarith [hb, h1, h2]
    have hra : r * (A : ℝ) = a := by
      rw [hr, div_mul_cancel₀ a hApos.ne']
    calc (Real.log P) ^ A ≤ (P ^ r) ^ A :=
          pow_le_pow_left₀ (Real.log_nonneg hP1) hlog A
      _ = P ^ a := by
          rw [← Real.rpow_natCast (P ^ r) A, ← Real.rpow_mul hPnonneg r (A : ℝ), hra]

end Work.BMF
