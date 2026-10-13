import Mathlib
import Submission.Work.WilC4.rpow_bounded_exponent_zero

namespace Work.WilC4

/-- **The exponent of a power-asymptotic is determined.**

If a set `Y ⊆ ℝ²` has points with arbitrarily large first coordinate and, near `+∞`, the
second coordinate of every point is pinched between `C⁻¹ x^σ` and `C x^σ` for some constant
`C ≥ 1`, while the ratio `y / x^q` converges to a **nonzero** limit `a`, then necessarily
`σ = q`.

Indeed, for large `x` on which a point exists, `x^(σ-q) = x^σ / x^q` is trapped in the
*positive* window `[|a|/(2C), 3C|a|/2]` (the upper bound `x^σ` bounds `x^(σ-q)` from below via
`|a|/2 ≤ |y|/x^q ≤ C x^(σ-q)`, the lower bound `C⁻¹ x^σ` bounds it from above via
`C⁻¹ x^(σ-q) ≤ |y|/x^q ≤ 3|a|/2`), and a positive real power is unbounded for a positive
exponent and tends to `0` for a negative one. -/
theorem pb_exponent_asymptotic {Y : Set (Fin 2 → ℝ)}
    (hdom : ∀ R : ℝ, ∃ x y : ℝ, R ≤ x ∧ ![x, y] ∈ Y)
    (σ C : ℝ) (hC : 1 ≤ C)
    (hσ : ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y →
      C⁻¹ * x ^ σ ≤ |y| ∧ |y| ≤ C * x ^ σ)
    {q : ℚ} {a : ℝ} (ha : a ≠ 0)
    (hasym : ∀ ε > (0 : ℝ), ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y →
      |y / x ^ (q : ℝ) - a| < ε) :
    σ = q := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCne : C ≠ 0 := hCpos.ne'
  have haabs : 0 < |a| := abs_pos.mpr ha
  obtain ⟨Rσ, hRσ⟩ := hσ
  obtain ⟨Ra, hRa⟩ := hasym (|a| / 2) (half_pos haabs)
  -- For every `R` there is a point `(x,y) ∈ Y` with `x ≥ R` on which `x^(σ-q)` is trapped.
  have hkey : ∀ R : ℝ, ∃ x : ℝ, R ≤ x ∧ |a| / (2 * C) ≤ x ^ (σ - (q : ℝ)) ∧
      x ^ (σ - (q : ℝ)) ≤ 3 * C * |a| / 2 := by
    intro R
    obtain ⟨x, y, hx, hmem⟩ := hdom (max (max Rσ Ra) (max R 1))
    have hxRσ : Rσ ≤ x := le_trans (le_trans (le_max_left Rσ Ra) (le_max_left _ _)) hx
    have hxRa : Ra ≤ x := le_trans (le_trans (le_max_right Rσ Ra) (le_max_left _ _)) hx
    have hxR : R ≤ x := le_trans (le_trans (le_max_left R 1) (le_max_right _ _)) hx
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_trans (le_max_right R 1) (le_max_right _ _)) hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hxq : 0 < x ^ (q : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hbnd := hRσ x y hxRσ hmem
    have hasy := hRa x y hxRa hmem
    have habs : |y / x ^ (q : ℝ)| = |y| / x ^ (q : ℝ) := by rw [abs_div, abs_of_pos hxq]
    have hlt := abs_lt.mp hasy
    -- `|a|/2 < |y|/x^q < 3|a|/2`
    have hlo : |a| / 2 < |y| / x ^ (q : ℝ) := by
      have h := abs_sub_abs_le_abs_sub a (y / x ^ (q : ℝ))
      rw [abs_sub_comm, habs] at h
      linarith [h, hlt.1]
    have hhi : |y| / x ^ (q : ℝ) < 3 * |a| / 2 := by
      have h := abs_sub_abs_le_abs_sub (y / x ^ (q : ℝ)) a
      rw [habs] at h
      linarith [h, hlt.2]
    refine ⟨x, hxR, ?_, ?_⟩
    · -- lower bound on `x^(σ-q)`, from `|y| ≤ C x^σ`
      have e1 : |y| / x ^ (q : ℝ) ≤ C * x ^ (σ - (q : ℝ)) := by
        have h := div_le_div_of_nonneg_right hbnd.2 hxq.le
        rw [mul_div_assoc, ← Real.rpow_sub hx0] at h
        exact h
      have h3 : |a| / 2 < C * x ^ (σ - (q : ℝ)) := lt_of_lt_of_le hlo e1
      have hstrict : |a| / (2 * C) < x ^ (σ - (q : ℝ)) := by
        rw [div_lt_iff₀ (show (0 : ℝ) < 2 * C by positivity)]
        nlinarith [h3]
      exact le_of_lt hstrict
    · -- upper bound on `x^(σ-q)`, from `C⁻¹ x^σ ≤ |y|`
      have e1 : C⁻¹ * x ^ (σ - (q : ℝ)) ≤ |y| / x ^ (q : ℝ) := by
        have h := div_le_div_of_nonneg_right hbnd.1 hxq.le
        rw [mul_div_assoc, ← Real.rpow_sub hx0] at h
        exact h
      have h3 : C⁻¹ * x ^ (σ - (q : ℝ)) < 3 * |a| / 2 := lt_of_le_of_lt e1 hhi
      have h4 : C * (C⁻¹ * x ^ (σ - (q : ℝ))) < C * (3 * |a| / 2) :=
        mul_lt_mul_of_pos_left h3 hCpos
      have h5 : C * (C⁻¹ * x ^ (σ - (q : ℝ))) = x ^ (σ - (q : ℝ)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hCne, one_mul]
      rw [h5] at h4
      linarith [h4]
  -- `x^(σ-q)` is trapped in a positive window along arbitrarily large `x`, so `σ - q = 0`.
  have hd0 : σ - (q : ℝ) = 0 := rpow_bounded_exponent_zero (div_pos haabs (by positivity)) hkey
  linarith

end Work.WilC4
