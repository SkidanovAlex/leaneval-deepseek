import Mathlib

namespace Work.CPull

/-- If `∑ ‖aₙ‖ n sⁿ` converges with `s > 0`, then at every `w` with `‖w‖ < s` the
termwise-differentiated power series `∑ (n+1) aₙ₊₁ wⁿ` is absolutely summable. -/
theorem summable_deriv_powSeries_of_majorant {a : ℕ → ℂ} {s : ℝ} (hs : 0 < s)
    (hsum : Summable (fun n : ℕ => ‖a n‖ * n * s ^ n)) (w : ℂ) (hw : ‖w‖ < s) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * a (n + 1) * w ^ n) := by
  -- The shifted majorant `∑ ‖aₙ₊₁‖ (n+1) sⁿ` is summable: it is `1/s` times the
  -- tail of `∑ ‖aₙ‖ n sⁿ`, obtained by reindexing along `Nat.succ`.
  have hM : Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) * s ^ n) := by
    have h2 : Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) * s ^ (n + 1)) := by
      have h := hsum.comp_injective Nat.succ_injective
      exact h
    have h3 := h2.const_smul (s⁻¹)
    refine h3.congr ?_
    intro n
    simp only [smul_eq_mul]
    field_simp
    ring
  -- Bound the norms of the differentiated terms by the majorant and compare.
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le
    (g := fun n => ‖((n + 1 : ℕ) : ℂ) * a (n + 1) * w ^ n‖)
    (f := fun n => ‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) * s ^ n) ?_ ?_ hM
  · intro n; positivity
  · intro n
    have hwn : ‖w‖ ^ n ≤ s ^ n := pow_le_pow_left₀ (norm_nonneg w) (le_of_lt hw) n
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have hcast : ‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) * s ^ n
        = (↑(n + 1) * ‖a (n + 1)‖) * s ^ n := by ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_left hwn (by positivity)

end Work.CPull
