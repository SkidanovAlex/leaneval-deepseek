import Mathlib.Analysis.SpecificLimits.Basic

namespace Commons.Analysis.InfiniteSum

/-- If `|u n| ≤ C * ρ ^ n` for all `n`, with `C ≥ 0`, `ρ ≥ 0` and `ρ * |x| < 1`,
then the series `∑ |u n * x ^ n|` converges (absolutely). -/
lemma powSeries_abs_summable_of_geom_bound {u : ℕ → ℝ} {C ρ x : ℝ}
    (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hu : ∀ n : ℕ, |u n| ≤ C * ρ ^ n) (hxρ : ρ * |x| < 1) :
    Summable fun n : ℕ => |u n * x ^ n| := by
  have hb : ∀ n : ℕ, |u n * x ^ n| ≤ C * (ρ * |x|) ^ n := by
    intro n
    calc
      |u n * x ^ n| = |u n| * |x ^ n| := by rw [abs_mul]
      _ = |u n| * |x| ^ n := by rw [abs_pow]
      _ ≤ (C * ρ ^ n) * |x| ^ n :=
        mul_le_mul_of_nonneg_right (hu n) (pow_nonneg (abs_nonneg x) n)
      _ = C * (ρ ^ n * |x| ^ n) := by rw [mul_assoc]
      _ = C * (ρ * |x|) ^ n := by rw [mul_pow]
  -- The comparison series has nonnegative terms (as `C ≥ 0` and `ρ * |x| ≥ 0`),
  -- and it is summable as a geometric series with ratio `< 1`.
  have hCρx : ∀ n : ℕ, 0 ≤ C * (ρ * |x|) ^ n := fun n =>
    mul_nonneg hC (pow_nonneg (mul_nonneg hρ (abs_nonneg x)) n)
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hb
    ((summable_geometric_of_lt_one (mul_nonneg hρ (abs_nonneg x)) hxρ).mul_left C)