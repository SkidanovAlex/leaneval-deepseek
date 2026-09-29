import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open Filter

namespace Commons.Analysis.InfiniteSum

/-- absolute-convergence type summability of the weighted geometric series
`Σₙ nᵏ·Xⁿ` for real `‖X‖ < 1` (any `k : ℕ`). -/
lemma summable_nat_pow_mul_geom (k : ℕ) {X : ℝ} (hX : ‖X‖ < 1) :
    Summable fun n : ℕ => (n : ℝ) ^ k * X ^ n := by
  -- pick a radius q with ‖X‖ < q < 1; polynomial growth is o(q^n), and q^n
  -- is summable, so n^k·X^n is (absolutely) summable by comparison.
  let c : ℝ := ‖X‖
  let q : ℝ := (1 + c) / 2
  have hc0 : 0 ≤ c := norm_nonneg X
  have hc1 : c < 1 := hX
  have hXq : ‖X‖ < q := by
    change c < q
    dsimp [q]
    nlinarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    nlinarith
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith
  have hsumq : Summable fun n : ℕ => q ^ n := summable_geometric_of_lt_one hq0 hq1
  have hlittle :
      (fun n : ℕ => (n : ℝ) ^ k * X ^ n) =o[atTop] fun n : ℕ => q ^ n := by
    exact isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (R := ℝ) k hXq
  have hEv : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) ^ k * X ^ n‖ ≤ q ^ n := by
    refine hlittle.eventuallyLE.mono ?_
    intro n hn
    calc
      ‖(n : ℝ) ^ k * X ^ n‖ ≤ ‖q ^ n‖ := hn
      _ = q ^ n := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 n)]
  have hEvCof : ∀ᶠ n : ℕ in cofinite, ‖(n : ℝ) ^ k * X ^ n‖ ≤ q ^ n := by
    simpa [Nat.cofinite_eq_atTop] using hEv
  exact Summable.of_norm_bounded_eventually
    (f := fun n : ℕ => (n : ℝ) ^ k * X ^ n) (g := fun n : ℕ => q ^ n) hsumq hEvCof

end Commons.Analysis.InfiniteSum

end