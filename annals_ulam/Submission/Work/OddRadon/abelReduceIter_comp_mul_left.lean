import Mathlib
import Submission.Work.OddRadon.Abel

/-!
# Scaling of the iterated Abel reductions

`abelReduce α F c = deriv F c / (2 α c)` is invariant under the dilation
`c ↦ b * c` up to the factor `b²`: for `b ≠ 0`

  `abelReduce α (fun t => Φ (b * t)) c = b² * abelReduce α Φ (b * c)`,

because `(Φ ∘ (b·))'(c) = b Φ'(b c)` and `b² / (b c) = b / c`.  Since the recursion
`abelReduceIter α (k+1) F = abelReduceIter (α-1) k (abelReduce α F)` only changes the
exponent, the factor `b²` is picked up at every one of the `k` steps, giving the statement
below: the `k`-fold reduction of the dilated datum at `y` is `b ^ (2k)` times the `k`-fold
reduction of the datum at `b * y`.

This is the input-data scaling rule used to relate `radonInverse` of a dilated profile to
`radonInverse` of the profile (`radonInverse_comp_mul_left`).
-/

noncomputable section

namespace Work.OddRadon

/-- One exponent-reduction step, with a constant factor, under the dilation `c ↦ b * c`. -/
private lemma abelReduce_comp_mul_left {Ψ : ℝ → ℝ} {b : ℝ} (hb : b ≠ 0) (C β : ℝ) :
    abelReduce β (fun c => C * Ψ (b * c)) =
      fun c => C * b ^ 2 * abelReduce β Ψ (b * c) := by
  funext c
  simp only [abelReduce, deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul]
  field_simp

/-- The general scaling rule for the iterated reductions: a constant factor `C` in front of a
dilated datum gains a factor `b ^ (2 * k)` after `k` reductions. -/
private lemma abelReduceIter_comp_mul_left_aux {b : ℝ} (hb : b ≠ 0) :
    ∀ (k : ℕ) (β : ℝ) (C : ℝ) (Ψ : ℝ → ℝ),
      abelReduceIter β k (fun c => C * Ψ (b * c)) =
        fun y => C * b ^ (2 * k) * abelReduceIter β k Ψ (b * y) := by
  intro k
  induction k with
  | zero =>
      intro β C Ψ
      funext y
      simp [abelReduceIter]
  | succ k ih =>
      intro β C Ψ
      rw [abelReduceIter_succ, abelReduceIter_succ]
      rw [abelReduce_comp_mul_left hb C β]
      rw [ih (β - 1) (C * b ^ 2) (abelReduce β Ψ)]
      funext y
      have hp : b ^ (2 * (k + 1)) = b ^ 2 * b ^ (2 * k) := by
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; ring
      simp only [hp]
      ring

theorem abelReduceIter_comp_mul_left {Φ : ℝ → ℝ} {b y : ℝ} (hb : b ≠ 0) {k : ℕ} {α : ℝ} :
    abelReduceIter α k (fun t : ℝ => Φ (b * t)) y =
      b ^ (2 * k) * abelReduceIter α k Φ (b * y) := by
  have h := congrFun (abelReduceIter_comp_mul_left_aux hb k α 1 Φ) y
  simpa using h

end Work.OddRadon
