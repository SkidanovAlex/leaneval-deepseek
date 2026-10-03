import Mathlib
import Submission.Work.Analysis.Probability.jumpCount

/-!
# The greedy `δ`-jump chain of a path

For a path `x : ℕ → ℝ` and a level `δ > 0` we define

* `nextJump x δ a` : the first time `n > a` with `δ < |x n - x a|` (`⊤` if there is none);
* `greedyTime x δ k` : the `k`-th greedy `δ`-jump time (`greedyTime x δ 0 = 0`, and
  `greedyTime x δ (k+1) = nextJump x δ (greedyTime x δ k)`, which is `⊤` once the chain stops);
* `greedyJumps x δ` : the number of greedy jumps, i.e. the number of `k ≥ 1` with
  `greedyTime x δ k < ⊤`, as an `ℝ≥0∞` (the supremum of those `k`).

These are the paths-level objects used to dominate `Kpath`: if `2δ ≤ λ` then a `λ`-oscillation
chain visits the blocks `[greedyTime x δ k, greedyTime x δ (k+1))` at most once per block, and
inside a block the path varies by at most `2δ ≤ λ`.

The definitions are stated for a bare path; applied to `fun n => F n ω` they give the greedy
jump times of the process `F`, which are stopping times when `F` is adapted.
-/

open scoped ENNReal BigOperators

namespace Work.Analysis.Probability

/-- The first time after `a` at which the path `x` is more than `δ` away from `x a`
(`⊤` if there is no such time). -/
noncomputable def nextJump (x : ℕ → ℝ) (δ : ℝ) (a : ℕ) : ℕ∞ := by
  classical
  exact if h : ∃ n : ℕ, a < n ∧ δ < |x n - x a| then (Nat.find h : ℕ) else ⊤

/-- The greedy `δ`-jump times of a path. -/
noncomputable def greedyTime (x : ℕ → ℝ) (δ : ℝ) : ℕ → ℕ∞
  | 0 => 0
  | (k + 1) =>
      if (greedyTime x δ k) < ⊤ then nextJump x δ ((greedyTime x δ k).toNat) else ⊤

/-- The number of greedy `δ`-jumps of a path, as an `ℝ≥0∞`. -/
noncomputable def greedyJumps (x : ℕ → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ (k : ℕ) (_ : greedyTime x δ (k + 1) < ⊤), ((k + 1 : ℕ) : ℝ≥0∞)

end Work.Analysis.Probability
