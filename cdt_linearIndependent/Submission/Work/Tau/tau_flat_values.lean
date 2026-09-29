import Mathlib
import Submission.Work.Tau.defs

/-!
# Area Tau: the flat summands `τ♭(bC) = 1136/289`, `τ♭(bA) = 191/49`

`τ♭(b) = (1/m²) Σ_{i<m} (2i+1) σ_i` where `σ_i = Σ_j b i j` is the `i`-th row sum
(0-indexed, so row `i` carries weight `2i+1`).  For the arrays `bC` (`m = 17`) and `bA`
(`m = 14`) the row sums are `σ_0 = 0`, `σ_1 = σ_2 = 2`, `σ_i = 4` for `i ≥ 3`; hence

* `τ♭(bC) = (1·0 + 3·2 + 5·2 + 4·(1+3+…+33 − 9)) / 17² = 1136/289`,
* `τ♭(bA) = (1·0 + 3·2 + 5·2 + 4·(1+3+…+27 − 9)) / 14² = 764/196 = 191/49`.

This file evaluates the two finite sums exactly: the numerators are computed as natural
numbers by kernel `decide`, then pushed into `ℝ`.
-/

namespace Work.Tau

open Submission.CDTPlan

/-- Numerator of `τ♭ bC`, as a natural number. -/
theorem bC_tauFlat_num :
    (∑ i : Fin 17, (2 * (i : ℕ) + 1) * rowSum bC i) = 1136 := by decide

/-- Numerator of `τ♭ bA`, as a natural number. -/
theorem bA_tauFlat_num :
    (∑ i : Fin 14, (2 * (i : ℕ) + 1) * rowSum bA i) = 764 := by decide

/-- `τ♭` of an array, with the sum of rationals written over a single natural numerator. -/
private theorem tauFlat_eq_nat {m r : ℕ} (b : Fin m → Fin r → ℕ) :
    tauFlat b = (1 / (m : ℝ) ^ 2) *
      ((∑ i : Fin m, (2 * (i : ℕ) + 1) * rowSum b i : ℕ) : ℝ) := by
  rw [tauFlat]
  simp only [Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem tau_flat_values : Submission.CDTPlan.tauFlat Submission.CDTPlan.bC = 1136 / 289 ∧ Submission.CDTPlan.tauFlat Submission.CDTPlan.bA = 191 / 49 := by
  rw [tauFlat_eq_nat bC, tauFlat_eq_nat bA, bC_tauFlat_num, bA_tauFlat_num]
  norm_num

end Work.Tau
