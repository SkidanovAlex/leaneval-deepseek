import Mathlib
import Submission.Work.Holonomy3.defs

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-- Weighted-sum bound: the rows of a `Fin m`-indexed array carry weights `2i+1 ≤ 2m²`
(as `i < m` and `m ≥ 1`), so the weighted total of the row sums is at most `2m²` times the
unweighted total. Dividing by `m²` gives `τ♭ ≤ 2·Σσ`. -/
theorem tauFlat_le_two_sum {m r : ℕ} (hm : 0 < m) (b : Fin m → Fin r → ℕ) :
    Submission.CDTPlan.tauFlat b ≤ 2 * (∑ i : Fin m, (Submission.CDTPlan.rowSum b i : ℝ)) := by
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  rw [Submission.CDTPlan.tauFlat]
  set S := ∑ i : Fin m, (2 * (i : ℝ) + 1) * (Submission.CDTPlan.rowSum b i : ℝ) with hSdef
  set T := ∑ i : Fin m, (Submission.CDTPlan.rowSum b i : ℝ) with hTdef
  have hS : S ≤ (m:ℝ)^2 * (2 * T) := by
    have hterm : ∀ i : Fin m, (2*(i:ℝ)+1) * (Submission.CDTPlan.rowSum b i : ℝ)
        ≤ (2*(m:ℝ)^2) * (Submission.CDTPlan.rowSum b i : ℝ) := by
      intro i
      have hσ : (0:ℝ) ≤ (Submission.CDTPlan.rowSum b i : ℝ) := by positivity
      have hn : 2 * (i:ℕ) + 2 ≤ 2 * m := by have := i.isLt; omega
      have hnR : 2 * (i:ℝ) + 2 ≤ 2 * (m:ℝ) := by exact_mod_cast hn
      have hle : (2*(i:ℝ)+1) ≤ 2*(m:ℝ)^2 := by
        nlinarith [hmR, hnR, sq_nonneg ((m:ℝ)), sq_nonneg ((m:ℝ) - 1)]
      exact mul_le_mul_of_nonneg_right hle hσ
    calc S = ∑ i : Fin m, (2 * (i : ℝ) + 1) * (Submission.CDTPlan.rowSum b i : ℝ) := rfl
      _ ≤ ∑ i : Fin m, (2*(m:ℝ)^2) * (Submission.CDTPlan.rowSum b i : ℝ) :=
            Finset.sum_le_sum fun i _ => hterm i
      _ = (2*(m:ℝ)^2) * T := by rw [Finset.mul_sum]
      _ = (m:ℝ)^2 * (2 * T) := by ring
  have h1 : (1/(m:ℝ)^2) * S ≤ (1/(m:ℝ)^2) * ((m:ℝ)^2 * (2*T)) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have h2 : (1/(m:ℝ)^2) * ((m:ℝ)^2 * (2*T)) = 2*T := by
    field_simp
  linarith

end Work.Holonomy3
