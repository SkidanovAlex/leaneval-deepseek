import Mathlib
import Submission.Work.Holonomy3.defs

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-! ## Combinatorial preliminaries

The paper's display `(taub)` is a purely finite computation: for an array whose column `j` is `0`
in the first `u_j` rows and equal to `bj j` afterwards, the weighted sum
`Σ_i (2i+1)·σ_i` of the row sums `σ_i = Σ_j b_{i,j}` collapses to `Σ_j (m² - u_j²)·bj_j`.

The only arithmetic input is the classical `1 + 3 + ⋯ + (2n-1) = n²`, here in the form
`Σ_{i<n} (2i+1) = n²` (rows are indexed from `0`, so row `i` carries the weight `2i+1`). -/

/-- The sum of the odd numbers `1 + 3 + ⋯ + (2n-1)` equals `n²`. -/
private lemma sum_range_odd (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 * (i : ℝ) + 1)) = (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The tail form of `sum_range_odd`: for `u ≤ m`, the odd weights on the `m - u` rows
`u, u+1, …, m-1` sum to `m² - u²`. -/
private lemma sum_range_ite_odd (m u : ℕ) (hu : u ≤ m) :
    (∑ i ∈ Finset.range m, (if i < u then (0 : ℝ) else (2 * (i : ℝ) + 1)))
      = (m : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
  have hsplit : Finset.range m = Finset.range u ∪ Finset.Ico u m := by
    ext i; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range u) (Finset.Ico u m) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Ico] at hi'
    omega
  have hzero : (∑ i ∈ Finset.range u, (if i < u then (0 : ℝ) else (2 * (i : ℝ) + 1))) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [if_pos hi]
  have hico : (∑ i ∈ Finset.Ico u m, (if i < u then (0 : ℝ) else (2 * (i : ℝ) + 1)))
      = ∑ i ∈ Finset.Ico u m, (2 * (i : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [if_neg (by omega : ¬ i < u)]
  rw [hsplit, Finset.sum_union hdisj, hzero, zero_add, hico]
  have hfull : (∑ i ∈ Finset.range m, (2 * (i : ℝ) + 1)) = (m : ℝ) ^ 2 := sum_range_odd m
  have hfull' : (∑ i ∈ Finset.range u ∪ Finset.Ico u m, (2 * (i : ℝ) + 1)) = (m : ℝ) ^ 2 := by
    rw [← hsplit]; exact hfull
  rw [Finset.sum_union hdisj, sum_range_odd u] at hfull'
  linarith

/-- `sum_range_ite_odd` over `Fin m`: the weighted number of rows at which column entries are
nonzero is `m² - u²`. -/
private lemma sum_fin_ite_odd (m u : ℕ) (hu : u ≤ m) :
    (∑ i : Fin m, (if (i : ℕ) < u then (0 : ℝ) else (2 * (i : ℝ) + 1)))
      = (m : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < u then (0 : ℝ) else 2 * (i : ℝ) + 1)]
  exact sum_range_ite_odd m u hu

/-- **The paper's display `(taub)`.** If the array `b` has the paper's column shape — column `j`
equal to `0` in the first `u j` rows and to `bj j` afterwards, with `u j ≤ m` — then
`τ♭(b) = (1/m²)·Σ_j (m² - u_j²)·b_j`. (Equivalently `τ♭(b) = σ_m - (1/m²)·Σ_j u_j² b_j` as soon as
`bj j = 0` for the columns with `u j = m`, so that `τ♭(b) ∈ [0, σ_m]`.) -/
theorem tauFlat_eq_colShape {m r : ℕ} {b : Fin m → Fin r → ℕ} {u : Fin r → ℕ} {bj : Fin r → ℕ}
    (h : ∀ i j, b i j = if (i : ℕ) < u j then 0 else bj j) (hu : ∀ j, u j ≤ m) :
    Submission.CDTPlan.tauFlat b =
      (1 / (m : ℝ) ^ 2) * ∑ j, (((m : ℝ) ^ 2 - (u j : ℝ) ^ 2) * (bj j : ℝ)) := by
  rw [Submission.CDTPlan.tauFlat]
  congr 1
  calc ∑ i : Fin m, (2 * (i : ℝ) + 1) * (rowSum b i : ℝ)
      = ∑ i : Fin m, ∑ j : Fin r, (2 * (i : ℝ) + 1) * (b i j : ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [rowSum, Nat.cast_sum, Finset.mul_sum]
    _ = ∑ j : Fin r, ∑ i : Fin m, (2 * (i : ℝ) + 1) * (b i j : ℝ) := Finset.sum_comm
    _ = ∑ j : Fin r, ((m : ℝ) ^ 2 - (u j : ℝ) ^ 2) * (bj j : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hb' : ∀ i : Fin m, (b i j : ℝ) = if (i : ℕ) < u j then (0 : ℝ) else (bj j : ℝ) := by
          intro i
          rw [h i j]
          by_cases hc : (i : ℕ) < u j <;> simp [hc]
        calc ∑ i : Fin m, (2 * (i : ℝ) + 1) * (b i j : ℝ)
            = ∑ i : Fin m,
                (if (i : ℕ) < u j then (0 : ℝ) else (2 * (i : ℝ) + 1)) * (bj j : ℝ) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hb' i]
              by_cases hc : (i : ℕ) < u j <;> simp [hc]
          _ = (∑ i : Fin m,
                (if (i : ℕ) < u j then (0 : ℝ) else (2 * (i : ℝ) + 1))) * (bj j : ℝ) := by
              rw [Finset.sum_mul]
          _ = ((m : ℝ) ^ 2 - (u j : ℝ) ^ 2) * (bj j : ℝ) := by
              rw [sum_fin_ite_odd m (u j) (hu j)]

end Work.Holonomy3
