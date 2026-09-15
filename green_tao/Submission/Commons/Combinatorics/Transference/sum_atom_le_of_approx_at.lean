import Mathlib
import Submission.Commons.Combinatorics.Transference.abs_prod_sub_prod_le_sum_abs_sub

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

set_option linter.unusedVariables false

/-- Corrected (and applicable) form of `sum_atom_le_of_approx`: the `(ν+1)`-weighted
approximation hypothesis is only needed at the atom under consideration, rather than for
every atom simultaneously.  If each atom `P j x` is approximated by the `[0,1]`-valued
`Ψ j` up to `η` and `|∑_y (ν y - 1) ∏_j Ψ j y| ≤ δ`, then for the atom of the join,
`|∑_{y : ∀ j, y ∈ P j x} (ν y - 1)| ≤ δ + K η`. -/
theorem sum_atom_le_of_approx_at {X : Type*} [Fintype X] [DecidableEq X] {K : ℕ}
    (P : Fin K → X → Finset X) (Ψ : Fin K → X → ℝ) (ν : X → ℝ) {η δ : ℝ}
    (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hν : ∀ x, 0 ≤ ν x)
    (hΨ0 : ∀ j x, 0 ≤ Ψ j x) (hΨ1 : ∀ j x, Ψ j x ≤ 1) (x : X)
    (happrox : ∀ j, ∑ y, (ν y + 1) * |(if y ∈ P j x then (1 : ℝ) else 0) - Ψ j y| ≤ η)
    (hcorr : |∑ y, (ν y - 1) * ∏ j, Ψ j y| ≤ δ) :
    |∑ y ∈ Finset.univ.filter (fun y => ∀ j, y ∈ P j x), (ν y - 1)| ≤ δ + K * η := by
  classical
  set U : ℝ := ∑ y, (ν y - 1) * ∏ j, (if y ∈ P j x then (1 : ℝ) else 0) with hUdef
  set T : ℝ := ∑ y, (ν y - 1) * ∏ j, Ψ j y with hTdef
  have hSU : ∑ y ∈ Finset.univ.filter (fun y => ∀ j, y ∈ P j x), (ν y - 1) = U := by
    rw [hUdef, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.prod_boole]
    by_cases hc : (∀ j, y ∈ P j x)
    · simp [hc]
    · simp [hc]
  rw [hSU]
  have hTbound : |T| ≤ δ := by
    rw [hTdef]; exact hcorr
  have hUTbound : |U - T| ≤ K * η := by
    have hUT : U - T
        = ∑ y, (ν y - 1) * ((∏ j, (if y ∈ P j x then (1 : ℝ) else 0)) - ∏ j, Ψ j y) := by
      rw [hUdef, hTdef, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    rw [hUT]
    calc |∑ y, (ν y - 1) * ((∏ j, (if y ∈ P j x then (1 : ℝ) else 0)) - ∏ j, Ψ j y)|
        ≤ ∑ y, |(ν y - 1) * ((∏ j, (if y ∈ P j x then (1 : ℝ) else 0)) - ∏ j, Ψ j y)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, |ν y - 1| * |(∏ j, (if y ∈ P j x then (1 : ℝ) else 0)) - ∏ j, Ψ j y| := by
            apply Finset.sum_congr rfl; intro y hy; rw [abs_mul]
      _ ≤ ∑ y, (ν y + 1) * ∑ j, |(if y ∈ P j x then (1 : ℝ) else 0) - Ψ j y| := by
            apply Finset.sum_le_sum
            intro y hy
            have hb : |(∏ j, (if y ∈ P j x then (1 : ℝ) else 0)) - ∏ j, Ψ j y|
                ≤ ∑ j, |(if y ∈ P j x then (1 : ℝ) else 0) - Ψ j y| :=
              abs_prod_sub_prod_le_sum_abs_sub Finset.univ
                (fun j => if y ∈ P j x then (1 : ℝ) else 0) (fun j => Ψ j y)
                (fun j _ => by split_ifs <;> norm_num)
                (fun j _ => by split_ifs <;> norm_num)
                (fun j _ => hΨ0 j y) (fun j _ => hΨ1 j y)
            have hνy : |ν y - 1| ≤ ν y + 1 := by
              rw [abs_le]; constructor <;> linarith [hν y]
            exact mul_le_mul hνy hb (abs_nonneg _) (by linarith [hν y])
      _ = ∑ j, ∑ y, (ν y + 1) * |(if y ∈ P j x then (1 : ℝ) else 0) - Ψ j y| := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
      _ ≤ ∑ _j : Fin K, η := by
            apply Finset.sum_le_sum; intro j hj; exact happrox j
      _ = K * η := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : |U| ≤ |U - T| + |T| := by
    calc |U| = |(U - T) + T| := by congr 1; ring
      _ ≤ |U - T| + |T| := abs_add_le _ _
  calc |U| ≤ |U - T| + |T| := h1
    _ ≤ K * η + δ := by linarith
    _ = δ + K * η := by ring

end Commons.Combinatorics.Transference
