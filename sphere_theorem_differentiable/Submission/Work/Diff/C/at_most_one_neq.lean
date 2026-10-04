import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

/-- If `∑ βᵢ² = 1` and `cos α > 0` with `cos²α > 1/2`, then at most one index can have
`βᵢ ≤ -cos α`; and if `βᵢ ≤ -cos α` then every other `βⱼ` satisfies `|βⱼ| ≤ sin α`. -/
lemma at_most_one_neq {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → ℝ} (hsum : ∑ i, β i ^ 2 = 1)
    {α : ℝ} (hcos_sq : 1 / 2 < Real.cos α ^ 2) (hcos_nn : 0 ≤ Real.cos α)
    (hsin_nn : 0 ≤ Real.sin α) :
    (∀ i j, i ≠ j → β i ≤ -Real.cos α → β j ≤ -Real.cos α → False) ∧
    (∀ i j, i ≠ j → β i ≤ -Real.cos α → |β j| ≤ Real.sin α) := by
  have hcos_pos : 0 < Real.cos α := by nlinarith [sq_nonneg (Real.cos α)]
  have hsin_sq : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by linarith [Real.sin_sq_add_cos_sq α]
  -- the sum of the squares of two distinct coordinates is at most the total sum
  have hpair : ∀ i j, i ≠ j → β i ^ 2 + β j ^ 2 ≤ ∑ k, β k ^ 2 := by
    intro i j hij
    have h := Finset.sum_add_sum_compl ({i, j} : Finset ι) (fun k => β k ^ 2)
    rw [Finset.sum_pair hij] at h
    have hnn : 0 ≤ ∑ k ∈ ({i, j} : Finset ι)ᶜ, β k ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg (β k))
    linarith [h]
  -- `β i ≤ -cos α` forces `cos α ^ 2 ≤ β i ^ 2`
  have hsq_ge : ∀ i, β i ≤ -Real.cos α → Real.cos α ^ 2 ≤ β i ^ 2 := by
    intro i hi
    have hbi_neg : β i < 0 := by linarith
    have habs : |Real.cos α| ≤ |β i| := by
      rw [abs_of_nonneg (le_of_lt hcos_pos), abs_of_neg hbi_neg]
      linarith
    exact sq_le_sq.mpr habs
  constructor
  · intro i j hij hi hj
    have h1 := hsq_ge i hi
    have h2 := hsq_ge j hj
    have hp := hpair i j hij
    rw [hsum] at hp
    linarith
  · intro i j hij hi
    have h1 := hsq_ge i hi
    have hp := hpair i j hij
    rw [hsum] at hp
    have hbj2 : β j ^ 2 ≤ Real.sin α ^ 2 := by rw [hsin_sq]; linarith
    have hle : |β j| ≤ |Real.sin α| := sq_le_sq.mp hbj2
    rwa [abs_of_nonneg hsin_nn] at hle

end Work.Diff.C
