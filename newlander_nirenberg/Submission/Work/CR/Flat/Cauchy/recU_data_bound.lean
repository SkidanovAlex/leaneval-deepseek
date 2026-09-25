import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open Set

/-- Step 0 of the estimate for the recursion `recU`: the data bounds on `trackSet`.

Writing `H j := holderNorm 0 α (f j) (polydisc 0 1)` and `S := ∑ i, (H i).toReal`,
the hypothesis `hS` that `∑ i, H i ≠ ⊤` gives `H j ≠ ⊤` for every `j`; then on the
tracked region `trackSet ⊆ polydisc 0 1` the values `f j` are bounded by `S` and are
`S`-Hölder with exponent `α`. -/
theorem recU_data_bound {n : ℕ} {α : ℝ} (hα : 0 < α)
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hS : (∑ i, holderNorm 0 α (f i) (polydisc 0 (fun _ => 1))) ≠ ⊤) :
    0 ≤ (∑ i, (holderNorm 0 α (f i) (polydisc 0 (fun _ => 1))).toReal) ∧
    (∀ j z, z ∈ trackSet → ‖f j z‖ ≤ ∑ i, (holderNorm 0 α (f i) (polydisc 0 (fun _ => 1))).toReal) ∧
    (∀ j x y, x ∈ trackSet → y ∈ trackSet →
      ‖f j x - f j y‖ ≤ (∑ i, (holderNorm 0 α (f i) (polydisc 0 (fun _ => 1))).toReal) * ‖x - y‖ ^ α) := by
  -- Abbreviate the individual norms.
  let H : Fin n → ℝ≥0∞ := fun i => holderNorm 0 α (f i) (polydisc 0 (fun _ => 1))
  change 0 ≤ (∑ i, (H i).toReal) ∧
    (∀ j z, z ∈ trackSet → ‖f j z‖ ≤ ∑ i, (H i).toReal) ∧
    (∀ j x y, x ∈ trackSet → y ∈ trackSet →
      ‖f j x - f j y‖ ≤ (∑ i, (H i).toReal) * ‖x - y‖ ^ α)
  -- Each `H j` is at most the sum, hence finite because the sum is finite.
  have hsingle : ∀ j, H j ≤ ∑ i, H i := fun j =>
    Finset.single_le_sum (f := H) (fun i _ => bot_le) (Finset.mem_univ j)
  have hne : ∀ j, H j ≠ ⊤ := by
    intro j hj
    have hle := hsingle j
    rw [hj] at hle
    exact hS (top_le_iff.mp hle)
  -- `toReal` of the sum is the sum of the `toReal`s.
  have htoReal_sum : (∑ i, H i).toReal = ∑ i, (H i).toReal :=
    ENNReal.toReal_sum (fun i _ => hne i)
  have hHj : ∀ j, (H j).toReal ≤ ∑ i, (H i).toReal := by
    intro j
    rw [← htoReal_sum]
    exact ENNReal.toReal_mono hS (hsingle j)
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)
  · intro j z hz
    have hz1 : z ∈ polydisc (0 : Fin n → ℂ) (fun _ => 1) := trackSet_subset_unit hz
    have h1 : ENNReal.ofReal ‖f j z‖ ≤ H j :=
      norm_apply_le_holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) hz1
    have h2 : ‖f j z‖ ≤ (H j).toReal := (ENNReal.ofReal_le_iff_le_toReal (hne j)).mp h1
    exact le_trans h2 (hHj j)
  · intro j x y hx hy
    by_cases hxy : x = y
    · subst hxy
      simp only [sub_self, norm_zero]
      rw [Real.zero_rpow (ne_of_gt hα), mul_zero]
    · have hx1 : x ∈ polydisc (0 : Fin n → ℂ) (fun _ => 1) := trackSet_subset_unit hx
      have hy1 : y ∈ polydisc (0 : Fin n → ℂ) (fun _ => 1) := trackSet_subset_unit hy
      -- The `0`-th iterated derivative is the function itself, up to the isometry to
      -- `0`-multilinear maps; so the norm of a difference agrees with `‖f j x - f j y‖`.
      have hns : ‖iteratedFDerivWithin ℝ 0 (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) x
          - iteratedFDerivWithin ℝ 0 (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) y‖
          = ‖f j x - f j y‖ := by
        simpa [dist_eq_norm] using
          (dist_iteratedFDerivWithin_zero (𝕜 := ℝ) (f := f j) (s := polydisc (0 : Fin n → ℂ) (fun _ => 1))
            (x := x) (g := f j) (t := polydisc (0 : Fin n → ℂ) (fun _ => 1)) (y := y))
      have hle : ENNReal.ofReal (‖f j x - f j y‖ / ‖x - y‖ ^ α) ≤ H j := by
        rw [← hns]
        exact le_trans
          (le_holderSeminorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) hx1 hy1 hxy)
          (holderSeminorm_le_holderNorm 0 α (f j) (polydisc (0 : Fin n → ℂ) (fun _ => 1)) (le_refl 0))
      have h2 : ‖f j x - f j y‖ / ‖x - y‖ ^ α ≤ (H j).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal (hne j)).mp hle
      have h3 : ‖f j x - f j y‖ / ‖x - y‖ ^ α ≤ (∑ i, (H i).toReal) :=
        le_trans h2 (hHj j)
      have hd : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      have h4 : ‖f j x - f j y‖ = (‖f j x - f j y‖ / ‖x - y‖ ^ α) * ‖x - y‖ ^ α :=
        (div_mul_cancel₀ _ (ne_of_gt hd)).symm
      rw [h4]
      exact mul_le_mul_of_nonneg_right h3 hd.le

end Work.CR.Flat.Cauchy
