import Mathlib
import Submission.Work.Mostow.LinAlgMatrixIneqAux

namespace Work.Mostow

/-- `Kset n δ` is the intersection of the closed half-spaces `x i ≥ δ` with the affine
hyperplane `∑ i, x i = 1`.  It is a closed subset of the compact box `∏ i, [δ, 1]`
(bounded because the coordinates are nonnegative and sum to one), hence compact. -/
theorem isCompact_Kset (n : ℕ) {δ : ℝ} (hδ : 0 < δ) : IsCompact (Kset n δ) := by
  have hclosed : IsClosed (Kset n δ) := by
    have hset : Kset n δ
        = {x : Fin n → ℝ | ∀ i, δ ≤ x i} ∩ {x | ∑ i, x i = 1} := rfl
    rw [hset]
    refine IsClosed.inter ?_ ?_
    · rw [show {x : Fin n → ℝ | ∀ i, δ ≤ x i} = ⋂ i, {x | δ ≤ x i} from by ext x; simp]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi (s := fun _ : Fin n => Set.Icc δ 1) fun _ => isCompact_Icc)
    hclosed ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro i
  refine ⟨hx.1 i, ?_⟩
  have hnonneg : ∀ j, 0 ≤ x j := fun j => le_trans hδ.le (hx.1 j)
  have h1 := Finset.single_le_sum (f := x) (fun j _ => hnonneg j) (Finset.mem_univ i)
  simpa [hx.2] using h1

end Work.Mostow
