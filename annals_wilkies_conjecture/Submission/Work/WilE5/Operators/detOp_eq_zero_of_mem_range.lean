import Mathlib
import Submission.Work.Wilkies.E.Spec

namespace Work.WilE5.Operators

/-- If the index `l` lies in the range of `ι`, then the `(j+1)×(j+1)` determinant `detOp c h ι l f`
vanishes: the column with derivative `∂_{ι a₀}` (where `ι a₀ = l`) coincides with the last column,
whose derivative is `∂_l`. -/
theorem detOp_eq_zero_of_mem_range {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r) (h : Fin j → WilkiesDesign.E.EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (hl : ∃ a, ι a = l) (f : WilkiesDesign.E.EAPoly k r) :
    WilkiesDesign.E.detOp c h ι l f = 0 := by
  obtain ⟨a₀, ha₀⟩ := hl
  unfold WilkiesDesign.E.detOp
  refine Matrix.det_zero_of_column_eq (i := Fin.castSucc a₀) (j := Fin.last j) ?_ ?_
  · exact Fin.castSucc_ne_last a₀
  · intro a
    simp [Fin.lastCases_castSucc, Fin.lastCases_last, ha₀]

end Work.WilE5.Operators
