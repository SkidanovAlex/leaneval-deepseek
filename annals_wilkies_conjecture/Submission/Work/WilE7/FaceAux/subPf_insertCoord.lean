import Mathlib
import Submission.Work.WilE7.FaceAux.InsertCoord

namespace Work.WilE7.FaceAux

open WilkiesDesign.E

theorem subPf_insertCoord {p : ℕ} (C : Set (Fin p → ℝ)) {t : ℝ} (ht : |t| ≤ 1)
    (hC : WilkiesDesign.E.SubPf p C) :
    WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = t} := by
  obtain ⟨m, X, hX⟩ := hC
  refine ⟨m, insertCoord X t, ?_⟩
  rw [insertCoord_set X ht, hX,
    projFirst_insertCoord (Work.WilE8.SemiPf.set_subset_cube X) t ht]

end Work.WilE7.FaceAux
