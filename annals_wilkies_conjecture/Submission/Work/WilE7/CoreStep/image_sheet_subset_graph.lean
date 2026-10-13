import Mathlib
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.DecompDefs

namespace Work.WilE7.CoreStep

theorem image_sheet_subset_graph {p m K k : ℕ} (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (tt : Fin K → (Fin p → ℝ) → ℝ)
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcovS : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
        ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
          WilkiesDesign.E.projSnd p (m + 1) z)
    (hlevel : ∀ j : Fin k, ∃ i : Fin K, ∀ x ∈ C,
      tt i x = Work.WilE7.CoreStep.vertCoord (s j x)) :
    projTop p m '' X.set ∩ Work.WilE7.cyl C ⊆
      ⋃ i : Fin K, Work.WilE7.gr C (tt i) ∩ Work.WilE7.cyl C := by
  rintro y ⟨⟨z, hz, hzy⟩, hycyl⟩
  have hyC : Fin.init y ∈ C := hycyl.1
  have hC : WilkiesDesign.E.projFirst p (m + 1) z ∈ C := by
    rw [← projTop_init p m z, hzy]; exact hyC
  obtain ⟨j, hj⟩ := hcovS z hz hC
  obtain ⟨i, hi⟩ := hlevel j
  refine Set.mem_iUnion.2 ⟨i, ⟨?_, hycyl⟩⟩
  have hiny : Fin.init y = WilkiesDesign.E.projFirst p (m + 1) z := by
    rw [← hzy, projTop_init]
  refine ⟨hyC, ?_⟩
  rw [hi (Fin.init y) hyC, hiny, hj, ← hzy, projTop_last]
  rfl

end Work.WilE7.CoreStep
