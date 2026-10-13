import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.SigmaAux

namespace Work.CoreStep

theorem hclosed_of_sigma {n m s : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (Sig : List (WilkiesDesign.E.SemiPf (n + s)))
    (hfront : Work.CoreStep.frontierSet n m T ⊆
      ⋃ S ∈ Sig, WilkiesDesign.E.projFirst n s '' S.set)
    (C : Set (Fin n → ℝ))
    (hdisj : ∀ S ∈ Sig, Disjoint C (WilkiesDesign.E.projFirst n s '' S.set)) :
    ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T := by
  intro z hz hzC
  by_contra hznot
  have hzfront : WilkiesDesign.E.projFirst n (m + 1) z ∈ frontierSet n m T :=
    ⟨z, ⟨hz, hznot⟩, rfl⟩
  have hmem := hfront hzfront
  simp only [Set.mem_iUnion, Set.mem_image] at hmem
  obtain ⟨S, hS, w, hw, hwe⟩ := hmem
  exact (Set.disjoint_left.mp (hdisj S hS)) hzC ⟨w, hw, hwe⟩

end Work.CoreStep
