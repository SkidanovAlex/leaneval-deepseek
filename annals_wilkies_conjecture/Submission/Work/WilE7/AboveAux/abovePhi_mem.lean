import Mathlib
import Submission.Work.WilE7.AboveAux.AboveDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.AboveAux
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux

theorem abovePhi_mem {p m k : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set) :
    ∀ q ∈ Work.WilE7.AboveAux.aboveH Z s j u₀,
      Work.WilE7.AboveAux.abovePhi s j q ∈ (Work.WilE7.AboveAux.aboveS Z S).set := by
  intro q hq
  rw [mem_aboveH] at hq
  obtain ⟨hq1, hqlast, hqtop⟩ := hq
  have hxC : projFirst p (m + 1) q.1 ∈ C := by
    rw [hC]; exact Set.mem_image_of_mem _ hq1
  have hmem := hsub j (projFirst p (m + 1) q.1) hxC
  have hcube : Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1))
      ∈ cubeC (p + (m + 1)) := hmem.1
  have hlvl : -1 ≤ (s j (projFirst p (m + 1) q.1)) (Fin.last m) := by
    have := hcube (Fin.natAdd p (Fin.last m))
    rw [Fin.append_right] at this
    linarith [neg_abs_le ((s j (projFirst p (m + 1) q.1)) (Fin.last m))]
  have ht : |q.2| ≤ 1 := abs_le.mpr ⟨by linarith, hqtop⟩
  show belowPt q.1 (s j (projFirst p (m + 1) q.1)) q.2 ∈ (aboveS Z S).set
  refine abovePt_mem Z S q.1 ?_ (s j (projFirst p (m + 1) q.1)) q.2 ?_ ht ?_
  · exact connectedComponentIn_subset Z.set u₀ hq1
  · exact hmem
  · exact hqlast

end Work.WilE7.AboveAux
