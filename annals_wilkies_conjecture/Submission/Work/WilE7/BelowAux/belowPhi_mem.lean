import Mathlib
import Submission.Work.WilE7.BelowAux.BelowDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.BelowAux
open WilkiesDesign WilkiesDesign.E

theorem belowPhi_mem {p m k : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set) :
    ∀ q ∈ Work.WilE7.BelowAux.belowH Z s j u₀,
      Work.WilE7.BelowAux.belowPhi s j q ∈ (Work.WilE7.BelowAux.belowS Z S).set := by
  intro q hq
  rw [mem_belowH] at hq
  obtain ⟨hq1, hqlo, hqhi⟩ := hq
  -- the base point is in the semipfaffian set `Z`
  have hZ : q.1 ∈ Z.set := connectedComponentIn_subset Z.set u₀ hq1
  -- its base projection lies in `C`
  have hxC : projFirst p (m + 1) q.1 ∈ C := by rw [hC]; exact ⟨q.1, hq1, rfl⟩
  -- the corresponding point of the stratum
  have hS : Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1)) ∈ S.X.set :=
    hsub j _ hxC
  -- the stratum point lies in the cube, so the sheet level is `≤ 1`
  have hcube : ∀ i : Fin (p + (m + 1)),
      |Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1)) i| ≤ 1 := hS.1
  have hlev : (s j (projFirst p (m + 1) q.1)) (Fin.last m) ≤ 1 := by
    have h := hcube (Fin.natAdd p (Fin.last m))
    rw [Fin.append_right] at h
    exact (abs_le.mp h).2
  have hV2 : belowV2 (belowPhi s j q) = (s j (projFirst p (m + 1) q.1)) (Fin.last m) :=
    belowV2_belowPt _ _ _
  rw [belowS_mem_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [belowZ1_belowPhi]; exact hZ
  · rw [belowZ2_belowPhi]; exact hS
  · rw [belowZ1_belowPhi, belowZ2_belowPhi, projFirst_append]
  · rw [belowT_belowPhi]; exact abs_le.mpr ⟨hqlo, le_trans (le_of_lt hqhi) hlev⟩
  · rw [belowT_belowPhi, hV2]; exact hqhi

end Work.WilE7.BelowAux
