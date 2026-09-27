import Mathlib
import Submission.Work.PL.Subdiv.SdBasic
import Submission.Work.PL.Subdiv.Util.Mesh.sd_mesh
import Submission.Work.PL.Subdiv.Util.Mesh.exists_fine

namespace Work.PL.Subdiv.Util.Mesh

/-- A finite complex admits an explicit dimension bound: the maximum number of vertices over its
faces.  This is the hypothesis `DimLE K d` required by `exists_fine`. -/
private theorem exists_dimle_of_finite {N : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) :
    ∃ d : ℕ, 0 < d ∧ PL.DimLE K d := by
  refine ⟨max (hK.toFinset.sup fun s => s.card) 1, Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), ?_⟩
  intro s hs
  have hsT : s ∈ hK.toFinset := (Set.Finite.mem_toFinset hK).mpr hs
  have hle : s.card ≤ hK.toFinset.sup (fun s => s.card) := Finset.le_sup hsT
  omega

theorem exists_fine_general {N : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ r, ∀ r' ≥ r, PL.MeshLT (Work.PL.Subdiv.sdIter r' K hK) δ := by
  obtain ⟨d, hd, hdim⟩ := exists_dimle_of_finite K hK
  exact exists_fine K hK d hd hdim δ hδ

end Work.PL.Subdiv.Util.Mesh
