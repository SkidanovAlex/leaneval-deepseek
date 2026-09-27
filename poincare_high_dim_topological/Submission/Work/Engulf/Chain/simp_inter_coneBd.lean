import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.ConeGeom
import Submission.Work.Engulf.Chain.ConeDefs
import Submission.Work.Engulf.Chain.ConeSetup
import Submission.Work.Engulf.Chain.coneCx_exists

/-!
# `Work.Engulf.Chain.simp_inter_coneBd`

The simplex on a face `σ` of a complex `Γ` meets the lateral boundary `coneBd a σ` of the cone
`aσ` (apex `a` generic, i.e. outside `⋃_{s ∈ Γ.faces} affineSpan (σ ∪ s)`) only in the boundary
`⋃_{v ∈ σ} simp (σ \ {v})` of `σ`.

The proof is short because the cone complex `Γ ∪ a ∗ σ` of Newman §12 is already available
(`Work.Engulf.Chain.coneCx_exists`): both `σ` and `insert a (σ \ {w})` are faces of it, so their
simplices meet in the simplex on the intersection of their vertex sets
(`Work.Engulf.simp_inter`), and `σ ∩ insert a (σ \ {w}) = σ \ {w}` because the generic apex is
not a vertex of `σ`.
-/

open Set Metric PL

namespace Work.Engulf.Chain

/-- The simplex on `σ` meets the lateral boundary `coneBd a σ = ⋃_{w ∈ σ} simp ((insert a σ) \ {w})`
of the cone `aσ` only in the boundary `⋃_{v ∈ σ} simp (σ \ {v})` of `σ`, when the apex `a` is
generic (`a` outside `affineSpan ℝ (σ ∪ s)` for every face `s` of `Γ`). -/
theorem simp_inter_coneBd {N : ℕ} (Γ : PL.Cx N) (σ : Finset (PL.E N)) (a : PL.E N)
    (hσ : σ ∈ Γ.faces)
    (hgen : ∀ s ∈ Γ.faces,
      a ∉ (affineSpan ℝ (((σ ∪ s : Finset (PL.E N)) : Set (PL.E N))) : Set (PL.E N))) :
    PL.simp σ ∩ Work.Engulf.Chain.coneBd a σ ⊆ ⋃ v ∈ σ, PL.simp (σ.erase v) := by
  -- the apex is outside `affineSpan ℝ σ`, hence not a vertex of `σ`
  have hass : a ∉ (affineSpan ℝ ((σ : Set (PL.E N))) : Set (PL.E N)) := by
    have h := hgen σ hσ
    rwa [Finset.union_self] at h
  have hane : a ∉ σ := fun h =>
    hass (subset_affineSpan ℝ ((σ : Set (PL.E N))) (by simpa using h))
  -- the cone complex `Γ' = Γ ∪ a ∗ σ` having `σ` and `insert a (σ \ {w})` as faces
  obtain ⟨Γ', hΓ'⟩ := coneCx_exists Γ σ a hσ hgen
  have hσ' : σ ∈ Γ'.faces := by
    rw [hΓ']; exact faces_subset_coneFaces σ a hσ
  rw [coneBd_eq hane]
  rintro x ⟨hxσ, hxB⟩
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxB
  refine Set.mem_iUnion₂.mpr ⟨w, hw, ?_⟩
  have hw' : insert a (σ.erase w) ∈ Γ'.faces := insert_a_erase_mem_faces hΓ' hσ w
  have hinter : x ∈ PL.simp σ ∩ PL.simp (insert a (σ.erase w)) := ⟨hxσ, hxw⟩
  rw [Work.Engulf.simp_inter hσ' hw'] at hinter
  have hvi : σ ∩ insert a (σ.erase w) = σ.erase w := by
    rw [Finset.inter_insert_of_notMem hane,
      (Finset.inter_eq_right).mpr (Finset.erase_subset w σ)]
  rwa [hvi] at hinter

end Work.Engulf.Chain
