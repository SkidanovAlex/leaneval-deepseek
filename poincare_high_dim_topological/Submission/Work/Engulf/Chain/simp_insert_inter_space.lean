import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.ConeGeom

namespace Work.Engulf.Chain

/-- Genericity of the apex: if `σ ∈ Γ.faces` and `a` is outside every affine span
`affineSpan ℝ (σ ∪ s)`, `s ∈ Γ.faces`, then the closed simplex `PL.simp (insert a σ)` meets the
space of `Γ` only in `PL.simp σ`.  (For a face `s`, `Work.Engulf.Aux.simp_insert_inter_simp_of_notMem`
with `u := σ` gives `simp (insert a σ) ∩ simp s ⊆ simp (σ ∩ s) ⊆ simp σ`.) -/
theorem simp_insert_inter_space {N : ℕ} (Γ : PL.Cx N) (σ : Finset (PL.E N)) (a : PL.E N)
    (hσ : σ ∈ Γ.faces)
    (hgen : ∀ s ∈ Γ.faces,
      a ∉ (affineSpan ℝ (((σ ∪ s : Finset (PL.E N)) : Set (PL.E N))) : Set (PL.E N))) :
    PL.simp (insert a σ) ∩ Γ.space ⊆ PL.simp σ := by
  rintro x ⟨hx1, hx2⟩
  -- `x` lies in the simplex of some face `s` of `Γ`
  rw [Geometry.SimplicialComplex.space, Set.mem_iUnion] at hx2
  obtain ⟨s, hx2⟩ := hx2
  rw [Set.mem_iUnion] at hx2
  obtain ⟨hs, hxs⟩ := hx2
  -- the two faces `σ` and `s` glue nicely
  have hglue : PL.simp σ ∩ PL.simp s ⊆ PL.simp (σ ∩ s) := by
    have h := Γ.inter_subset_convexHull hσ hs
    simpa only [PL.simp, Finset.coe_inter] using h
  -- the cone on `σ` with apex `a` meets `simp s` only in `simp (σ ∩ s)`
  have h := Work.Engulf.Aux.simp_insert_inter_simp_of_notMem (u := σ) (s := s) hglue (hgen s hs)
  exact PL.simp_mono Finset.inter_subset_left (h ⟨hx1, hxs⟩)

end Work.Engulf.Chain
