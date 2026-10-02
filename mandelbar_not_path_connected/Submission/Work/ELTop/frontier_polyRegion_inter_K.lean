import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.ELTop.landsN_mem_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

/-- The boundary of the ray polygon, met with the filled Julia set, is exactly the set of
landing points of its pairs: the ray pieces lie off `K c` (they are contained in the rays, which
are disjoint from `K c`), and the equipotential arc of level `R > 1` lies off `K c` as well. -/
theorem polyCurve_inter_K {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) {R : ℝ} (hR : 1 < R) :
    Work.EL.polyCurve ps R ∩ Work.EL.K c = {z : ℂ | ∃ P ∈ ps, P.y = z} := by
  ext z
  constructor
  · rintro ⟨hzC, hzK⟩
    rw [Work.EL.polyCurve] at hzC
    simp only [Set.mem_ofPred_eq] at hzC
    rcases hzC with ⟨P, hP, hyz | hpa | hpb⟩ | ⟨θ, hθ, hfar, hθz⟩
    · exact ⟨P, hP, hyz.symm⟩
    · exfalso
      exact (Work.EL.paramRay_subset_compl hN P.a
        (Work.Top.NakaneData.rayPiece_subset_paramRay hpa)) hzK
    · exfalso
      exact (Work.EL.paramRay_subset_compl hN P.b
        (Work.Top.NakaneData.rayPiece_subset_paramRay hpb)) hzK
    · exfalso
      exact (Work.EL.rayPt_notMem_K hN hR) (hθz ▸ hzK)
  · rintro ⟨P, hP, hyz⟩
    refine ⟨?_, landsN_mem_K hN (hyz ▸ P.lands_a)⟩
    rw [Work.EL.polyCurve]
    simp only [Set.mem_ofPred_eq]
    exact Or.inl ⟨P, hP, Or.inl hyz.symm⟩

theorem frontier_polyRegion_inter_K {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    frontier (Work.EL.polyRegion ps R) ∩ Work.EL.K c = {z : ℂ | ∃ P ∈ ps, P.y = z} := by
  have hCK := polyCurve_inter_K hN ps hR
  -- `polyRegion` is one of the two sides of the Jordan curve `polyCurve ps R`
  let S : Work.Top.Sides (Work.EL.polyCurve ps R) := hJ.sides (Work.EL.polyCurve ps R) hC
  have hseedD : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈ Work.EL.polyRegion ps R :=
    seed_mem_polyRegion hN ps hA hR
  have hseedC : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R)
      ∈ (Work.EL.polyCurve ps R)ᶜ := Work.EL.polyRegion_subset_compl ps R hseedD
  have hseed_union : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈ S.I ∪ S.O := by
    rw [S.union_eq]; exact hseedC
  have hfront : frontier (Work.EL.polyRegion ps R) = Work.EL.polyCurve ps R := by
    rcases hseed_union with hseedI | hseedO
    · have hsub : S.I ⊆ Work.EL.polyRegion ps R :=
        S.preconnected_I.subset_connectedComponentIn hseedI S.subset_compl_I
      have hle : Work.EL.polyRegion ps R ⊆ S.I := by
        rcases S.subset_of_preconnected (Work.EL.isPreconnected_polyRegion ps R)
          (Work.EL.polyRegion_subset_compl ps R) with h | h
        · exact h
        · exact absurd (h hseedD) (S.notMem_O_of_mem_I hseedI)
      rw [Set.Subset.antisymm hle hsub, S.frontier_I]
    · have hsub : S.O ⊆ Work.EL.polyRegion ps R :=
        S.preconnected_O.subset_connectedComponentIn hseedO S.subset_compl_O
      have hle : Work.EL.polyRegion ps R ⊆ S.O := by
        rcases S.subset_of_preconnected (Work.EL.isPreconnected_polyRegion ps R)
          (Work.EL.polyRegion_subset_compl ps R) with h | h
        · exact absurd (h hseedD) (S.notMem_I_of_mem_O hseedO)
        · exact h
      rw [Set.Subset.antisymm hle hsub, S.frontier_O]
  rw [hfront]
  exact hCK

end Work.ELTop
