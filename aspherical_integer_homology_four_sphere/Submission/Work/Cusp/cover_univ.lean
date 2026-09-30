import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.cuspInvOuter_mem_Sq
import Submission.Work.Cusp.wedge_cover
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The cover theorem on `M̂`.**  If the fold charts `Φ i` cover the interior `M̄ ∖ Tset` of the
hyperbolic piece, then `M̂` is covered by the images of their sources together with the images, in
the five filling pieces, of the three layer strata (collar `‖p‖∞ ≥ 1/2`, polar `1/24 < ‖p‖∞`, core
`‖p‖∞ < 1/12`).

A point of `M̂` is the image either of a point `x` of `M̄` or of a point `(p,y)` of a filling piece.

* If `x ∉ Tset`, the fold charts cover it.
* If `x ∈ Tset`, then `x` is glued to a boundary point of a filling piece, whose layer parameter is
  `‖p‖∞ = 1 ≥ 1/2`, so it lies in the collar layer.
* For a filling point `(p,y)`, the layer parameter `r = ‖p‖∞ ∈ [0,1]` satisfies `r ≥ 1/2` (collar),
  or `r < 1/2 ≤ 12/24` and `r > 1/24` (polar), or `r ≤ 1/24 < 1/12` (core). -/
theorem cover_univ (a : Work.Space.Assembly) (ι : Type) [Fintype ι]
    (Phi : ι → OpenPartialHomeomorph a.Mbar E4)
    (hfold : {x : a.Mbar | x ∉ a.Tset} ⊆ ⋃ i, (Phi i).source) :
    (⋃ i, a.incMbar '' (Phi i).source) ∪
      (⋃ v : Work.Space.Cusp, a.incW v '' (collarLayer (a.Torus v))) ∪
      (⋃ v : Work.Space.Cusp, a.incW v '' (polarLayer (a.Torus v))) ∪
      (⋃ v : Work.Space.Cusp, a.incW v '' (coreLayer (a.Torus v))) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro z
  obtain ⟨w, rfl⟩ := Quotient.exists_rep z
  rcases w with x | y
  · -- `z` is the image of a point `x` of `M̄`.
    change a.incMbar x ∈ _
    by_cases hx : x ∈ a.Tset
    · -- `x` lies on the glued boundary: it is a collar point of a filling piece.
      rw [a.incMbar_eq_incW hx]
      refine Or.inl (Or.inl (Or.inr ?_))
      refine Set.mem_iUnion.mpr ⟨(a.glue ⟨x, hx⟩).1.1, ?_⟩
      refine Set.mem_image_of_mem _ ?_
      have hb : nrm ((a.glue ⟨x, hx⟩).1.2.1 : E2) = 1 := (a.glue ⟨x, hx⟩).2
      simp only [collarLayer, Set.mem_setOf_eq]
      rw [hb]
      norm_num
    · -- `x` lies off `Tset`: one of the fold charts covers it.
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hfold hx)
      exact Or.inl (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ hi⟩)))
  · -- `z` is the image of a point `(p, y)` of a filling piece.
    obtain ⟨v, p⟩ := y
    change a.incY ⟨v, p⟩ ∈ _
    rcases le_or_gt (1/2 : ℝ) (nrm (p.1 : E2)) with hc | hc
    · -- collar layer `‖p‖∞ ≥ 1/2`
      exact Or.inl (Or.inl (Or.inr
        (Set.mem_iUnion.mpr ⟨v, Set.mem_image_of_mem _
          (by simpa [collarLayer] using hc)⟩)))
    · rcases le_or_gt (nrm (p.1 : E2)) (1/24 : ℝ) with hp | hp
      · -- core layer `‖p‖∞ ≤ 1/24 < 1/12`
        exact Or.inr (Set.mem_iUnion.mpr ⟨v, Set.mem_image_of_mem _
          (by simp only [coreLayer, Set.mem_setOf_eq]; linarith)⟩)
      · -- polar layer `1/24 < ‖p‖∞ < 1/2`
        exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨v, Set.mem_image_of_mem _
          (by simp only [polarLayer, Set.mem_setOf_eq]; exact hp)⟩))

end Work.Cusp
