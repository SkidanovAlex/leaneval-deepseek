import Mathlib
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Cohomology.relChainsHomeomorphCompat

namespace Work.Serre.Csr

noncomputable section

open scoped Topology unitInterval

/-- **The homeomorphism `(x, y) ↦ (x, e y)` of pullbacks.**  For maps `q : E → B`, `χ : D → B` and
a homeomorphism `e : D' ≃ₜ D`, the map `(x, y) ↦ (x, e y)` carries the pullback of `q` along
`χ ∘ e` homeomorphically onto the pullback of `q` along `χ`. -/
def pullbackHomeo {D D' B E : Type*} [TopologicalSpace D] [TopologicalSpace D']
    [TopologicalSpace B] [TopologicalSpace E]
    (q : C(E, B)) (χ : C(D, B)) (e : D' ≃ₜ D) :
    Work.StemsB.Pullback q (χ.comp (homeoToCM e)) ≃ₜ Work.StemsB.Pullback q χ where
  toFun x := ⟨(x.1.1, e x.1.2), x.2⟩
  invFun x := ⟨(x.1.1, e.symm x.1.2), by
    have h := x.2
    rw [ContinuousMap.comp_apply, homeoToCM_apply, Homeomorph.apply_symm_apply]
    exact h⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp
  continuous_toFun := Continuous.subtype_mk
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (e.continuous.comp (continuous_snd.comp continuous_subtype_val)))
    (fun x => x.2)
  continuous_invFun := Continuous.subtype_mk
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (e.symm.continuous.comp (continuous_snd.comp continuous_subtype_val)))
    (fun x => by simpa using x.2)

/-- **The cube model of the disc pair.**  Let `χ = cellMap n Y ι f i` be the characteristic map of
the `i`-th `(n+2)`-cell and `e = cubeDiscHomeo n : I^{n+2} ≃ₜ cellDisk n` the standard
homeomorphism carrying the boundary of the cube to the unit sphere.  The map
`(x,y) ↦ (x, e y)` is a homeomorphism of pairs `(Pullback q (χ ∘ e), (χ ∘ e)^*∂I^{n+2}) ≅
(Pullback q χ, χ^*(S^{n+2}))`, so it induces an isomorphism on relative singular homology over `ℤ`
in every degree. -/
theorem relChainsCubeDisc (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) (k : ℕ) :
    Nonempty
      (((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback q
          ((Work.RatHurewicz.cellMap n Y ι f i).comp (homeoToCM (cubeDiscHomeo n)))))
        {x : Work.StemsB.Pullback q
            ((Work.RatHurewicz.cellMap n Y ι f i).comp (homeoToCM (cubeDiscHomeo n))) |
          Work.StemsB.pullbackSnd q
            ((Work.RatHurewicz.cellMap n Y ι f i).comp (homeoToCM (cubeDiscHomeo n))) x ∈
              Cube.boundary (Fin (n+2))}).homology k)
        ≅
       ((Work.Cohomology.relChains
          (TopCat.of (Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i)))
        {x : Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i) |
          Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i) x ∈ dSph n 1}).homology k)) := by
  refine Work.Cohomology.relChainsHomeomorphCompat _ _ _ _
    (pullbackHomeo q (Work.RatHurewicz.cellMap n Y ι f i) (cubeDiscHomeo n)) ?_ k
  intro x
  show x.1.2 ∈ Cube.boundary (Fin (n+2)) ↔ cubeDiscHomeo n x.1.2 ∈ dSph n 1
  exact cubeDiscHomeo_boundary n x.1.2

end

end Work.Serre.Csr
