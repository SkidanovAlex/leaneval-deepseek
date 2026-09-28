import Mathlib
import Submission.Work.SSS.serreE1EZ

namespace Work.SSS

/-- **A simplex of `Δ[P]` whose underlying monotone map misses a vertex lies in `∂Δ[P]`.**

`Work.SSS.stdIdSimplex P` is the fundamental `P`-simplex of `Δ[P]`, i.e. the simplex corresponding
to the identity morphism `⦋P⦌ ⟶ ⦋P⦌`.  For any morphism `g : ⦋m⦌ ⟶ ⦋P⦌` of `SimplexCategory` and
any vertex `j : Fin (P+1)` not in the image of the underlying monotone map `g`, the `m`-simplex
`(Δ[P]).map g.op (stdIdSimplex P)` of `Δ[P]` (the simplex corresponding to the composite `g ≫ 𝟙`)
lies in the boundary subcomplex `∂Δ[P]`.

Proof sketch: `(Δ[P]).map g.op (stdIdSimplex P) = SSet.stdSimplex.objEquiv.symm (g ≫ 𝟙)`, whose
underlying monotone map is `g` (`SSet.stdSimplex.coe_asOrderHom_objEquiv_symm` combined with
`SSet.stdSimplex.map_apply`), so `SSet.mem_boundary_iff_notMem_range` applies with the witness `j`.

(The statement is written in a notation-free style so that it elaborates standalone; the proof may
`open scoped Simplicial`/`open CategoryTheory` freely.) -/
theorem mem_boundary_map_stdIdSimplex {P m : ℕ}
    (g : SimplexCategory.mk m ⟶ SimplexCategory.mk P) (j : Fin (P+1))
    (hj : ∀ k : Fin (m+1), ¬ (CategoryTheory.ConcreteCategory.hom g) k = j) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}).map (Opposite.op g)
        (Work.SSS.stdIdSimplex P))
      ∈ (SSet.boundary P).obj (Opposite.op (SimplexCategory.mk m)) := by
  rw [SSet.mem_boundary_iff_notMem_range]
  refine ⟨j, fun h => ?_⟩
  obtain ⟨k, hk⟩ := h
  refine hj k ?_
  rw [← hk]
  simp only [Work.SSS.stdIdSimplex, SSet.stdSimplex.map_apply,
    SSet.stdSimplex.objEquiv.apply_symm_apply]
  rfl

end Work.SSS
