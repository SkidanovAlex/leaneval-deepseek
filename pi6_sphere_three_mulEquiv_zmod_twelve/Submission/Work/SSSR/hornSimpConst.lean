import Mathlib
import Submission.Work.SSSR.serreE1PieceDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open scoped Simplicial
open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
/-- **The constant simplex at the last vertex lies in the horn of `Δ[s]`** (for `1 ≤ s`).
`Work.SSSR.hornSimp s ⊆ Δ[s]` is the horn `⋃_{i<s} d_i Δ[s]`, i.e. the subcomplex of simplices
`a : [n] → [s]` whose image misses some vertex `< s`; equivalently
`a ∈ (hornSimp s).obj _ ↔ ∃ i : Fin s, ∀ j, a j ≠ i.castSucc` (see
`SSet.stdSimplex.mem_face_iff` and `Work.SSSR.hornSimp`).

Every value of the constant map `SSet.const ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s))`
is the degenerate simplex at the last vertex `v_s`, whose image is `{s}`; this misses the vertex
`0` because `s ≠ 0` when `1 ≤ s`, hence lies in the horn.  So the constant map at `v_s` lands in
`hornSimp s`. -/
theorem hornSimpConst (s : ℕ) (hs : 1 ≤ s) :
    (⊤ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet).Subcomplex)
      ≤ (Work.SSSR.hornSimp s).preimage
        (SSet.const (X := (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet))
          ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s))) := by
  rw [Subfunctor.le_def]
  intro U x _
  rw [SSet.Subcomplex.preimage_obj]
  rw [Work.SSSR.hornSimp, Subfunctor.iSup_obj]
  refine Set.mem_iUnion.mpr ⟨⟨0, hs⟩, ?_⟩
  rw [SSet.stdSimplex.face_obj]
  simp only [Set.mem_ofPred_eq, Finset.image_subset_iff, Finset.mem_compl, Finset.mem_singleton]
  intro j _
  -- The value of the constant map is `Δ[s].map (U.unop.const _ 0).op v_s`, an
  -- `U`-simplex whose underlying order map is constantly the last vertex `s`.
  have hw : (ConcreteCategory.hom
        ((SSet.const (X := (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet))
          ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s))).app U)) x
      = (ConcreteCategory.hom ((Δ[s]).map (U.unop.const _ 0).op))
          ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s)) := rfl
  rw [hw]
  have hobj : SSet.stdSimplex.objEquiv
      ((Δ[s]).map (U.unop.const _ 0).op
        ((SSet.stdSimplex.obj₀Equiv (n := s)).symm (Fin.last s)))
      = SimplexCategory.const U.unop ⦋s⦌ (Fin.last s) := by
    have hconst : SSet.stdSimplex.objEquiv (SSet.stdSimplex.const s (Fin.last s) (op ⦋0⦌))
        = SimplexCategory.const ⦋0⦌ ⦋s⦌ (Fin.last s) := rfl
    rw [SSet.stdSimplex.map_apply]
    simp only [Equiv.apply_symm_apply, SSet.stdSimplex.obj₀Equiv_symm_apply]
    rw [Quiver.Hom.unop_op, SimplexCategory.const_comp, hconst, SimplexCategory.const_apply]
  rw [hobj, SimplexCategory.const_apply]
  intro hcontra
  have := congrArg Fin.val hcontra
  simp at this
  omega

end Work.SSSR
