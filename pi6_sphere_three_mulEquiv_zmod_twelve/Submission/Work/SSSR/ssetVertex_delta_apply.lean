import Mathlib
import Submission.Work.SSSR.coherentLiftDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial
/-- **How a coface of the standard simplex acts on general simplices.**  The covariant action of
`SimplexCategory` on the standard simplex is by postcomposition of the underlying monotone maps:
`(stdSimplex.map g).app m x` corresponds under `objEquiv` to `objEquiv x ≫ g`. -/
lemma objEquiv_stdSimplex_map {n n' : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (g : n ⟶ n') (x : (SSet.stdSimplex.obj n).obj m) :
    SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map g).app m x) = SSet.stdSimplex.objEquiv x ≫ g := by
  have h := SSet.stdSimplex.objEquiv_symm_comp (f := SSet.stdSimplex.objEquiv x) (g := g)
  rw [Equiv.symm_apply_apply] at h
  rw [← h, Equiv.apply_symm_apply]

/-- **The `0`-th vertex functoriality of a coface.**  Reading off the `0`-th vertex of a standard
simplex commutes with the action of a coface `g`: the vertex of `(stdSimplex.map g).app _ x` is the
image under `g` of the vertex of `x`. -/
lemma obj₀Equiv_stdSimplex_map {n n' : ℕ} (g : ⦋n⦌ ⟶ ⦋n'⦌) (x : Δ[n] _⦋0⦌) :
    SSet.stdSimplex.obj₀Equiv ((SSet.stdSimplex.map g).app (op ⦋0⦌) x)
      = g.toOrderHom (SSet.stdSimplex.obj₀Equiv x) := by
  rw [show SSet.stdSimplex.obj₀Equiv ((SSet.stdSimplex.map g).app (op ⦋0⦌) x)
        = (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map g).app (op ⦋0⦌) x)).toOrderHom 0 by
      rw [SSet.stdSimplex.obj₀Equiv_apply]; rfl]
  rw [objEquiv_stdSimplex_map, SimplexCategory.comp_toOrderHom]
  simp only [OrderHom.comp_coe, Function.comp_apply]
  rw [SSet.stdSimplex.obj₀Equiv_apply]
  rfl

/-- **The `0`-th vertex of `Δ[n+1]` pulled back along a face `δ_j` with `j ≠ 0` is the `0`-th
vertex of `Δ[n]`.**  Here `Work.SSSR.ssetVertex n = (SSet.stdSimplex.obj₀Equiv).symm 0` is the
`0`-simplex of `Δ[n]` corresponding to the vertex `0`, and `δ_j` with `j ≠ 0` is the coface
skipping the vertex `j`, which therefore fixes the vertex `0`. -/
theorem ssetVertex_delta_apply {n : ℕ} (j : Fin (n + 2)) (hj : j ≠ 0) :
    (SSet.stdSimplex.δ (n := n) j).app (Opposite.op (SimplexCategory.mk 0)) (Work.SSSR.ssetVertex n)
      = Work.SSSR.ssetVertex (n + 1) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [show SSet.stdSimplex.δ (n := n) j = SSet.stdSimplex.map (SimplexCategory.δ j) from rfl]
  rw [obj₀Equiv_stdSimplex_map]
  simp only [Work.SSSR.ssetVertex, Equiv.apply_symm_apply]
  rw [show (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ j)) (0 : Fin (n+1))
        = Fin.succAbove j 0 from rfl]
  exact Fin.succAbove_ne_zero_zero hj

end Work.SSSR
