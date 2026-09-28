import Mathlib
import Submission.Work.Cohomology.SubdivisionHomotopyData
import Submission.Work.Cohomology.Sd_comm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Simplicial Limits in
open scoped Simplicial in
/-- Evaluating the null-homotopic chain map `nullHomotopicMap' (tRel X)` on the generator of a
singular `(m+1)`-simplex: it is the signed sum of the homotopy images of the faces plus the
boundary of the homotopy image. -/
theorem tRel_eval (X : TopCat) (m : ℕ) (σ : (TopCat.toSSet.obj X) _⦋m + 1⦌) :
    (Homotopy.nullHomotopicMap' (tRel X)).f (m + 1) (gen X (m + 1) σ) =
      (∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • tElem X m ((TopCat.toSSet.obj X).δ i σ))
        + ((singularChains ℤ X).d (m + 2) (m + 1)).hom (tElem X (m + 1) σ) := by
  rw [Homotopy.nullHomotopicMap'_f (k₂ := m + 2) (k₁ := m + 1) (k₀ := m)
    (ComplexShape.down_mk (m + 2) (m + 1) rfl) (ComplexShape.down_mk (m + 1) m rfl) (tRel X)]
  rw [tRel_self X m, tRel_self X (m + 1)]
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.add_apply]
  rw [tHom_gen X (m + 1) σ, d_gen X m σ]
  congr 1
  rw [map_sum]
  congr 1
  ext i
  rw [map_zsmul, tHom_gen]

end Work.Cohomology
