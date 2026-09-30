import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSSR.HornDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory in
/-- Naturality of `morphSimplex` under postcomposition with a morphism of the simplex category:
the shape of a simplex `σ` restricted along `φ` is the shape of `σ` precomposed with the induced
map of standard simplices. -/
theorem morphSimplex_naturality_apply {X : Type} [TopologicalSpace X] {k m : ℕ}
    (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk m)
    (σ : SSet.stdSimplex.obj (SimplexCategory.mk m) ⟶ TopCat.toSSet.obj (TopCat.of X))
    (z : stdSimplex ℝ (Fin (k + 1))) :
    ⇑(Work.SSSR.morphSimplex k X (SSet.stdSimplex.map φ ≫ σ)) z =
      ⇑(Work.SSSR.morphSimplex m X σ) (stdSimplex.map (⇑φ) z) := by
  simp only [morphSimplex, simplexEquiv, Equiv.trans_apply]
  rw [← SSet.yonedaEquiv_naturality φ σ]
  exact TopCat.toSSetObjEquivT_naturality_apply φ (SSet.yonedaEquiv σ) z

end Work.SSSR
