import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSS.serreE1Defs

namespace Work.SSS

open CategoryTheory Simplicial Opposite

/-- The `n`-simplex of the constant simplicial set map at `σ₀`, read through the dictionary
`TopCat.toSSetObjEquivT`, is the constant continuous map with value `toSSetObj₀Equiv σ₀`. -/
theorem toSSetObjEquiv_const_apply {B : Type} [TopologicalSpace B]
    (σ₀ : (Work.SSS.sSing B).obj (Opposite.op (SimplexCategory.mk 0))) (n : ℕ) {X : SSet.{0}}
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) :
    TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk n))
        ((SSet.const σ₀).app (Opposite.op (SimplexCategory.mk n)) x) =
      ContinuousMap.const (stdSimplex ℝ (Fin (n+1))) (TopCat.toSSetObj₀Equiv σ₀) := by
  -- `(SSet.const σ₀).app _ _` is the value at `σ₀` of the simplicial map induced by the
  -- constant order map `⦋n⦌ ⟶ ⦋0⦌`.
  have happ : (SSet.const σ₀).app (Opposite.op (SimplexCategory.mk n)) x =
      (ConcreteCategory.hom
        ((Work.SSS.sSing B).map
          (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op)) σ₀ := by
    rw [SSet.const_app]; rfl
  ext z
  rw [happ]
  -- naturality of the dictionary in the simplex category reduces the evaluation at `z`
  -- to the evaluation of `toSSetObjEquivT σ₀` at the (unique) point of `Δ[0]`.
  rw [TopCat.toSSetObjEquivT_naturality_apply]
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquivT_apply, ContinuousMap.const_apply]
  congr 1
  haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b => Fin.ext (by omega)⟩
  exact Subsingleton.elim _ _

end Work.SSS
