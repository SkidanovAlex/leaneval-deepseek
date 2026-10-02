import Mathlib
import Submission.Work.Surgery.Collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Collars do not depend on the chart structure, only on the boundary *set*

`Work.Surgery.Collar n M` is a structure on a *charted* space: its domain is
`(𝓡∂ (n+1)).boundary M × [0,∞)`, so the *type* of a collar depends on the `ChartedSpace` instance.
Two chart structures on the same space with the **same boundary set** have interchangeable collars
(`Work.ThomBordism.Collar.of_instance_congr`): a collar's fields are set-theoretic (an open embedding
whose restriction to the zero slice is the inclusion).

This is what lets a collar produced in the `Lvl` chart structure of a level set be used with the
chart structure produced by `Work.ThomBordism.levelSet_positiveAtlas_of_coframing`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Function Set Topology

namespace Work.ThomBordism

/-- **A collar transports across an equality of boundary *sets*.**  If the two chart structures on
`M` have the same boundary set, a collar for the first is a collar for the second. -/
def Collar.of_instance_congr {n : ℕ} {M : Type} [TopologicalSpace M]
    {cA cB : ChartedSpace (EuclideanHalfSpace (n + 1)) M}
    (h : @ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
            (EuclideanHalfSpace (n + 1)) _ (modelWithCornersEuclideanHalfSpace (n + 1)) M _ cA
       = @ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
            (EuclideanHalfSpace (n + 1)) _ (modelWithCornersEuclideanHalfSpace (n + 1)) M _ cB) :
    @Work.Surgery.Collar n M _ cA → @Work.Surgery.Collar n M _ cB := by
  intro c
  have hsub : @ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
      (EuclideanHalfSpace (n + 1)) _ (modelWithCornersEuclideanHalfSpace (n + 1)) M _ cB
      ⊆ @ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
      (EuclideanHalfSpace (n + 1)) _ (modelWithCornersEuclideanHalfSpace (n + 1)) M _ cA :=
    fun x hx => h.symm ▸ hx
  have hsub' : @ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
      (EuclideanHalfSpace (n + 1)) _ (modelWithCornersEuclideanHalfSpace (n + 1)) M _ cA
      ⊆ @ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
      (EuclideanHalfSpace (n + 1)) _ (modelWithCornersEuclideanHalfSpace (n + 1)) M _ cB :=
    fun x hx => h ▸ hx
  let e : (@ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
      (EuclideanHalfSpace (n + 1)) _ (modelWithCornersEuclideanHalfSpace (n + 1)) M _ cB) ≃ₜ
      (@ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
      (EuclideanHalfSpace (n + 1)) _ (modelWithCornersEuclideanHalfSpace (n + 1)) M _ cA) :=
    { toFun := Set.inclusion hsub
      invFun := Set.inclusion hsub'
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun p => Subtype.ext rfl
      continuous_toFun := IsInducing.subtypeVal.continuous_iff.mpr (by
        simpa [Function.comp_def] using continuous_subtype_val)
      continuous_invFun := IsInducing.subtypeVal.continuous_iff.mpr (by
        simpa [Function.comp_def] using continuous_subtype_val) }
  refine @Work.Surgery.Collar.mk n M _ cB
    (fun p : (@ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
        (EuclideanHalfSpace (n + 1)) _ (modelWithCornersEuclideanHalfSpace (n + 1)) M _ cB)
        × Work.Surgery.HalfLine => @Work.Surgery.Collar.toFun n M _ cA c (e p.1, p.2)) ?_ ?_
  · exact (@Work.Surgery.Collar.isOpenEmbedding n M _ cA c).comp
      (e.prodCongr (Homeomorph.refl Work.Surgery.HalfLine)).isOpenEmbedding
  · intro x
    exact @Work.Surgery.Collar.toFun_zero n M _ cA c (e x)

end Work.ThomBordism
