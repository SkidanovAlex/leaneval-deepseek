import Mathlib
import Submission.Work.TangentClasses.Tangent

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The transition functions of the tangent bundle of a product

For two smooth manifolds `M` (modelled on `(E, H)` via `I`) and `N` (modelled on `(E', H')` via
`I'`) the product `M × N` is charted on `ModelProd H H'` and modelled on `I.prod I'`.  This
module computes the transition functions (change of coordinates) of its tangent bundle: the
Jacobian of a product map is the (block diagonal) product of the Jacobians, so on the product
`M × N` the transition functions of `T(M × N)` are the Whitney-sum combinations of those of
`TM` and `TN`.

The analytic content is isolated in `fderivWithin_prodMap`: the derivative within a product set
of a product map `Prod.map f g` is the `prodMap` of the derivatives within the factors.
-/

namespace Work.TangentClasses

open Bundle
open scoped Manifold ContDiff
open Set

noncomputable section

/-- **The derivative of a product map over a product set.**
If `f` is differentiable within `s` at `x` and `g` within `t` at `y`, then `Prod.map f g` is
differentiable within `s ×ˢ t` at `(x, y)` with derivative
`(fderivWithin f s x).prodMap (fderivWithin g t y)`. -/
lemma fderivWithin_prodMap {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {f : E → F} {g : G → H} {s : Set E} {t : Set G} {x : E} {y : G}
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g t y)
    (hs : UniqueDiffWithinAt 𝕜 s x) (ht : UniqueDiffWithinAt 𝕜 t y) :
    fderivWithin 𝕜 (Prod.map f g) (s ×ˢ t) (x, y) =
      (fderivWithin 𝕜 f s x).prodMap (fderivWithin 𝕜 g t y) := by
  have hprod : HasFDerivWithinAt (Prod.map f g)
      ((fderivWithin 𝕜 f s x).prodMap (fderivWithin 𝕜 g t y)) (s ×ˢ t) (x, y) :=
    HasFDerivWithinAt.prodMap (x, y)
      (hf.hasFDerivWithinAt.mono (Set.fst_image_prod_subset s t))
      (hg.hasFDerivWithinAt.mono (Set.snd_image_prod_subset s t))
  exact hprod.fderivWithin (hs.prod ht)

/-- **Transition functions of the tangent bundle of a product.**
On `M × N` the transition function of the tangent bundle `T(M × N)` between the preferred charts
at `p` and `q`, evaluated at the point `z` of the common source, is the product (block diagonal
`prodMap`) of the transition functions of `TM` and `TN`.  This is the bundle-level form of
`T(M × N) ≅ TM ⊕ TN` and hence of `p(T(M × N)) = p(TM) · p(TN)`. -/
theorem tangentBundle_prod_coordChange {E H E' H' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
    (p q z : M × N)
    (hz : z.1 ∈ (extChartAt I p.1).source ∩ (extChartAt I q.1).source ∧
      z.2 ∈ (extChartAt I' p.2).source ∩ (extChartAt I' q.2).source) :
    (Work.TangentClasses.tangentBundle (I.prod I') (M × N)).coordChange
        (achart (ModelProd H H') p) (achart (ModelProd H H') q) z =
      (tangentCoordChange I p.1 q.1 z.1).prodMap (tangentCoordChange I' p.2 q.2 z.2) := by
  rw [Work.TangentClasses.tangentBundle_coordChange_eq_tangentCoordChange]
  rw [tangentCoordChange_def, tangentCoordChange_def, tangentCoordChange_def]
  -- The composite of the product chart transitions is the product map of the two transitions.
  have hF : (↑(extChartAt (I.prod I') q) ∘ ↑(extChartAt (I.prod I') p).symm : E × E' → E × E')
      = Prod.map (↑(extChartAt I q.1) ∘ ↑(extChartAt I p.1).symm)
                 (↑(extChartAt I' q.2) ∘ ↑(extChartAt I' p.2).symm) := by
    funext w
    simp only [Function.comp_apply, extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe]
    rfl
  rw [hF]
  have hA : extChartAt (I.prod I') p z = (extChartAt I p.1 z.1, extChartAt I' p.2 z.2) := by
    simp only [extChartAt_prod, PartialEquiv.prod_coe]
  rw [hA, ModelWithCorners.range_prod]
  -- It remains to apply the product rule for `fderivWithin` on the product set.
  refine fderivWithin_prodMap ?_ ?_ ?_ ?_
  · exact (hasFDerivWithinAt_tangentCoordChange hz.1).differentiableWithinAt
  · exact (hasFDerivWithinAt_tangentCoordChange hz.2).differentiableWithinAt
  · exact I.uniqueDiffOn _
      (extChartAt_target_subset_range p.1 ((extChartAt I p.1).map_source hz.1.1))
  · exact I'.uniqueDiffOn _
      (extChartAt_target_subset_range p.2 ((extChartAt I' p.2).map_source hz.2.1))

end

end Work.TangentClasses
