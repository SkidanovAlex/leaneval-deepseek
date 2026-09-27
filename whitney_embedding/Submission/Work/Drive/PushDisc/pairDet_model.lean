import Mathlib
import Submission.Work.Whitney.PairDet
import Submission.Work.Drive.PushDisc.asymSignDefs

/-!
# `Work.Drive.PushDisc.pairDet_model`: the two-chart crossing sign in the model coordinates

The sign derivation of the one-sided normal form computes the two crossing signs of a Whitney bigon
in the *model* coordinates.  In those coordinates the two jets of `f` at the two preimages are
obtained by transporting one common jet `dΘ` of the ambient chart through the two linear maps
`A`, `B` (the model parametrisations of the two sheets), so both are of the form `T.comp A` and
`T.comp B` for a single `T` (the reading of the model jet in the `ℝ^{2(k+1)}`-coordinates of `f`).

This lemma is the bookkeeping step: under that factorisation the two-chart determinant
`Work.Whitney.pairDet` is exactly the determinant of `pairEquiv (k+1) ∘ (T.comp (A.coprod B))`.
It is a pure linear-algebra computation: `toLinearMap` of a `ContinuousLinearMap.coprod` is the
`LinearMap.coprod` of the `toLinearMap`s, and `T.comp` distributes over `LinearMap.coprod`
(`LinearMap.comp_coprod`).
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff

theorem pairDet_model {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (T : Work.Drive.Whitney.Mdl k →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (a b : M)
    (A B : EuclideanSpace ℝ (Fin (k + 1)) →ₗ[ℝ] Work.Drive.Whitney.Mdl k)
    (hA : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c₁.symm u)) (c₁ a)).toLinearMap
      = T.comp A)
    (hB : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c₂.symm u)) (c₂ b)).toLinearMap
      = T.comp B) :
    Work.Whitney.pairDet f c₁ c₂ a b =
      LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
        (T.comp (A.coprod B))) := by
  -- The common `toLinearMap`-factorisation of the coproduct of the two jets.
  have hcoprod :
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c₁.symm u)) (c₁ a)).coprod
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c₂.symm u)) (c₂ b))).toLinearMap
      = T.comp (A.coprod B) := by
    -- `toLinearMap` of a `ContinuousLinearMap.coprod` is the `LinearMap.coprod` of the parts.
    show (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c₁.symm u)) (c₁ a)).toLinearMap.coprod
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c₂.symm u)) (c₂ b)).toLinearMap
      = T.comp (A.coprod B)
    rw [hA, hB, LinearMap.comp_coprod]
  unfold Work.Whitney.pairDet
  rw [hcoprod]

end Work.Drive.PushDisc
