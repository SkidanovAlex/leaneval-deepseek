import Mathlib
import Submission.Work.Diff.EXT.ricJetDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart matrix of a Riemannian metric is positive definite

For a smooth Riemannian metric `g : SMet I M`, a chart centre `x₀` and a point `p` in the chart at
`x₀`, the Gram matrix of the coordinate frame of the chart at `p`

`Work.Diff.EXT.gmat g x₀ p i j = g.inner p (frameVector I x₀ p (bB i)) (frameVector I x₀ p (bB j))`

is positive definite.

This is the fact that makes the deTurck trick workable: it is exactly what is needed to invert the
chart matrix (the coordinate frame is a basis of the tangent space, so the Gram matrix of a
Riemannian metric in it is non-degenerate, indeed positive definite).

The proof is pure linear algebra, independent of the manifold structure beyond the fact that the
coordinate frame is *injective*: the coordinate map
`c ↦ frameVector I x₀ p c` is `symmL` of the tangent-bundle trivialization at `x₀`, whose left
inverse is `continuousLinearMapAt` (valid at every point of the base set of the trivialization, i.e.
on the chart source).

* `posDef_gram_of_injective` (proved below) is the general linear-algebra core: for a positive
  definite bilinear form `B` on a module `V` and an injective linear map `L : E →ₗ V`, the matrix
  `i j ↦ B (L eᵢ) (L eⱼ)` of `B` in the image of the canonical basis is positive definite.  It is a
  `PosDef`-valued version of `Work.Diff.EXT.gram_det_ne_zero_linearEquiv` (which only concludes that
  the determinant is non-zero); we work with the quadratic form of `B` pulled back along `L` and
  the characterization `LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix` of positive
  definiteness of a bilinear form by the positive definiteness of its matrix in any basis.
-/

set_option linter.unusedSectionVars false

open scoped Bundle Manifold ContDiff Topology
open Bundle

namespace Work.Diff.STE.deTurck

/-- **Gram matrices of a positive definite bilinear form along an injective linear map are positive
definite.**

If `L : E →ₗ[ℝ] V` is injective and `B` is a symmetric positive definite bilinear form on `V`, then
the matrix `i j ↦ B (L (finBasis i)) (L (finBasis j))` is positive definite.

Note the hypotheses on `V`: only the structures that the `inner` field of a Riemannian metric
requires (`AddCommGroup`, `Module ℝ`, `TopologicalSpace`, `IsTopologicalAddGroup`,
`ContinuousConstSMul ℝ`) — in particular *no* `NormedAddCommGroup`, which the tangent space
`TangentSpace I p` does not carry in general. -/
lemma posDef_gram_of_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
      [ContinuousConstSMul ℝ V]
    (L : E →ₗ[ℝ] V) (hL : Function.Injective L)
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v w : V, B v w = B w v) (hpos : ∀ v : V, v ≠ 0 → 0 < B v v) :
    (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      B (L (Module.finBasis ℝ E i)) (L (Module.finBasis ℝ E j)))).PosDef := by
  classical
  -- The pull-back of `B` along `L`, as a bilinear form on the model space `E`.
  let Bₗ : LinearMap.BilinForm ℝ E := LinearMap.mk₂ ℝ (fun ξ η => B (L ξ) (L η))
    (fun ξ η ζ => by simp) (fun c ξ η => by simp) (fun ξ η ζ => by simp) (fun c ξ η => by simp)
  have hBₗ_apply : ∀ ξ η : E, Bₗ ξ η = B (L ξ) (L η) := fun ξ η => by
    simp [Bₗ, LinearMap.mk₂_apply]
  -- `Bₗ` is symmetric and positive definite, because `B` is and `L` is injective.
  have hBₗsymm : Bₗ.IsSymm := LinearMap.BilinForm.IsSymm.mk (fun ξ η => by
    rw [hBₗ_apply, hBₗ_apply]; exact hsymm _ _)
  have hquad : Bₗ.toQuadraticMap.PosDef := by
    intro ξ hξ
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hBₗ_apply]
    exact hpos _ (fun h => hξ (hL (by simpa using h)))
  -- The matrix in the statement is exactly the matrix of `Bₗ` in the canonical basis.
  have hmat : (LinearMap.BilinForm.toMatrix (Module.finBasis ℝ E)) Bₗ =
      Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        B (L (Module.finBasis ℝ E i)) (L (Module.finBasis ℝ E j))) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.of_apply, hBₗ_apply]
  rw [← hmat]
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix (Module.finBasis ℝ E) Bₗ
    hBₗsymm).mp hquad

theorem posDef_gmat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) :
    (Matrix.of (Work.Diff.EXT.gmat (I := I) g x₀ p)).PosDef := by
  -- `p` lies in the base set of the trivialization of the tangent bundle at `x₀`.
  have hp' : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hp
  -- The coordinate map `c ↦ symmL c` is injective, its left inverse being `continuousLinearMapAt`.
  have hL : Function.Injective
      ((trivializationAt E (TangentSpace I) x₀).symmL ℝ p).toLinearMap := by
    intro a b hab
    have hab' : (trivializationAt E (TangentSpace I) x₀).symmL ℝ p a
        = (trivializationAt E (TangentSpace I) x₀).symmL ℝ p b := hab
    have h := congrArg ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p) hab'
    simpa only [Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) hp' a,
      Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) hp' b] using h
  -- Unfold the chart matrix and the coordinate frame.
  rw [show Work.Diff.EXT.gmat (I := I) g x₀ p
      = (fun i j => ((g.inner p) ((trivializationAt E (TangentSpace I) x₀).symmL ℝ p
            ((Module.finBasis ℝ E) i)))
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ p ((Module.finBasis ℝ E) j))) from by
    funext i j
    rw [Work.Diff.EXT.gmat, Work.Diff.EXT.fvec, Submission.Geodesic.frameVector]
    rfl]
  exact posDef_gram_of_injective _ hL (g.inner p) (g.symm p) (g.pos p)

end Work.Diff.STE.deTurck
