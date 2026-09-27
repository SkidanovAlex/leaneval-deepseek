import Mathlib
import Submission.Work.Whitney.DoubleDetC

/-!
# Re-parametrising a double point by a linear map fixing the image point

If `Ψ` has a double point at the parameters `u, v` (i.e. `Ψ u = Ψ v`), `S` is a continuous linear
map fixing `Ψ u`, and `H` is differentiable at `Ψ u`, then the signed determinant of the double
point of `H ∘ S ∘ Ψ` at `(u, v)` is `det S` times the signed determinant of the double point of
`H ∘ Ψ`.

This is the linear-bookkeeping step of the Whitney cancellation: composing the ambient map with a
linear automorphism (or any endomorphism) scales the local intersection number of the two sheets
by the determinant.

The mathematical content is that both derivatives `D(H ∘ S ∘ Ψ)(u)` and `D(H ∘ S ∘ Ψ)(v)` factor
as `(DH(Ψ u)) ∘ S ∘ (DΨ)`, so the two-sheet linear map is
`(pairEquiv n) ∘ DH(Ψ u) ∘ S ∘ ((DΨ u) coprod (DΨ v))`, and the determinant is multiplicative.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- `coprod` composed with a common linear map on the left: the two-sheet map of `H ∘ S ∘ Ψ`
factors through the two-sheet map of `S ∘ Ψ`. -/
private lemma coprod_comp_comp {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)))
    (S : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    (L.comp (S.comp A)).coprod (L.comp (S.comp B)) = (L.comp S).comp (A.coprod B) := by
  rw [← ContinuousLinearMap.comp_coprod L (S.comp A) (S.comp B),
      ← ContinuousLinearMap.comp_coprod S A B, ContinuousLinearMap.comp_assoc]

/-- The purely linear-algebraic core: inserting `S` into the two-sheet data multiplies the
signed determinant by `det S`. -/
private lemma doubleDetRep_comp_clm_aux {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)))
    (S : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    LinearMap.det ((Work.Projection.pairEquiv n).toLinearMap.comp
        (((L.comp (S.comp A)).coprod (L.comp (S.comp B))).toLinearMap))
      = LinearMap.det S.toLinearMap *
        LinearMap.det ((Work.Projection.pairEquiv n).toLinearMap.comp
          (((L.comp A).coprod (L.comp B)).toLinearMap)) := by
  set pairE : EuclideanSpace ℝ (Fin (2 * n)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    (Work.Projection.pairEquiv n).toLinearMap with hpairE
  set G : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) := pairE.comp L.toLinearMap with hG
  set M : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) := (A.coprod B).toLinearMap with hM
  have h1 : pairE.comp (((L.comp (S.comp A)).coprod (L.comp (S.comp B))).toLinearMap)
      = G.comp (S.toLinearMap.comp M) := by
    rw [coprod_comp_comp L S A B, ContinuousLinearMap.toLinearMap_comp,
        ContinuousLinearMap.toLinearMap_comp, hG, hM]
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, LinearMap.comp_assoc]
  have h2 : pairE.comp (((L.comp A).coprod (L.comp B)).toLinearMap)
      = G.comp M := by
    rw [← ContinuousLinearMap.comp_coprod L A B, ContinuousLinearMap.toLinearMap_comp, hG, hM,
        LinearMap.comp_assoc]
  rw [h1, h2, LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_comp]
  ring

/-- **Re-parametrising a double point by a linear endomorphism fixing the image point.** -/
theorem doubleDetRep_comp_clm {n : ℕ}
    (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)))
    (S : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (u v : EuclideanSpace ℝ (Fin n))
    (huv : Ψ u = Ψ v) (hz : S (Ψ u) = Ψ u)
    (hH : DifferentiableAt ℝ H (Ψ u))
    (hΨu : DifferentiableAt ℝ Ψ u) (hΨv : DifferentiableAt ℝ Ψ v) :
    doubleDetRep (fun x => H (S (Ψ x))) u v
      = LinearMap.det S.toLinearMap * doubleDetRep (fun x => H (Ψ x)) u v := by
  have hH' : DifferentiableAt ℝ H (S (Ψ u)) := by rw [hz]; exact hH
  have hSv : S (Ψ v) = Ψ u := by rw [← huv]; exact hz
  have hH'' : DifferentiableAt ℝ H (S (Ψ v)) := by rw [hSv]; exact hH
  have hHv : DifferentiableAt ℝ H (Ψ v) := by rw [← huv]; exact hH
  have hdiffu : DifferentiableAt ℝ (fun x => S (Ψ x)) u := S.differentiableAt.comp u hΨu
  have hdiffv : DifferentiableAt ℝ (fun x => S (Ψ x)) v := S.differentiableAt.comp v hΨv
  have hfu : fderiv ℝ (fun x => H (S (Ψ x))) u
      = (fderiv ℝ H (Ψ u)).comp (S.comp (fderiv ℝ Ψ u)) := by
    rw [fderiv_fun_comp u hH' hdiffu, fderiv_fun_comp u S.differentiableAt hΨu, hz,
        ContinuousLinearMap.fderiv]
  have hfv : fderiv ℝ (fun x => H (S (Ψ x))) v
      = (fderiv ℝ H (Ψ u)).comp (S.comp (fderiv ℝ Ψ v)) := by
    rw [fderiv_fun_comp v hH'' hdiffv, fderiv_fun_comp v S.differentiableAt hΨv, hSv,
        ContinuousLinearMap.fderiv]
  have hgu : fderiv ℝ (fun x => H (Ψ x)) u
      = (fderiv ℝ H (Ψ u)).comp (fderiv ℝ Ψ u) := by
    rw [fderiv_fun_comp u hH hΨu]
  have hgv : fderiv ℝ (fun x => H (Ψ x)) v
      = (fderiv ℝ H (Ψ u)).comp (fderiv ℝ Ψ v) := by
    rw [fderiv_fun_comp v hHv hΨv, ← huv]
  rw [doubleDetRep, doubleDetRep, hfu, hfv, hgu, hgv]
  exact doubleDetRep_comp_clm_aux (fderiv ℝ H (Ψ u)) S (fderiv ℝ Ψ u) (fderiv ℝ Ψ v)

end Work.Whitney
