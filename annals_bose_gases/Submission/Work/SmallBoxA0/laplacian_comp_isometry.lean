import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.InnerProductSpace.Laplacian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

/--
Chain rule for the second iterated derivative under right-composition with a linear isometry
equivalence: the second derivative of `fun y => f (A y)` at `x` is the second derivative of `f`
at `A x`, precomposed (in every slot) with `A`.
-/
lemma iteratedFDeriv_two_comp_linearIsometryEquiv
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3))
    (hf : ContDiff ℝ 2 f) :
    iteratedFDeriv ℝ 2 (fun y => f (A y)) x =
      (iteratedFDeriv ℝ 2 f (A x)).compContinuousLinearMap
        (fun _ => (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))) := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ)
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) hf x
    (by norm_num : (2 : ℕ) ≤ (2 : WithTop ℕ∞))
  simpa [Function.comp_def] using h

/-- The Laplacian is invariant under precomposition with a linear isometry equivalence. -/
lemma laplacian_comp_isometry
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ) (hφ : ContDiff ℝ 2 φ) :
    Laplacian.laplacian (fun x => φ (A x)) =
      fun x => (Laplacian.laplacian φ) (A x) := by
  funext x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (fun x => φ (A x)),
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
        ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 3))).map A)]
  apply Finset.sum_congr rfl
  intro i _
  rw [OrthonormalBasis.map_apply, iteratedFDeriv_two_comp_linearIsometryEquiv A φ x hφ]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

end Work.SmallBoxA0
