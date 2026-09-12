import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.klain333_fin1

namespace Commons.Geometry.Convex.Hadwiger

/-- Transporting a valuation on `W` back to `V` along a linear isometric
equivalence `e : V ≃ₗᵢ[ℝ] W` (precomposition with `ConvexBody.imageLIE e`)
preserves the additivity, translation-invariance and simplicity clauses
that do not involve an ambient isometry group. -/
theorem imageLIE_admissible
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (μ : ConvexBody W → ℝ)
    (hadd : ∀ A B C D : ConvexBody W,
        (A : Set W) = (C : Set W) ∪ (D : Set W) →
        (B : Set W) = (C : Set W) ∩ (D : Set W) → μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody W, ∀ t : W,
        (B : Set W) = (fun x : W => x + t) '' (A : Set W) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody W, interior (K : Set W) = ∅ → μ K = 0) :
    (∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) →
        μ (ConvexBody.imageLIE e A) + μ (ConvexBody.imageLIE e B) =
          μ (ConvexBody.imageLIE e C) + μ (ConvexBody.imageLIE e D)) ∧
    (∀ A B : ConvexBody V, ∀ t : V,
        (B : Set V) = (fun x : V => x + t) '' (A : Set V) →
        μ (ConvexBody.imageLIE e A) = μ (ConvexBody.imageLIE e B)) ∧
    (∀ K : ConvexBody V, interior (K : Set V) = ∅ → μ (ConvexBody.imageLIE e K) = 0) := by
  constructor
  · intro A B C D hU hI
    have hU' : (ConvexBody.imageLIE e A : Set W) =
        (ConvexBody.imageLIE e C : Set W) ∪ (ConvexBody.imageLIE e D : Set W) := by
      rw [imageLIE_apply, imageLIE_apply, imageLIE_apply, hU, Set.image_union]
    have hI' : (ConvexBody.imageLIE e B : Set W) =
        (ConvexBody.imageLIE e C : Set W) ∩ (ConvexBody.imageLIE e D : Set W) := by
      rw [imageLIE_apply, imageLIE_apply, imageLIE_apply, hI,
        Set.image_inter e.injective]
    exact hadd (ConvexBody.imageLIE e A) (ConvexBody.imageLIE e B)
      (ConvexBody.imageLIE e C) (ConvexBody.imageLIE e D) hU' hI'
  constructor
  · intro A B t hB
    apply htrans (ConvexBody.imageLIE e A) (ConvexBody.imageLIE e B) (e t)
    rw [imageLIE_apply, imageLIE_apply, hB]
    exact lie_image_translate (e := e) (A := (A : Set V)) (t := t)
  · intro K hK
    apply hsimple
    rw [imageLIE_apply]
    rw [lie_image_interior (e := e) (A := (K : Set V))]
    rw [hK]
    simp

end Commons.Geometry.Convex.Hadwiger
