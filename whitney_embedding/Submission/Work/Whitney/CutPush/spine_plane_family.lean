import Mathlib
import Submission.Work.Whitney.CutPush.spine_unknotting
import Submission.Work.Whitney.CutPush.localised_projection_family

/-!
# The plane field of the straightened sheet along the spine

Third brick of the tube-flattening assembly (`CutPush/NOTES_STATE_S61.md` §2): after `A₁` has
straightened the spine's chord (`CutPush/spine_unknotting.lean`), the tangent `n`-plane field of the
*straightened sheet* `A₁ ∘ f` along `δ` is a smooth family of orthogonal projections
(`exists_localised_projection_family`, applied with `F := A₁ ∘ f`), on an open set containing
`[-1, 2]` so that the frame transport has room around the collar's height range `[0, 1]`.
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology Set

/-- **The plane field of the straightened sheet along the spine.** -/
theorem exists_plane_family_of_spine {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [LocallyCompactSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hAi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv)
    (hlinv : Function.LeftInverse Ainv A)
    (δ : ℝ → M)
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ) :
    ∃ (P : ℝ → EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))
      (W : Set ℝ),
      IsOpen W ∧ Set.Icc (-1 : ℝ) 2 ⊆ W ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin (2 * n)) => P p.1 p.2) ∧
      (∀ t ∈ W, P t * P t = P t) ∧
      (∀ t ∈ W, ∀ x y : EuclideanSpace ℝ (Fin (2 * n)),
        inner ℝ (P t x) y = inner ℝ x (P t y)) ∧
      (∀ t ∈ W, LinearMap.range (P t : EuclideanSpace ℝ (Fin (2 * n)) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))
        = LinearMap.range ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
            (fun y : M => A (f y)) (δ t)
            : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).toLinearMap)) := by
  have hAF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => A (f y)) := hA.contMDiff.comp hf
  have hAFinj : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (fun z => A (f z)) y) :=
    mfderiv_comp_injective f hf himm A Ainv hA hAi hlinv
  have hab : (-1 : ℝ) ≤ 2 := by norm_num
  exact exists_localised_projection_family (fun y : M => A (f y)) hAF hAFinj hδ (-1) 2 hab

end Work.Whitney.CutPush
