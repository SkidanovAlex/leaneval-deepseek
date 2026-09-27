import Mathlib
import Submission.Work.Whitney.DoublePoint
import Submission.Work.Whitney.OrientedAtlas

/-!
# The "one inserted double point" step, as a predicate

This file isolates the *interface* of the insertion step of Whitney's endgame
(`Work.Whitney.exists_addDoublePoint_oriented`, whose proof performs it, and
`Work.Whitney.exists_insertedDoublePoint`, which also produces the chart and clean-ball data
needed to *locate* the inserted double point).

The predicate `Work.Whitney.InsertedDoublePoint f A p₁ p₂ f' p' q'` collects everything the
cancellation step (`Work.Whitney.cancel_double_points_oriented`) needs to know about the modified
map `f'`: it is a smooth immersion whose double point set is that of `f` together with the single
new (ordered) pair `(p', q')`, both double points `(p₁,p₂)` and `(p',q')` are *simple* (their
values have exactly two preimages), and the new point is of the *opposite sign* to `(p₁,p₂)`
relative to the oriented atlas `A`.

Keeping the locatedness data (`‖c p'‖ < R`, `‖c q'‖ < R` and the eventual radius conditions at
`p₁`, `p₂`) inside the proof of `exists_insertedDoublePoint` rather than in this predicate makes
the reduction lemma `Work.Whitney.exists_reduce_double_points_abstract` depend only on the
*geometric* content of the insertion, and not on the choice of the auxiliary chart `c`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- **A single double point inserted into `f`.**  All the data the Whitney cancellation needs about
the map `f'` obtained from `f` by gluing in the model at a clean point. -/
structure InsertedDoublePoint {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (p₁ p₂ : M) (f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M) : Prop where
  contMDiff : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f'
  injective_mfderiv : ∀ y, Function.Injective
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f' y)
  doubleSet_eq : doubleSet f' = doubleSet f ∪ {(p', q'), (q', p')}
  oppositeSign : OppositeSign A f' p₁ p₂ p' q'
  finite_doubleSet : (doubleSet f').Finite
  simple_new : ∀ z : M, f' z = f' p' → z = p' ∨ z = q'
  simple_old : ∀ z : M, f' z = f' p₁ → z = p₁ ∨ z = p₂
  distinct : p' ≠ q' ∧ p' ≠ p₁ ∧ p' ≠ p₂ ∧ q' ≠ p₁ ∧ q' ≠ p₂ ∧ p₁ ≠ p₂
  new_not_old : (p', q') ∉ doubleSet f

end Work.Whitney
