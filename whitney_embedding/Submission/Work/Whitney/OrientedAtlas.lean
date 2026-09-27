import Mathlib
import Submission.Work.Whitney.PairDet

/-!
# Oriented atlases, and the sign comparison of two double points

A cover of `M` by charts whose pairwise transition maps have *positive* Jacobian determinant is the
data of a global orientation of `M` (assume `M` connected, or work componentwise).  Such a cover
`A` makes the *sign* of the `pairDet`-comparison of two double points canonical: the charts of `A`
give trivialisations of the tangent bundle which are all positively related, so the sign of

`pairDet f c₁ c₂ p₁ p₂ * pairDet f c₃ c₄ q₁ q₂`

(where `c₁, c₂, c₃, c₄ ∈ A` are charts at `p₁, p₂, q₁, q₂`) does not depend on the choice of the
four charts.  This is the sign comparison that the Whitney cancellation needs: it is an intrinsic
geometric datum (the framing condition of the bigon), expressible as an explicit real number, so
that an endgame can case-split on its sign, while the cancellation lemma can take it as a
hypothesis.

`Work.Whitney.IsOrientedAtlas` is the cover-with-positive-transitions condition, and
`Work.Whitney.pairDet_sign_eq_of_orientedAtlas` is the chart-independence of the comparison.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- **An oriented atlas**: a family of charts covering `M` such that any two of its charts have
transition map with positive Jacobian determinant at every point of the overlap. -/
def IsOrientedAtlas {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))) : Prop :=
  (∀ x : M, ∃ c ∈ A, x ∈ c.source) ∧
  (∀ c₁ ∈ A, ∀ c₂ ∈ A, ∀ x : M, x ∈ c₁.source → x ∈ c₂.source →
    0 < (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₂ (c₁.symm u)) (c₁ x)).det)

/-- **The two double points `(p₁,p₂)` and `(q₁,q₂)` have opposite signs**, relative to the
orientation given by the atlas `A`: some (equivalently, by
`Work.Whitney.oppositeSign_iff`, every) choice of charts of `A` at the four points makes the
product of the two two-chart signed determinants negative. -/
def OppositeSign {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ q₁ q₂ : M) : Prop :=
  ∃ (c₁ c₂ c₃ c₄ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    c₁ ∈ A ∧ c₂ ∈ A ∧ c₃ ∈ A ∧ c₄ ∈ A ∧
    p₁ ∈ c₁.source ∧ p₂ ∈ c₂.source ∧ q₁ ∈ c₃.source ∧ q₂ ∈ c₄.source ∧
    pairDet f c₁ c₂ p₁ p₂ * pairDet f c₃ c₄ q₁ q₂ < 0

end Work.Whitney
