import Mathlib
import Submission.Work.Whitney.OrientedAtlas
import Submission.Work.Whitney.oppositeSign_iff
import Submission.Work.Whitney.PairDet

namespace Work.Whitney

/-- **The sign comparison of two double points, read in a single chart of an oriented atlas.**

`Work.Whitney.OppositeSign A f p₁ p₂ q₁ q₂` asks that *some* quadruple of charts of the oriented
atlas `A`, containing the four points, makes the product of the two two-chart determinants
negative.  `Work.Whitney.oppositeSign_iff` shows this is equivalent to the same inequality for
*every* such quadruple; evaluating it at the quadruple `(c, c, c, c)` and using
`Work.Whitney.pairDet_self` (which says `pairDet f c c a b = doubleDetC f c a b` by definition)
turns that into the single-chart criterion `doubleDetC f c p₁ p₂ * doubleDetC f c q₁ q₂ < 0`.

This is the form in which the sign bookkeeping is actually used: the relative sign of two double
points is measured in one fixed chart `c ∈ A` containing all four points, so that the two sheets at
`p₁` and `p₂` (resp. `q₁` and `q₂`) are seen through a common trivialisation and the numbers are
directly comparable. -/
theorem oppositeSign_iff_doubleDetC {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : Work.Whitney.IsOrientedAtlas A)
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ q₁ q₂ : M)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hc : c ∈ A)
    (hp₁ : p₁ ∈ c.source) (hp₂ : p₂ ∈ c.source) (hq₁ : q₁ ∈ c.source) (hq₂ : q₂ ∈ c.source) :
    Work.Whitney.OppositeSign A f p₁ p₂ q₁ q₂ ↔
      Work.Whitney.doubleDetC f c p₁ p₂ * Work.Whitney.doubleDetC f c q₁ q₂ < 0 := by
  have h := Work.Whitney.oppositeSign_iff (n := n) (M := M) A hA f p₁ p₂ q₁ q₂ c c c c
    hc hc hc hc hp₁ hp₂ hq₁ hq₂
  rw [Work.Whitney.pairDet_self, Work.Whitney.pairDet_self] at h
  exact h.symm

end Work.Whitney
