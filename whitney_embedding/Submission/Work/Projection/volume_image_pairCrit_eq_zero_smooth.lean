import Mathlib
import Submission.Work.Projection.TransverseDefs
import Submission.Work.Projection.isOpen_pairDom_smooth
import Submission.Work.Projection.contDiffOn_pairParam_smooth

set_option linter.style.haveILetI false

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

/-- The image of the critical set of the pair parametrisation `Work.Projection.pairParam e p q`
(defined in `Submission.Work.Projection.TransverseDefs` with the *smooth* (`C^∞`) manifold
structure, i.e. the order `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`; the critical set is
`Work.Projection.pairCrit e p q`) has measure zero.  This is the equal-dimension case of Sard
applied to the parametrisation.  It is identical to `Work.Projection.volume_image_pairCrit_eq_zero`
in `Submission.Work.Projection.volume_image_pairCrit_eq_zero` except that the hypothesis is
smoothness rather than analyticity.  The measure is the Lebesgue (= product Haar) measure on the
model space `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` of `M × M`. -/
theorem volume_image_pairCrit_eq_zero_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p q : M) :
    MeasureTheory.volume (pairParam e p q '' pairCrit e p q) = 0 := by
  -- The Lebesgue measure on the product `ℝ^n × ℝ^n` is the product of the Lebesgue measures of
  -- the factors, hence an additive Haar measure.
  haveI hhaar : Measure.IsAddHaarMeasure
      (volume : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  -- The equal-dimension case of Sard's lemma, applied to the parametrisation on its (open) domain.
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
    (s := pairCrit e p q) (f := pairParam e p q)
    (f' := fun ab => fderiv ℝ (pairParam e p q) ab) ?_ ?_
  · -- `pairParam` is differentiable at every point of its domain, and `pairCrit ⊆ pairDom`.
    intro x hx
    have hxdom : x ∈ pairDom e p q := hx.1
    have hdiff : DifferentiableAt ℝ (pairParam e p q) x :=
      ((contDiffOn_pairParam_smooth e he p q).differentiableOn_one).differentiableAt
        ((isOpen_pairDom_smooth e he p q).mem_nhds hxdom)
    exact hdiff.hasFDerivAt.hasFDerivWithinAt
  · -- The critical set is by definition the set where the determinant vanishes.
    intro x hx
    exact hx.2

end Work.Projection
