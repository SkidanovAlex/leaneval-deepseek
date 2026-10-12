import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory

/-- A function `u` on `ℝ` which is such that `t ↦ t * u t` is integrable on the interval
`(0, R)` admits a strongly measurable representative (a.e. equal to it on that interval).
Indeed, on `(0, R)` the point `0` is the only point where division by `t` can fail, and it is
not in the interval, so `u` agrees a.e. there with `(t * u t) * t⁻¹`. -/
theorem ae_stronglyMeasurable_rep {R : ℝ} {u : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn (fun t : ℝ => t * u t) (Set.Ioo (0 : ℝ) R)) :
    ∃ u' : ℝ → ℝ, MeasureTheory.StronglyMeasurable u' ∧
      u' =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioo (0 : ℝ) R)] u := by
  have h1 : AEStronglyMeasurable (fun t : ℝ => t * u t)
      (Measure.restrict volume (Set.Ioo (0 : ℝ) R)) := hu.aestronglyMeasurable
  have hinv : AEStronglyMeasurable (fun t : ℝ => t⁻¹)
      (Measure.restrict volume (Set.Ioo (0 : ℝ) R)) := measurable_inv.aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun t : ℝ => (t * u t) * t⁻¹)
      (Measure.restrict volume (Set.Ioo (0 : ℝ) R)) := h1.mul hinv
  have h3 : (fun t : ℝ => (t * u t) * t⁻¹)
      =ᵐ[Measure.restrict volume (Set.Ioo (0 : ℝ) R)] u := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with t ht
    rw [mul_comm t (u t), mul_inv_cancel_right₀ (ne_of_gt ht.1) (u t)]
  have h4 : AEStronglyMeasurable u (Measure.restrict volume (Set.Ioo (0 : ℝ) R)) := h2.congr h3
  exact ⟨h4.mk, h4.stronglyMeasurable_mk, h4.ae_eq_mk.symm⟩

end Work.SmallBoxA0
