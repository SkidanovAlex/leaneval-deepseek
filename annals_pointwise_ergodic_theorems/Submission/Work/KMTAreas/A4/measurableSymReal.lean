import Mathlib
import Submission.Work.KMTAreas.A4.symbolRatioDefs

namespace Work.KMTAreas.A4

/-- **Measurability of the real Ionescu–Wainger symbol.**

`Work.KMTAreas.A4.symReal ρ l k R ξ = ∑ α ∈ iwArithFreqs ρ l, ∑ j ∈ suppIdx R,
kmtBump ((val(ξ - α) + j) / 2^k)` is a finite sum of compositions of the measurable canonical
representative `ξ ↦ (AddCircle.equivIco (1 : ℝ) 0 ξ).val` (`Work.KMTAreas.A4.measurable_equivIco_val`)
with the measurable function `Work.KMTAreas.A4.bumpRescaled k`
(`Work.KMTAreas.A4.measurable_bumpRescaled`), translation being measurable, so the finite sums
(`Finset.measurable_sum`) are measurable. -/
theorem measurableSymReal (ρ : ℝ) (l : ℕ) (k : ℤ) (R : ℝ) :
    Measurable (Work.KMTAreas.A4.symReal ρ l k R) := by
  unfold symReal
  refine Finset.measurable_sum _ fun α _ => Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_bumpRescaled k).comp
    ((measurable_equivIco_val.comp (measurable_id.sub measurable_const)).add measurable_const)

end Work.KMTAreas.A4
