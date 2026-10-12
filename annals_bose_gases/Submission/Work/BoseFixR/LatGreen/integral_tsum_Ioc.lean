import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.BoseFixR.LatGreen.Theta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

/-- Tonelli-type exchange of an integral over `Ioc 0 η` with a series of nonnegative
integrable functions, granted that the series of integrals is summable.

The proof reduces the supremum condition of `MeasureTheory.integral_tsum` to the given
summability hypothesis: for each `i` the extended-norm integral `∫⁻ t, ‖F i t‖ₑ` is
`ENNReal.ofReal` of the ordinary integral of `F i` (nonnegativity of `F i`), and a summable
real series has `ENNReal.ofReal`-sum not equal to `⊤`. -/
theorem integral_tsum_Ioc {ι : Type*} [Countable ι] {η : ℝ} (hη : 0 < η)
    {F : ι → ℝ → ℝ} (hnn : ∀ i t, 0 ≤ F i t)
    (hint : ∀ i, MeasureTheory.IntegrableOn (F i) (Set.Ioc 0 η))
    (hsum : Summable fun i => ∫ t in Set.Ioc 0 η, F i t) :
    ∫ t in Set.Ioc 0 η, (∑' i, F i t) = ∑' i, ∫ t in Set.Ioc 0 η, F i t := by
  have hAESM : ∀ i, MeasureTheory.AEStronglyMeasurable (F i)
      (MeasureTheory.volume.restrict (Set.Ioc 0 η)) :=
    fun i => (hint i).aestronglyMeasurable
  have h1 : ∀ i, ∫⁻ t, ‖F i t‖ₑ ∂(MeasureTheory.volume.restrict (Set.Ioc 0 η))
      = ENNReal.ofReal (∫ t in Set.Ioc 0 η, F i t) := fun i => by
    rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hint i)]
    congr 1
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t => Real.norm_of_nonneg (hnn i t))
  have hlin : (∑' i, ∫⁻ t, ‖F i t‖ₑ ∂(MeasureTheory.volume.restrict (Set.Ioc 0 η))) ≠ ⊤ := by
    rw [tsum_congr h1]
    exact hsum.tsum_ofReal_ne_top
  exact MeasureTheory.integral_tsum hAESM hlin

end Work.BoseFixR.LatGreen
