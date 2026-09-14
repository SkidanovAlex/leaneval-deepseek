import Mathlib
import Submission.Commons.MeasureTheory.Integral.ofReal_norm_smul_sub_le_lintegral_deriv_sq
import Submission.Commons.MeasureTheory.Integral.lintegral_Ioc_sliding_le

open MeasureTheory Set
open scoped ENNReal

set_option linter.style.haveILetI false

namespace Commons.MeasureTheory.Integral

/-- The sliding difference-quotient `L²` estimate: for an absolutely continuous curve
`f : ℝ → E` with values in a finite-dimensional real inner product space, the `L²` norm of the
sliding difference quotient `t ↦ s⁻¹ • (f (t + s) - f t)` over `(a, b - s]` is bounded by the
`L²` norm of the derivative over `(a, b]`. -/
theorem lintegral_sliding_differenceQuotient_le_of_finiteDimensional {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E} {a b s : ℝ} (hab : a ≤ b) (hs : 0 < s) (hsb : s ≤ b - a)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    (∫⁻ t in Set.Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2))
      ≤ ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv f t‖ ^ 2) := by
  have hGmeas : AEMeasurable (fun u : ℝ => ENNReal.ofReal (‖deriv f u‖ ^ 2)) volume := by
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    have hd : Measurable (deriv f) := measurable_deriv f
    have h2 : Measurable (fun u : ℝ => ‖deriv f u‖ ^ 2) :=
      (continuous_norm.pow 2).measurable.comp hd
    exact (ENNReal.measurable_ofReal.comp h2).aemeasurable
  have hpoint : ∀ t ∈ Set.Ioc a (b - s),
      ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ENNReal.ofReal s⁻¹ * ∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2) :=
    fun t ht => ofReal_norm_smul_sub_le_lintegral_deriv_sq hs ht hf
  calc (∫⁻ t in Set.Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2))
      ≤ ∫⁻ t in Set.Ioc a (b - s),
          ENNReal.ofReal s⁻¹ * ∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2) :=
        setLIntegral_mono' measurableSet_Ioc hpoint
    _ = ENNReal.ofReal s⁻¹
          * ∫⁻ t in Set.Ioc a (b - s),
              ∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal s⁻¹
          * (ENNReal.ofReal s * ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (‖deriv f u‖ ^ 2)) := by
        gcongr
        exact lintegral_Ioc_sliding_le hs (fun u => ENNReal.ofReal (‖deriv f u‖ ^ 2)) hGmeas
    _ = ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (‖deriv f u‖ ^ 2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hs.le), inv_mul_cancel₀ hs.ne',
          ENNReal.ofReal_one, one_mul]

end Commons.MeasureTheory.Integral
