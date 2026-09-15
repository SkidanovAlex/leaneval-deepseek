import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

namespace Commons.MeasureTheory.Integral

/-- If `a ≤ b` and the topological support of `H : ℝ → ℝ` is contained in the open interval
`(a, b)`, then `H` vanishes off `(a, b)`, so its integral over `a..b` equals its integral over
the whole real line. -/
theorem intervalIntegral_eq_integral_of_tsupport_subset {H : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hH : tsupport H ⊆ Set.Ioo a b) :
    ∫ x in a..b, H x = ∫ x, H x := by
  have hzero : ∀ x, x ∉ Set.Ioo a b → H x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hH h)
  calc ∫ x in a..b, H x
      = ∫ x in Ioc a b, H x := intervalIntegral.integral_of_le hab
    _ = ∫ x in Ioo a b, H x :=
        (setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume)) (f := H)).symm
    _ = ∫ x, H x := setIntegral_eq_integral_of_forall_compl_eq_zero hzero

end Commons.MeasureTheory.Integral