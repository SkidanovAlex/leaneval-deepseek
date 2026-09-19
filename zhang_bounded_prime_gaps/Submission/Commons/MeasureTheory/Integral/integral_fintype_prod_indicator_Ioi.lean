import Mathlib.MeasureTheory.Integral.Pi

namespace Commons.MeasureTheory.Integral

/-- Fubini over a product of halflines: the integral of a product of one-variable
functions against the orthant indicator factorises. -/
theorem integral_fintype_prod_indicator_Ioi {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, MeasureTheory.Integrable ((Set.Ioi (0:ℝ)).indicator (f i))) :
    ∫ x : ι → ℝ, ∏ i, (Set.Ioi (0:ℝ)).indicator (f i) (x i)
      = ∏ i, ∫ t in Set.Ioi (0:ℝ), f i t := by
  rw [_root_.MeasureTheory.integral_fintype_prod_volume_eq_prod
    (fun i => (Set.Ioi (0:ℝ)).indicator (f i))]
  exact Finset.prod_congr rfl fun i _ => _root_.MeasureTheory.integral_indicator measurableSet_Ioi

end Commons.MeasureTheory.Integral