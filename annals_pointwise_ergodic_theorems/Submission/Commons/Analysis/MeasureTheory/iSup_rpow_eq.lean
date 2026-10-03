import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.MeasureTheory

theorem iSup_rpow_eq {ι : Type*} {q : ℝ} (hq : 0 < q) (f : ι → ENNReal) :
    (⨆ i, f i) ^ q = ⨆ i, (f i) ^ q := by
  simpa only [ENNReal.orderIsoRpow_apply] using (ENNReal.orderIsoRpow q hq).map_iSup f

end Commons.Analysis.MeasureTheory