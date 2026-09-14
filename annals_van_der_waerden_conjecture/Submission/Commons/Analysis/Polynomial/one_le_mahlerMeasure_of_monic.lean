import Mathlib.Analysis.Polynomial.MahlerMeasure

namespace Commons.Analysis.Polynomial

theorem one_le_mahlerMeasure_of_monic {p : Polynomial ℂ} (hp : p.Monic) :
    1 ≤ p.mahlerMeasure := by
  exact Polynomial.one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
    (by rw [hp.leadingCoeff, norm_one])

end Commons.Analysis.Polynomial