import Mathlib.NumberTheory.Chebyshev

namespace Commons.NumberTheory.Chebyshev

theorem theta_measurable : Measurable Chebyshev.theta := by
  exact Chebyshev.theta_mono.measurable

end Commons.NumberTheory.Chebyshev