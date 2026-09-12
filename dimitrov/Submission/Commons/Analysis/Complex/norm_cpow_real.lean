import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Complex

lemma norm_cpow_real {w : ℂ} {t : ℝ} : ‖w ^ (t : ℂ)‖ = ‖w‖ ^ t := by
  exact _root_.Complex.norm_cpow_real w t

end Commons.Analysis.Complex
