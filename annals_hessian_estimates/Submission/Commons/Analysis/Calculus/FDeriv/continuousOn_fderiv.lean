import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace Commons.Analysis.Calculus.FDeriv

theorem continuousOn_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F} {s : Set E}
    (hs : IsOpen s) (hu : ContDiffOn ℝ 1 u s) : ContinuousOn (fderiv ℝ u) s :=
  hu.continuousOn_fderiv_of_isOpen hs le_rfl

end Commons.Analysis.Calculus.FDeriv