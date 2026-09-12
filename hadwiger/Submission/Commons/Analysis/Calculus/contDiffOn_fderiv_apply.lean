import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace Commons.Analysis.Calculus

theorem contDiffOn_fderiv_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → F}
    (hf : ContDiffOn ℝ ⊤ f s) (hs : IsOpen s) (v : E) :
    ContDiffOn ℝ ⊤ (fun y : E => fderiv ℝ f y v) s := by
  exact (ContinuousLinearMap.apply ℝ F v).contDiff.fun_comp_contDiffOn
    (hf.fderiv_of_isOpen hs (m := ⊤) le_top)

end Commons.Analysis.Calculus