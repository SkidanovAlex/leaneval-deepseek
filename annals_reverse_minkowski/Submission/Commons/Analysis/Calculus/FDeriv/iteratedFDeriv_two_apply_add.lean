import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.Calculus.FDeriv

open scoped Topology in
theorem iteratedFDeriv_two_apply_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x a b : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (iteratedFDeriv ℝ 2 (f + g) x) ![a, b]
      = (iteratedFDeriv ℝ 2 f x) ![a, b] + (iteratedFDeriv ℝ 2 g x) ![a, b] := by
  rw [iteratedFDeriv_add_apply hf hg, add_apply]

end Commons.Analysis.Calculus.FDeriv