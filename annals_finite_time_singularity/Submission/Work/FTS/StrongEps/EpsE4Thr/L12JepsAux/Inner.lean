import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.Basic
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open Work.FTS.StrongEps (Jeps Jker zShift thShift IsMollKernel IsSmoothKernel
  epsRHSP IsEpsSolP abs_Jeps_le_sup Jeps_eq_zero)
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux

set_option autoImplicit false

/-- `K` is continuous. -/
lemma continuous_K : Continuous Work.Spaces.K := by
  show Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

/-- The angular weight of `L₁₂` is bounded by `3` on the whole line (in particular on `Iθ`). -/
lemma abs_K_le (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h2 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ]
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_sq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [abs_nonneg (Real.sin θ), h1, h2]


end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
