import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.ParamRays.Green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The parameter Green function is the parameter potential

The escape chapter defines the Green function of a `MonicGrowth` map as the `limUnder` of the
partial Green functions `greenIter f d z n = d^{-n} log⁺ ‖f^[n] z‖`, so that

`greenParam c = green (Tantibar c) 2 0 = limUnder_n 2^{-n} log⁺ ‖T_c^[n] 0‖`.

The parameter-ray chapter defines the same quantity as the `limsup` of the sequence
`Work.ParamRays.greenSeq c 0 n = 2^{-n} log⁺ ‖T_c^[n] 0‖`,

`paramPotential c = greenFun c 0 = limsup_n 2^{-n} log⁺ ‖T_c^[n] 0‖`.

The two are equal because the sequence `greenSeq c 0` converges (that is
`tendsto_greenIter` for the mandatory `MonicGrowth` structure of `Tantibar c`), and for a
convergent sequence the `limsup` is the limit, i.e. it coincides with its `limUnder`.  The only
point to check is that the two definitions of `log⁺` — `Work.Escape.logPos x = log (max 1 x)`
and Mathlib's `Real.log⁺ x = max 0 (log x)` — agree on the non-negative reals, which is
`Real.posLog_eq_log_max_one`.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

/-- The escape chapter's partial Green functions and the parameter-ray chapter's `greenSeq`
are the same sequence at the critical point. -/
theorem greenIter_Tantibar_zero_eq_greenSeq (c : ℂ) :
    greenIter (LeanEval.ComplexAnalysis.Tantibar c) 2 0 = Work.ParamRays.greenSeq c 0 := by
  funext n
  rw [greenIter_def, Work.ParamRays.greenSeq, Work.ParamRays.orbit]
  congr 1
  exact (Real.posLog_eq_log_max_one (norm_nonneg _)).symm

/-- The sequence of partial Green functions of `T_c` at the critical point converges to
`greenParam c`. -/
theorem tendsto_greenSeq_greenParam (c : ℂ) :
    Filter.Tendsto (Work.ParamRays.greenSeq c 0) Filter.atTop (nhds (greenParam c)) := by
  have ht := tendsto_greenIter (LeanEval.ComplexAnalysis.Tantibar c) 2 ‖c‖
    (monicGrowth_Tantibar c) le_rfl 0
  rw [greenIter_Tantibar_zero_eq_greenSeq] at ht
  simpa [greenParam] using ht

/-- The escape chapter's Green function of the critical orbit agrees with the parameter-ray
chapter's parameter potential. -/
theorem greenParam_eq_paramPotential (c : ℂ) :
    greenParam c = Work.ParamRays.paramPotential c := by
  rw [Work.ParamRays.paramPotential]
  exact (Work.ParamRays.greenFun_eq_of_tendsto (tendsto_greenSeq_greenParam c)).symm

end Work.Escape
