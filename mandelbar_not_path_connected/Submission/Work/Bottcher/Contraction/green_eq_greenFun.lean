import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.ParamRays.Green
import Submission.Work.Escape.greenParam_eq_paramPotential
import Submission.Work.Escape.tendsto_greenIter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

open Filter

/-- The escape chapter's partial Green functions `greenIter (T_c) 2 z` and the
parameter-ray chapter's `greenSeq c z` are the same sequence: the two chapters
differ only in their definition of `log⁺`, and `logPos x = log (max 1 x)` agrees
with `Real.log⁺ x = max 0 (log x)` on non-negative reals. -/
theorem greenIter_Tantibar_eq_greenSeq (c z : ℂ) :
    Work.Escape.greenIter (LeanEval.ComplexAnalysis.Tantibar c) 2 z =
      Work.ParamRays.greenSeq c z := by
  funext n
  rw [Work.Escape.greenIter_def, Work.ParamRays.greenSeq, Work.ParamRays.orbit]
  congr 1
  exact (Real.posLog_eq_log_max_one (norm_nonneg _)).symm

/-- The Green function of the tricorn family, defined in the escape chapter as
`limUnder_n 2^{-n} log⁺ ‖T_c^[n] z‖`, agrees with the parameter-ray chapter's
Green function, defined as `limsup_n 2^{-n} log⁺ ‖T_c^[n] z‖`.  The two are equal
because the sequence converges (the partial Green functions have an honest limit,
`Escape.tendsto_greenIter`). -/
theorem green_eq_greenFun (c z : ℂ) :
    Work.Bottcher.green c z = Work.ParamRays.greenFun c z := by
  have ht : Filter.Tendsto (Work.ParamRays.greenSeq c z) Filter.atTop
      (nhds (Work.Bottcher.green c z)) := by
    have h := Work.Escape.tendsto_greenIter (LeanEval.ComplexAnalysis.Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) le_rfl z
    rw [greenIter_Tantibar_eq_greenSeq c z] at h
    simpa [Work.Bottcher.green] using h
  exact (Work.ParamRays.greenFun_eq_of_tendsto ht).symm

end Work.Bottcher.Contraction
