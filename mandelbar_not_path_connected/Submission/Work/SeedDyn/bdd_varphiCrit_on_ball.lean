import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.ParamRays.greenFun_pos_of_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn

open Filter

/-- **Auxiliary bound.**  The Green function of the (anti)polynomial family `T_c` is bounded
above on the part of the escaping set that lies in the closed ball of radius `R`: for
`‖z‖ ≤ R` one has `G_c z ≤ log (2 * (max R 0 + ‖c‖ + 1))`.

This is the uniform-in-`z` form of `Work.ParamRays.GreenGrowth.greenSeq_le_log`, which
estimates the normalized logarithms `greenSeq c z n = 2^{-n} log⁺ ‖T_c^[n] z‖` by
`log (2 * (‖z‖ + ‖c‖ + 1))`, a bound that is itself uniform on a ball; the `limsup`
defining `G_c` is then dominated by the same constant. -/
theorem greenFun_le_log_of_norm_le (c : ℂ) (R : ℝ) {z : ℂ} (hzR : ‖z‖ ≤ R) :
    Work.ParamRays.greenFun c z ≤ Real.log (2 * (max R 0 + (‖c‖ + 1))) := by
  refine Work.ParamRays.greenFun_le_of_eventually (Eventually.of_forall fun n => ?_)
  refine le_trans (Work.ParamRays.GreenGrowth.greenSeq_le_log c z n) ?_
  refine Real.log_le_log (by positivity) ?_
  have h1 : ‖z‖ ≤ max R 0 := le_trans hzR (le_max_left R 0)
  linarith [norm_nonneg z, norm_nonneg c]

/-- The Böttcher coordinate `varphiCrit c` is bounded on the part of the escaping set inside
the closed ball of radius `R`.

On `esc c` the modulus of the Böttcher coordinate is `exp (G_c z)` (D3 of the design note),
and `G_c` is bounded there by `greenFun_le_log_of_norm_le`, whence the uniform bound
`‖varphiCrit c z‖ ≤ exp (log (2 * (max R 0 + ‖c‖ + 1))) = 2 * (max R 0 + ‖c‖ + 1)`. -/
theorem bdd_varphiCrit_on_ball {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (R : ℝ) :
    ∃ M : ℝ, ∀ z ∈ Work.SeedDyn.esc c, ‖z‖ ≤ R → ‖Work.Bottcher.varphiCrit c z‖ ≤ M := by
  refine ⟨2 * (max R 0 + (‖c‖ + 1)), fun z hz hzR => ?_⟩
  rw [norm_varphiCrit_esc hc hz]
  calc Real.exp (Work.ParamRays.greenFun c z)
      ≤ Real.exp (Real.log (2 * (max R 0 + (‖c‖ + 1)))) :=
        Real.exp_le_exp.mpr (greenFun_le_log_of_norm_le c R hzR)
    _ = 2 * (max R 0 + (‖c‖ + 1)) := Real.exp_log (by positivity)

end Work.SeedDyn
