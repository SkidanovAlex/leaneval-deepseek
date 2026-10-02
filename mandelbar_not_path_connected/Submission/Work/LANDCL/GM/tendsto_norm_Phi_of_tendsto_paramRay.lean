/-
Copyright: subproject `Submission/Work/LANDCL/` of `mandelbar_not_path_connected`.

# The level of a converging sequence on a parameter ray tends to `1`

This is the "level" step of the reduction `Work.LANDCL.repellingRayParamStable` (`gm`): a
sequence `cₙ` of parameters on the parameter ray `R(θ)` (so `cₙ ∉ Mb` and `‖Φ cₙ‖ > 1`) which
converges to a parameter `c` *on* the mandelbar has `‖Φ cₙ‖ → 1`, i.e. the equipotential level
of the ray points tends to the boundary level.

The mathematics is the continuity of the potential: by `Work.ParamRays.continuous_potential` the
function `c ↦ log ‖Φ c‖` (with the convention `log 0 = 0`, so that it vanishes on `Mb`) is
continuous on the whole plane, so `log ‖Φ (cₙ)‖ → log ‖Φ c‖ = 0`; raising to the exponential
turns this into `‖Φ cₙ‖ = exp (log ‖Φ cₙ‖) → exp 0 = 1`, using `1 < ‖Φ cₙ‖`
(`Work.ParamRays.CP.one_lt_norm_Phi`).
-/
import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.ParamRays.continuous_potential

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.GM

open Filter
open scoped Topology

/-- **The level `‖Φ cₙ‖` along a parameter ray tending to a parameter of the mandelbar tends to
`1`.**  The hypotheses are exactly the situation of the reduction `gm`: `hN` the parameter
Böttcher input, `hc : c ∈ Mandelbar` the limiting parameter, `hmem` says `cₙ ∈ R(θ)`, and
`htend` says `cₙ → c`. -/
theorem tendsto_norm_Phi_of_tendsto_paramRay (hN : Work.ParamRays.NakaneInput) {c : ℂ}
    (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) {θ : ℝ} {cn : ℕ → ℂ}
    (hmem : ∀ n : ℕ, cn n ∈ Work.ParamRays.paramRay θ)
    (htend : Filter.Tendsto cn Filter.atTop (nhds c)) :
    Filter.Tendsto (fun n : ℕ => ‖Work.ParamRays.Phi (cn n)‖) Filter.atTop (nhds 1) := by
  -- ray points lie outside the mandelbar
  have hnotmem : ∀ n : ℕ, cn n ∉ Work.ParamRays.Mb :=
    fun n => (Work.ParamRays.mem_paramRay.mp (hmem n)).1
  -- the potential is continuous and vanishes at `c ∈ Mb`, so the levels below tend to `0`
  have hpot : Filter.Tendsto (fun n : ℕ => Work.ParamRays.potential (cn n))
      Filter.atTop (nhds (0 : ℝ)) := by
    have h := ((Work.ParamRays.continuous_potential hN).continuousAt (x := c)).tendsto.comp htend
    rwa [Work.ParamRays.potential_eq_zero_of_mem hc] at h
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (Work.ParamRays.potential (cn n)))
      Filter.atTop (nhds 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp hpot
    simpa only [Function.comp_def, Real.exp_zero] using h
  -- off the mandelbar the potential is `log ‖Φ ·‖`, and `‖Φ ·‖ > 1` there
  have hpos : ∀ n : ℕ, 0 < ‖Work.ParamRays.Phi (cn n)‖ :=
    fun n => lt_trans zero_lt_one (Work.ParamRays.CP.one_lt_norm_Phi hN (hnotmem n))
  have hfun : (fun n : ℕ => ‖Work.ParamRays.Phi (cn n)‖) =
      fun n : ℕ => Real.exp (Work.ParamRays.potential (cn n)) := by
    funext n
    rw [Work.ParamRays.potential, dite_eq_right (hnotmem n), Real.exp_log (hpos n)]
  rw [hfun]
  exact hexp

end Work.LANDCL.GM
