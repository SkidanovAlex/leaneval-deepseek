/-
# Discharging PARIMPL's `GreenEscapeOpen`: the joint continuity of the Green function

`Work.PARIMPL.GreenEscapeOpen` (`Submission/Work/PARIMPL/Leak.lean`) is the **NAKANE input** of the
robust-leak argument `Work.PARIMPL.robust_of_greenOpen` (item (I2) of
`NOTES_LEAD_mandelbar_residuals.md` §1.4, consumed by `LeakData.robust`):

> if `G_{c₀} z > 0` then, for all `c'` close to `c₀` and all `z'` close to `z`,
> `G_{c'} z' > 0`.

It is an immediate consequence of the *joint continuity* of `(c,z) ↦ G_c z`
(`Work.NAKANE.continuous_greenFun`, proved from the continuity of the Green function of the
escape chapter): `{(c,z) | 0 < G_c z}` is the preimage of the open half line `(0,∞)` under a
continuous function, hence open, hence a neighbourhood of `(c₀,z)`.

This file contains the one-line discharge `Work.NAKANE.greenEscapeOpen`; no other content of
`Work.PARIMPL` is used.
-/
import Submission.Work.NAKANE.GreenJoint
import Submission.Work.PARIMPL.Leak

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The NAKANE input `Work.PARIMPL.GreenEscapeOpen`, discharged.** -/
theorem greenEscapeOpen : Work.PARIMPL.GreenEscapeOpen := by
  intro c z h
  have hcont : Continuous (fun p : ℂ × ℂ => Work.ParamRays.greenFun p.1 p.2) := continuous_greenFun
  have h0 : 0 < Work.ParamRays.greenFun c z := by
    rw [greenFun_eq_green]
    exact h
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := (c, z)))
    (Work.ParamRays.greenFun c z) h0
  refine ⟨δ / 2, by positivity, fun c' hc' z' hz' => ?_⟩
  have hd1 : dist c' c < δ / 2 := Metric.mem_ball.mp hc'
  have hd2 : dist z' z < δ / 2 := Metric.mem_ball.mp hz'
  have hdist : dist (c', z') (c, z) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (by linarith) (by linarith)
  have h1 : dist (Work.ParamRays.greenFun c' z') (Work.ParamRays.greenFun c z) <
      Work.ParamRays.greenFun c z := hδ' (x := (c', z')) hdist
  have h2 : 0 < Work.ParamRays.greenFun c' z' := by
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h1.1]
  rw [greenFun_eq_green] at h2
  exact h2

end Work.NAKANE
