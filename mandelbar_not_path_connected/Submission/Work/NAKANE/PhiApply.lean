/-
# Consequences of the joint continuity of the critical Böttcher coordinate

Two conveniences that the consumers of `Work.NAKANE` (PARIMPL, GATE) ask for, both immediate
consequences of `Work.NAKANE.continuousOn_jointVarphi`:

* `Work.NAKANE.continuousOn_varphiCrit_fixed` : for a **fixed** point `z` which belongs to
  `critDomain c` for all parameters `c` in a set `S`, the function `c ↦ φ_c(z)` is continuous on
  `S`.  (Special cases: `z = c` — `Work.NAKANE.continuousOn_varphiCrit_self`; `z` a fixed far
  point, or a point of a fixed orbit.)
* `Work.NAKANE.continuousOn_jointVarphi_far` : on the far block `‖c‖ ≤ C`, `farRadius C < ‖z‖`
  the joint Böttcher coordinate *is* the explicit product formula, so its joint continuity there is
  an immediate corollary of the (polynomial) continuity of the product formula.

Also `Work.NAKANE.potential_tendsto_atTop`, the `potential`-form of the divergence of the potential
at infinity (matching the field `tendsto_potential` of `Work.Top.NakaneData`).
-/
import Submission.Work.NAKANE.BottcherJoint
import Submission.Work.NAKANE.PotentialTop
import Submission.Work.NAKANE.PhiContinuity
import Submission.Work.NAKANE.BottcherFar.continuousOn_jointBottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Continuity of `c ↦ φ_c z` at a fixed point `z` of the critical domain.** -/
theorem continuousOn_varphiCrit_fixed {S : Set ℂ} {z : ℂ}
    (hz : ∀ c ∈ S, z ∈ Work.ParamRays.critDomain c) :
    ContinuousOn (fun c : ℂ => Work.Bottcher.varphiCrit c z) S :=
  ContinuousOn.comp (s := S) (t := jointDomain) (g := jointVarphi)
    (f := fun c : ℂ => (c, z)) continuousOn_jointVarphi
    (continuous_id.prodMk continuous_const).continuousOn fun c hc => hz c hc

/-- The joint Böttcher coordinate agrees with the explicit product formula on the far block, where
both are (jointly) continuous. -/
theorem continuousOn_jointVarphi_far (C : ℝ) :
    ContinuousOn jointVarphi (farBlock C (farRadius C)) := by
  refine (Work.NAKANE.BottcherFar.continuousOn_jointBottcher.mono ?_).congr ?_
  · intro p hp
    exact escapeRadius_lt_of_farRadius_lt hp.1 hp.2
  · rintro ⟨c, z⟩ hp
    exact jointVarphi_eq_jointBottcher_of_far' hp.1 hp.2

/-- **The potential diverges at infinity**, in the `Work.ParamRays.potential` form. -/
theorem potential_tendsto_atTop (t : ℝ) :
    ∃ R : ℝ, ∀ c : ℂ, R ≤ ‖c‖ → t ≤ Work.ParamRays.potential c := by
  obtain ⟨R, hR⟩ := paramPotential_tendsto_atTop (t / 2)
  exact ⟨R, fun c hc => by
    rw [potential_eq_two_paramPotential]
    linarith [hR c hc]⟩

end Work.NAKANE
