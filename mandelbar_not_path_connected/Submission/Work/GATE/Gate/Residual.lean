/-
# The GATE residual: the branch data and the base window at one parameter

`Work.GATE.GateResidual e α` packages everything that the design §2.3 still owes at a single
parameter `e` and direction `α`:

* a critical Böttcher coordinate `φ` of the parameter `e` (Böttcher's theorem, delivered as
  `Work.Bottcher.bottcherExists_crit` / `Work.ParamRays.Phi_eq_of_isCritBottcher`);
* `BranchData φ α` — the `α`-Böttcher branch `Λ` of the second return map `F_e = (T_e)^{10}` on
  the tube (`G1` + `G2`: the branch fixing `±a` agrees with the `α`-branch along the critical
  orbit);
* `BaseWindow bd e` — the `G3` connecting path: `e = Λ^[m] p` with the base point `p` inside the
  `α`-window (`A1` at `c₀`, transported by the joint continuity of the Böttcher coordinate).

The *conclusion* of `G4` (the design's `extAngle e = α + (ϑ_e p_e - α)/1024^m` and the window) is
**proved** in `Submission/Work/GATE/Gate/Transport.lean`, and used below; nothing about the final
angle conclusion is assumed.
-/
import Submission.Work.GATE.Gate.Transport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE

open LeanEval.ComplexAnalysis (Mandelbar)

/-- **The GATE residual at one parameter**: the `α`-Böttcher branch along the critical orbit and
the base window of §2.3. -/
structure GateResidual (e : ℂ) (α : ℝ) where
  /-- the critical Böttcher coordinate of the parameter `e`. -/
  φ : ℂ → ℂ
  /-- the `α`-branch of the inverse of the second return map on the tube (`G1` + `G2`). -/
  bd : BranchData φ α
  /-- the connecting path: `e = Λ^[m] p` with the base point in the `α`-window (`G3`). -/
  bw : BaseWindow bd e
  /-- `φ` is *the* critical Böttcher coordinate of `e` (Böttcher's theorem). -/
  hPhi : Work.ParamRays.Phi e = φ e

/-- The two root directions lie away from `0` and `1` (the half-width on which the
`α`-relative lifting of the Böttcher argument is valid). -/
theorem alpha1_quarter : (1 / 4 : ℝ) < Work.Final.alpha1 ∧ Work.Final.alpha1 < 3 / 4 := by
  constructor <;> · rw [Work.Final.alpha1, Work.EL.alpha1]; norm_num

theorem alpha2_quarter : (1 / 4 : ℝ) < Work.Final.alpha2 ∧ Work.Final.alpha2 < 3 / 4 := by
  constructor <;> · rw [Work.Final.alpha2, Work.EL.alpha2]; norm_num

/-- **The GATE conclusion (G4), at one parameter**: a residual at `e` in the direction `α` puts
the external angle of `e` in the `α`-window. -/
theorem GateResidual.window {e : ℂ} {α : ℝ} (G : GateResidual e α)
    (hα0 : 1 / 4 < α) (hα1 : α < 3 / 4) :
    |Work.ParamRays.extAngle e - α| < Work.Final.windowEps :=
  gate_window G.bd G.bw hα0 hα1 G.hPhi

/-- The same, in the window-membership form. -/
theorem GateResidual.window_mem {e : ℂ} {α : ℝ} (G : GateResidual e α)
    (hα0 : 1 / 4 < α) (hα1 : α < 3 / 4) :
    Work.ParamRays.extAngle e ∈
      Set.Ioo (α - Work.Final.windowEps) (α + Work.Final.windowEps) :=
  mem_window_of_abs_lt (G.window hα0 hα1)

/-- The GATE conclusion at the first root direction `α₁ = 371/1023`. -/
theorem GateResidual.window_alpha1 {e : ℂ} (G : GateResidual e Work.Final.alpha1) :
    Work.ParamRays.extAngle e ∈
      Set.Ioo (Work.Final.alpha1 - Work.Final.windowEps)
        (Work.Final.alpha1 + Work.Final.windowEps) :=
  G.window_mem alpha1_quarter.1 alpha1_quarter.2

/-- The GATE conclusion at the second root direction `α₂ = 404/1023`. -/
theorem GateResidual.window_alpha2 {e : ℂ} (G : GateResidual e Work.Final.alpha2) :
    Work.ParamRays.extAngle e ∈
      Set.Ioo (Work.Final.alpha2 - Work.Final.windowEps)
        (Work.Final.alpha2 + Work.Final.windowEps) :=
  G.window_mem alpha2_quarter.1 alpha2_quarter.2

end Work.GATE
