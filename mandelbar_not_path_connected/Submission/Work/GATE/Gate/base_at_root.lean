/-
# The `c₀` case of the gate residual, as far as it is proved

The residual of §2.3 at a parameter `e` is `Work.GATE.GateResidual e α`:

* `BranchData` — the `α`-Böttcher branch of `(T_e)^{10}` on the positive-potential tube,
  normalised at the direction `α` (the design's `G1` + `G2`);
* `BaseWindow` — the connecting-path identity `e = Λ^[m] p` with the base point `p` in the
  `α`-window (the design's `G3`, whose window is `A1`).

This module records the two halves of the **`c₀` case**, which need no PARIMPL data:

* `branchData_alpha1_of_rootParabolic` (**proved**, `Submission/Work/GATE/Gate/`) — at a root arc
  the `α₁`-branch of the second return map exists on the tube of ray points of angles in
  `(α₁ - 1/8, α₁ + 1/8)` at levels `> 1`, with the normalisation `deviation (Λ z) = deviation z/1024`
  (the design's key arithmetic `(α₁ + 371)/1024 = α₁`);
* `A1` (**proved**, `Submission/Work/GATE/Nest/`) — a point of the `z₁`-nest off `K` has its
  dynamical ray in one of the two windows, and a ray in the window has Böttcher deviation in the
  window (`deviation_eq_of_mem_paramRay`, `Nest/base_window.lean`): the base of `G3` at `c₀`.

What is *not* here: the transport of these two statements from `c₀` to a nearby parameter `e`
(where the critical orbit escapes through the gate).  That is the design's `G1` proper (the choice
of the tube `D` avoiding the critical values, PARIMPL's domain) together with the joint continuity
of the Böttcher coordinate (NAKANE).
-/
import Submission.Work.GATE.Gate.Defs
import Submission.Work.GATE.Gate.branchData_alpha1_of_rootParabolic
import Submission.Work.GATE.Nest.base_window

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

/-- **The `c₀` case of the gate residual.**  At a root arc `d`:

1. **`G2` at `c₀`** — the `α₁`-branch of `F_{c₀}` on the tube of ray points with angles in
   `(α₁ - 1/8, α₁ + 1/8)` and levels `> 1` satisfies the four `BranchData` conditions
   (`hright`, `hmem`, `hS_dev`, `hdev`), i.e. it is the inverse branch normalised at the
   direction `α₁`;
2. **`G3`'s base at `c₀`** — for a point whose ray `A1` puts in the `α₁`-window (resp. the
   `α₂`-window), the Böttcher argument is within `windowEps` of `α₁` (resp. `α₂`). -/
theorem gateResidual_base_at_root {c : ℂ} (d : Work.EL.RootParabolic c) :
    (∃ bd : BranchData d.φ Work.EL.alpha1, bd.F = Work.EL.F c ∧
      ∀ (θ t : ℝ), 1 < t → Work.EL.alpha1 - 1 / 8 < θ → θ < Work.EL.alpha1 + 1 / 8 →
        Work.EL.rayPt d.hN θ t ∈ bd.S) ∧
    (∀ (z : ℂ) (ϑ : ℝ), z ∈ Work.EL.paramRay d.hN ϑ →
      ((Work.EL.alpha1 - Work.Final.windowEps < ϑ ∧ ϑ ≤ Work.EL.alpha1) ∨
        (Work.EL.alpha2 ≤ ϑ ∧ ϑ < Work.EL.alpha2 + Work.Final.windowEps)) →
      |deviation d.φ Work.EL.alpha1 z| < Work.Final.windowEps ∨
        |deviation d.φ Work.EL.alpha2 z| < Work.Final.windowEps) :=
  ⟨Work.GATE.Gate.branchData_alpha1_of_rootParabolic d,
    fun z ϑ hz hwin => Nest.base_window_disjunction d.hN hz hwin⟩

end Work.GATE
