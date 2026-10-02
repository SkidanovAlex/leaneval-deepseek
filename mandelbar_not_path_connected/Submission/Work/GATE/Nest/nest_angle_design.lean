/-
# `A1` in the form of `NOTES_LEAD_mandelbar_residuals.md` §2.2

The design states `A1` as

> `∀ δ>0, ∃ n, ∀ z ∈ Q̂ₙ ∖ K, ϑ(z) ∈ (α₁−δ, α₁) ∪ (α₂, α₂+δ)`,

with `Q̂ₙ` the level-`n` region of the `z₁`-nest (`polyRegion [P0, Qp n] (Qlev L n)`, which
`Work.ELNest.NestData.Qmem` identifies with
`pairSideNear P0 ∩ pairSideNear (Qp n) ∩ {pot < log (Qlev L n)}`).

This module assembles that statement from the two proved ingredients:

* `Work.GATE.Nest.exists_nest_level_window` — the level `n` at which both certificate angles
  `bAng n`, `bAng' n` are inside the `δ`-windows;
* `Work.GATE.Nest.nest_angle_z1` — the nest-angle lemma at that level,

with the nest interface `Work.EL.Z1Nest` (ELRig's structure: the `α`-pair `P0` with its angles
`α₁`, `α₂`, the level-`n` pairs `Q n` with their `PairSides`) and the two angle specifications
`(Q n).a = bAng' n`, `(Q n).b = bAng n + 1` of the certificate (ELNest's `NestData.Qpa/Qpb`).
-/
import Submission.Work.GATE.Defs
import Submission.Work.GATE.Nest.nest_angle_z1
import Submission.Work.GATE.Nest.exists_nest_level_window
import Submission.Work.ELRig.Inputs

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

namespace Work.GATE.Nest

open LeanEval.ComplexAnalysis (Mandelbar)

/-- **`A1`, in the form of §2.2 of the design.**  For every `δ > 0` there is a level `n` of the
`z₁`-nest such that every point of the level-`n` nest region off the filled Julia set has a
dynamical ray whose angle lies in `(α₁-δ, α₁] ∪ [α₂, α₂+δ)`.

`hcover` is the ray cover `Work.GATE.Nest.mem_paramRay_of_notMem_K`; the two angle hypotheses
`hQa`, `hQb` are the certificate's identification of the level-`n` pair as
`(bAng' n, bAng n + 1)` (ELNest's `NestData.Qpa/Qpb`). -/
theorem nest_angle_design {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {z₁ : ℂ} {Pa : Set ℂ}
    (nest : Work.EL.Z1Nest hN z₁ Pa)
    (hcover : ∀ z ∉ Work.EL.K c, ∃ ϑ : ℝ, z ∈ Work.EL.paramRay hN ϑ)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, ∀ z : ℂ, z ∉ Work.EL.K c →
      z ∈ Work.EL.pairSideNear nest.P0 → z ∈ Work.EL.pairSideNear (nest.Q n) →
      ∃ ϑ : ℝ, z ∈ Work.EL.paramRay hN ϑ ∧
        ((Work.EL.alpha1 - δ < ϑ ∧ ϑ ≤ Work.EL.alpha1) ∨
          (Work.EL.alpha2 ≤ ϑ ∧ ϑ < Work.EL.alpha2 + δ)) := by
  obtain ⟨n, hn1, hn2⟩ := exists_nest_level_window hδ
  refine ⟨n, fun z hzK hzP hzQ => ?_⟩
  exact nest_angle_z1 hN nest.P0 (nest.Q n) n hδ
    nest.P0_spec.1 nest.P0_spec.2.1 (hQa n) (hQb n)
    nest.sides_P0 (nest.sides_Q n) hcover hzK hzP hzQ hn1 hn2

end Work.GATE.Nest
