/-
# `twoSided` from SEG + A1 + the gate residual

`Work.GATE.twoSided` derives the `twoSided` field of `Work.Final.FinalInputs` from the *named
conclusion* `GateAngle` of §2.3.  This module proves the same theorem from the finer residual
`Work.GATE.GateResidual`, in which the *conclusion* of GATE is not assumed: all that is assumed
per parameter is

* the `α`-Böttcher branch `Λ` of `(T_e)^{10}` on the tube, normalised at the direction `α`
  (`Work.GATE.BranchData`: the design's `G1` + `G2`), and
* the connecting-path identity `e = Λ^[m] p` with the base point `p` in the `α`-window
  (`Work.GATE.BaseWindow`: the design's `G3`).

The transport `G4` and the window arithmetic are **proved** (`Work.GATE.gate_window`,
`Work.GATE.GateResidual.window`), `A1` is proved (`Work.GATE.Nest.*`), and `SEG` is proved
(`Work.GATE.Segment.seg_tongues`).  So the residual of the whole chapter is: *along the critical
orbit the inverse branch fixing `±a` agrees with the `α₁`-branch on the tube, and the base point
of the connecting path lies in the `α₁`-window* — a precise dynamical statement about the tube
`D` and the joint Böttcher continuity, not the final angle conclusion.
-/
import Submission.Work.GATE.Defs
import Submission.Work.GATE.Segment.seg_tongues
import Submission.Work.GATE.Gate.Residual

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

/-- **The two gate-window conclusions from the residual.**  A residual datum for every parameter
of the `b`-tongue (`α₁`) resp. of the `ι b`-tongue (`α₂`) inside a neighbourhood of `c₀` puts the
external angles in the two windows. -/
theorem gate_windows_of_residual {c₀ : ℂ} {Nm : Set ℂ} (TD : TransitData c₀ Nm)
    (h₁ : ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ,
      bTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
        Nonempty (GateResidual e Work.Final.alpha1))
    (h₂ : ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ,
      iotaTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
        Nonempty (GateResidual e Work.Final.alpha2)) :
    (∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ,
      bTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
        Work.ParamRays.extAngle e ∈ Set.Ioo (Work.Final.alpha1 - Work.Final.windowEps)
          (Work.Final.alpha1 + Work.Final.windowEps)) ∧
    (∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ,
      iotaTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
        Work.ParamRays.extAngle e ∈ Set.Ioo (Work.Final.alpha2 - Work.Final.windowEps)
          (Work.Final.alpha2 + Work.Final.windowEps)) := by
  obtain ⟨ρ₁, hρ₁, hg₁⟩ := h₁
  obtain ⟨ρ₂, hρ₂, hg₂⟩ := h₂
  exact ⟨⟨ρ₁, hρ₁, fun e he ht hM => (hg₁ e he ht hM).some.window_alpha1⟩,
    ⟨ρ₂, hρ₂, fun e he ht hM => (hg₂ e he ht hM).some.window_alpha2⟩⟩

/-- **`twoSided` from SEG + the gate residual.**  Same conclusion as `Work.GATE.twoSided`, with
the named conclusion `GateAngle` replaced by the finer per-parameter residual `GateResidual`
(the branch data `G1`+`G2` and the connecting path `G3`). -/
theorem twoSided_of_residual {c₀ : ℂ} {Nm : Set ℂ} (hOpen : IsOpen Nm)
    (hfront : c₀ ∈ frontier Nm) (TD : TransitData c₀ Nm)
    (h₁ : ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ,
      bTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
        Nonempty (GateResidual e Work.Final.alpha1))
    (h₂ : ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ,
      iotaTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
        Nonempty (GateResidual e Work.Final.alpha2)) :
    TwoSided c₀ Nm := by
  obtain ⟨hwin₁, hwin₂⟩ := gate_windows_of_residual TD h₁ h₂
  obtain ⟨ρ₁, hρ₁, hg₁⟩ := hwin₁
  obtain ⟨ρ₂, hρ₂, hg₂⟩ := hwin₂
  intro r hr
  set r' : ℝ := min (min r ρ₁) ρ₂ with hr'def
  have hr' : 0 < r' := lt_min (lt_min hr hρ₁) hρ₂
  obtain ⟨x, y, hseg, e₁, he₁, e₂, he₂, hM₁, hM₂, ht₁, ht₂⟩ :=
    Work.GATE.Segment.seg_tongues hOpen hfront TD hr'
  refine ⟨x, y, fun z hz => ⟨(hseg hz).1, ?_⟩, e₁, he₁, e₂, he₂, hM₁, hM₂, ?_, ?_⟩
  · exact Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) (hseg hz).2
  · exact hg₁ e₁ ⟨(hseg he₁).1,
      Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _)) (hseg he₁).2⟩ ht₁ hM₁
  · exact hg₂ e₂ ⟨(hseg he₂).1,
      Metric.ball_subset_ball (min_le_right _ _) (hseg he₂).2⟩ ht₂ hM₂

end Work.GATE
