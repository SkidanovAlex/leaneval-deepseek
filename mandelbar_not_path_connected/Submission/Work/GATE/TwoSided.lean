/-
# `Work.GATE.twoSided` — the `twoSided` field of `Work.Final.FinalInputs`

This module assembles the two halves of the design §2:

* `Work.GATE.Segment.seg_tongues` (§2.1, **SEG**): at every scale `r > 0` a straight segment in
  the implosion side `Nm` inside `ball c₀ r` carries two escaping parameters, one in the
  `b`-tongue and one in the `ι b`-tongue of the transit coordinate (`Work.GATE.TransitData`);
* `Work.GATE.GateAngle` (§2.3, **GATE**): the parameters of the two tongues have parameter
  external angles within `ε` of `α₁`, resp. `α₂`.

The assembly below is the *verbatim* `twoSided` field, up to the definitional unfolding of
`Work.GATE.TwoSided`.
-/
import Submission.Work.GATE.Defs
import Submission.Work.GATE.Segment.seg_tongues

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

/-- **`Work.GATE.twoSided`** — the `twoSided` field of `Work.Final.FinalInputs`: at every scale
`r > 0` a straight segment in the implosion side `Nm` inside `ball c₀ r` carries two escaping
parameters whose parameter external angles lie in the two windows around the root angles
`α₁ = 371/1023` and `α₂ = 404/1023`.

The hypotheses are the two named inputs of the design:

* `hOpen`/`hfront` — the elementary structure of `Nm` (an open set accumulating at `c₀`; in the
  endgame `c₀ ∈ frontier Nm` is `Work.Final.RootArc.mem_frontier_Nm`);
* `TD : TransitData c₀ Nm` — **TT**, PARIMPL's transit coordinate (§1.3–1.4);
* `G : GateAngle c₀ Nm TD` — **GATE** (§2.3), the angle transport through the gate.

The two points `e₁`, `e₂` produced are in the *open* segment, hence in `Nm`, and the segment is
contained in `Nm ∩ ball c₀ r`. -/
theorem twoSided {c₀ : ℂ} {Nm : Set ℂ} (hOpen : IsOpen Nm) (hfront : c₀ ∈ frontier Nm)
    (TD : TransitData c₀ Nm) (G : GateAngle c₀ Nm TD) : TwoSided c₀ Nm := by
  intro r hr
  obtain ⟨ρg, hρg, hg⟩ := G.b Work.Final.windowEps windowEps_pos
  obtain ⟨ρi, hρi, hi⟩ := G.iota Work.Final.windowEps windowEps_pos
  set r' : ℝ := min (min r ρg) ρi with hr'def
  have hr' : 0 < r' := lt_min (lt_min hr hρg) hρi
  obtain ⟨x, y, hseg, e₁, he₁, e₂, he₂, hM₁, hM₂, ht₁, ht₂⟩ :=
    Work.GATE.Segment.seg_tongues hOpen hfront TD hr'
  refine ⟨x, y, fun z hz => ⟨(hseg hz).1, ?_⟩, e₁, he₁, e₂, he₂, hM₁, hM₂, ?_, ?_⟩
  · exact Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) (hseg hz).2
  · refine mem_window_of_abs_lt (hg e₁ ?_ ht₁ hM₁)
    exact ⟨(hseg he₁).1,
      Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _)) (hseg he₁).2⟩
  · refine mem_window_of_abs_lt (hi e₂ ?_ ht₂ hM₂)
    exact ⟨(hseg he₂).1, Metric.ball_subset_ball (min_le_right _ _) (hseg he₂).2⟩

/-- **`GateAngle` in the window form**: a parameter of the `b`-tongue near `c₀` has its
parameter external angle in the window `(α₁ - ε, α₁ + ε)`. -/
theorem GateAngle.b_window {c₀ : ℂ} {Nm : Set ℂ} {TD : TransitData c₀ Nm}
    (G : GateAngle c₀ Nm TD) :
    ∀ ε > 0, ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ,
      bTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
        Work.ParamRays.extAngle e ∈
          Set.Ioo (Work.Final.alpha1 - ε) (Work.Final.alpha1 + ε) := by
  intro ε hε
  obtain ⟨ρ, hρ, h⟩ := G.b ε hε
  exact ⟨ρ, hρ, fun e he ht hM => mem_window_of_abs_lt (h e he ht hM)⟩

/-- **`GateAngle` in the window form**, `ι b`-tongue. -/
theorem GateAngle.iota_window {c₀ : ℂ} {Nm : Set ℂ} {TD : TransitData c₀ Nm}
    (G : GateAngle c₀ Nm TD) :
    ∀ ε > 0, ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ,
      iotaTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
        Work.ParamRays.extAngle e ∈
          Set.Ioo (Work.Final.alpha2 - ε) (Work.Final.alpha2 + ε) := by
  intro ε hε
  obtain ⟨ρ, hρ, h⟩ := G.iota ε hε
  exact ⟨ρ, hρ, fun e he ht hM => mem_window_of_abs_lt (h e he ht hM)⟩

/-- **Non-vacuity of `twoSided`**: at every scale there is an escaping parameter in `ball c₀ r`
(namely `e₁` of the segment).  This is `Work.Final.FinalInputs.exists_escaping_near` in the
vocabulary of this area. -/
theorem twoSided_exists_notMem {c₀ : ℂ} {Nm : Set ℂ} (h : TwoSided c₀ Nm) {r : ℝ}
    (hr : 0 < r) : ∃ c ∈ Metric.ball c₀ r, c ∉ Mandelbar := by
  obtain ⟨x, y, hseg, e₁, he₁, -, -, hM₁, -⟩ := h r hr
  exact ⟨e₁, (hseg he₁).2, hM₁⟩

/-- **The two escaping parameters of `twoSided` are distinct**: their external angles lie in the
two disjoint windows. -/
theorem twoSided_distinct {c₀ : ℂ} {Nm : Set ℂ} (h : TwoSided c₀ Nm) {r : ℝ} (hr : 0 < r) :
    ∃ e₁ e₂ : ℂ, e₁ ∈ Nm ∩ Metric.ball c₀ r ∧ e₂ ∈ Nm ∩ Metric.ball c₀ r ∧ e₁ ≠ e₂ ∧
      e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
      Work.ParamRays.extAngle e₁ ∈ Set.Ioo (Work.Final.alpha1 - Work.Final.windowEps)
        (Work.Final.alpha1 + Work.Final.windowEps) ∧
      Work.ParamRays.extAngle e₂ ∈ Set.Ioo (Work.Final.alpha2 - Work.Final.windowEps)
        (Work.Final.alpha2 + Work.Final.windowEps) := by
  obtain ⟨x, y, hseg, e₁, he₁, e₂, he₂, hM₁, hM₂, hw₁, hw₂⟩ := h r hr
  refine ⟨e₁, e₂, hseg he₁, hseg he₂, fun hEq => ?_, hM₁, hM₂, hw₁, hw₂⟩
  rw [← hEq] at hw₂
  have hsep := windows_disjoint
  linarith [hw₁.2, hw₂.1]

/-- **Consistency of `twoSided` with the implosion side**: the segment lies in `Nm` at every
scale, so `Nm` accumulates at `c₀`.  This is `Work.Final.mem_closure_Nm_of_twoSided` in the
vocabulary of this area (and it makes `twoSided` consistent with
`Work.Final.ImplosionSide.c_mem_closure`). -/
theorem twoSided_mem_closure {c₀ : ℂ} {Nm : Set ℂ} (h : TwoSided c₀ Nm) : c₀ ∈ closure Nm := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨x, y, hseg, e₁, he₁, -⟩ := h ε hε
  exact ⟨e₁, (hseg he₁).1, by simpa [Metric.mem_ball, dist_comm] using (hseg he₁).2⟩

/-- The two angle windows are disjoint, so the two parameters produced by `twoSided` have
different external angles (hence are different points). -/
theorem extAngle_ne_of_mem_windows {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Set.Ioo (Work.Final.alpha1 - Work.Final.windowEps)
      (Work.Final.alpha1 + Work.Final.windowEps))
    (h₂ : θ₂ ∈ Set.Ioo (Work.Final.alpha2 - Work.Final.windowEps)
      (Work.Final.alpha2 + Work.Final.windowEps)) : θ₁ ≠ θ₂ := by
  intro h
  have hsep := windows_disjoint
  rw [h] at h₁
  linarith [h₁.2, h₂.1]

/-- The two angle windows of `twoSided` are disjoint (arithmetic of the root portrait): the two
escaping parameters produced by `twoSided` have genuinely different angles. -/
theorem windowEps_separation :
    Work.Final.alpha1 + Work.Final.windowEps < Work.Final.alpha2 - Work.Final.windowEps :=
  windows_disjoint

end Work.GATE
