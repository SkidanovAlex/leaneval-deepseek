/-
# GATE2 — the phase identity: the minimal residual of residual 2, and the window it gives

The design's §2.3 (`G1`–`G4`) proves, for a parameter `e` of a tongue, that the *parameter*
Böttcher angle of `e` is the `α`-Böttcher angle of the *base point* of the connecting path divided
by `1024^m`:

    extAngle e = α + (ϑ p_e − α)/1024^m ,     p_e = (F_e)^[m] e ,

i.e. in the `α`-relative deviation `Work.GATE.deviation` (the lifted Böttcher argument):

    **deviation φ_e α e = deviation φ_e α p_e / 1024^m** .

Everything else of `G1`–`G4` — the tube `D`, the inverse branch `Λ`, the identification of `Λ` with
the `α`-Böttcher branch along the critical orbit — is *machinery* for this one scalar identity
(together with the window bound on `p_e`, which is residual 1 + the tracked exit,
`Submission/Work/GATE2/Window.lean`).  This module

* states that identity as the residual **`Work.GATE2.PhaseResidual`**, in vocabulary that contains
  no gate object at all (only Böttcher's `varphiCrit`, ELRig's `Work.EL.F`, the *definitions*
  `Work.GATE.deviation`, `bTongue`/`iotaTongue` and `Work.Final.windowEps`);
* proves that it *suffices*: `Work.GATE2.window_of_phase` turns it, together with the window bound
  on the base point, into the parameter window `|extAngle e − α| < windowEps`, and
  `Work.GATE2.twoSided_of_phaseResidual` assembles `Work.GATE.TwoSided c₀ Nm` from it (via SEG and
  the window arithmetic, `Work.GATE2.twoSided_of_phaseWindows`);
* proves that GATE's own machinery *implies* it
  (`Work.GATE2.phaseResidual_of_gateResidual`: from `Work.GATE.GateResidual`, whose `BaseWindow`
  carries `e = Λ^[m] p` and the window bound, the identity is `Work.GATE.deviation_iterate`), so
  the new residual is *strictly weaker* than `G1`+`G2`+`G3` and a future prover has strictly less
  to do.

## Why the identity is a single integer condition

`Work.GATE2.varphiCrit_F_iterate` gives `(φ_e z)^{1024^m} = φ_e (F_e^m z)`, so the two sides of the
identity differ (before the reduction by `1024^m`) by an integer multiple of `1/1024^m`
(`Work.GATE2.phase_gap_integrality`): the identity is *equivalent* to the vanishing of one integer
`j` — the design's "the branch is the one whose `α`-displacement is divided by `1024`", i.e. the
integer `371 = 1023·α₁` (the arithmetic `(α₁ + 371)/1024 = α₁` of GATE's `branchDataAlpha1`).
-/
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.Transport
import Submission.Work.GATE2.Escape

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

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar)

/-! ## The phase identity gives the parameter window -/

/-- **The phase identity plus the base window give the parameter window.**  If the `α`-deviation of
the parameter `e` is the `α`-deviation of the base point `(F_e)^[m] e` divided by `1024^m`
(the design's `G4` formula `extAngle e = α + (ϑ p_e − α)/1024^m`), and the base point's deviation
is in the window `(−windowEps, windowEps)`, then the external angle of `e` is in the `α`-window.

This is the *net* content of `G1`–`G4`: no tube and no branch is mentioned. -/
theorem window_of_phase {e : ℂ} {α : ℝ} (hα0 : 1 / 4 < α) (hα1 : α < 3 / 4)
    (hM : e ∉ Mandelbar) {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsCritBottcher e φ) {m : ℕ}
    (hid : Work.GATE.deviation φ α e =
      Work.GATE.deviation φ α ((Work.EL.F e)^[m] e) / (1024 : ℝ) ^ m)
    (hbound : |Work.GATE.deviation φ α ((Work.EL.F e)^[m] e)| < Work.Final.windowEps) :
    |Work.ParamRays.extAngle e - α| < Work.Final.windowEps := by
  have hΦ : Work.ParamRays.Phi e = φ e := Work.ParamRays.Phi_eq_of_isCritBottcher hM hφ
  have hdiv : (1 : ℝ) ≤ (1024 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hde : |Work.GATE.deviation φ α e| < Work.Final.windowEps := by
    have h1 : |Work.GATE.deviation φ α e| ≤ |Work.GATE.deviation φ α ((Work.EL.F e)^[m] e)| := by
      rw [hid, abs_div, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 1024) m)]
      rw [div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 1024) m)]
      nlinarith [abs_nonneg (Work.GATE.deviation φ α ((Work.EL.F e)^[m] e)), hdiv]
    linarith [hbound, h1]
  have hsmall : |Work.GATE.deviation φ α e| < 1 / 4 :=
    lt_trans hde Work.GATE.windowEps_lt_quarter
  have h1 : toIcoMod one_pos 0 (Work.GATE.bAngle φ e) = α + Work.GATE.deviation φ α e := by
    rw [← Work.GATE.toIcoMod_liftAngle φ α e]
    exact Work.GATE.toIcoMod_eq_alpha_add_deviation hα0 hα1 hsmall
  have hext : Work.ParamRays.extAngle e = α + Work.GATE.deviation φ α e := by
    simpa [Work.ParamRays.extAngle, Work.GATE.bAngle, hΦ] using h1
  rw [hext, add_sub_cancel_left]
  exact hde

/-! ## The residual -/

/-- **The phase residual: the minimal form of residual 2 (`G1`+`G2`+`G3` of §2.3).**

For every parameter `e` of the `b`-tongue (resp. of the `ι b`-tongue) near `c₀` on the implosion
side, off the mandelbar, there is a time `m` at which the critical orbit has passed the gate, such
that

* the base point `p = (F_e)^[m] e` has its `α`-deviation in the window (`windowEps`), and
* the phase identity `deviation φ_e α e = deviation φ_e α p / 1024^m` holds,

`φ_e = Work.Bottcher.varphiCrit e` being the canonical critical Böttcher coordinate of `T_e`
(Böttcher's theorem, available for every `e`).

The first conjunct is *proved* elsewhere in this area once the design's §2.2 access is available
(`Work.GATE2.orbitWindow_of_continuousAt`: residual 1 at `c₀` plus the tracked exit); the content
of the residual is the phase identity.  GATE's machinery implies it
(`Work.GATE2.phaseResidual_of_gateResidual`), and it yields the assembly
(`Work.GATE2.window_of_phase`, `Work.GATE2.twoSided_of_phaseResidual`). -/
structure PhaseResidual (c₀ : ℂ) (Nm : Set ℂ) (TD : Work.GATE.TransitData c₀ Nm) where
  /-- the radius on which the phase identity holds. -/
  ρ : ℝ
  /-- ... which is positive. -/
  hρ : 0 < ρ
  /-- the `b`-tongue, direction `α₁`. -/
  b : ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e → e ∉ Mandelbar →
    ∃ φ : ℂ → ℂ, Work.ParamRays.IsCritBottcher e φ ∧ ∃ m : ℕ,
      |Work.GATE.deviation φ Work.EL.alpha1 ((Work.EL.F e)^[m] e)| < Work.Final.windowEps ∧
      Work.GATE.deviation φ Work.EL.alpha1 e =
        Work.GATE.deviation φ Work.EL.alpha1 ((Work.EL.F e)^[m] e) / (1024 : ℝ) ^ m
  /-- the `ι b`-tongue, direction `α₂`. -/
  iota : ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e →
    e ∉ Mandelbar →
    ∃ φ : ℂ → ℂ, Work.ParamRays.IsCritBottcher e φ ∧ ∃ m : ℕ,
      |Work.GATE.deviation φ Work.EL.alpha2 ((Work.EL.F e)^[m] e)| < Work.Final.windowEps ∧
      Work.GATE.deviation φ Work.EL.alpha2 e =
        Work.GATE.deviation φ Work.EL.alpha2 ((Work.EL.F e)^[m] e) / (1024 : ℝ) ^ m

/-- **The phase residual gives the two parameter windows** (via `Work.GATE2.window_of_phase`, with
`φ = varphiCrit e`, `Work.Bottcher.isCritBottcher_varphiCrit`). -/
theorem PhaseResidual.toWindows {c₀ : ℂ} {Nm : Set ℂ} {TD : Work.GATE.TransitData c₀ Nm}
    (PR : PhaseResidual c₀ Nm TD) :
    (∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e →
        e ∉ Mandelbar → |Work.ParamRays.extAngle e - Work.Final.alpha1| < Work.Final.windowEps) ∧
      (∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e →
        e ∉ Mandelbar → |Work.ParamRays.extAngle e - Work.Final.alpha2| < Work.Final.windowEps) := by
  constructor
  · refine ⟨PR.ρ, PR.hρ, fun e he ht hM => ?_⟩
    obtain ⟨φ, hφ, m, hbound, hid⟩ := PR.b e he ht hM
    exact window_of_phase Work.GATE.alpha1_quarter.1 Work.GATE.alpha1_quarter.2 hM hφ hid hbound
  · refine ⟨PR.ρ, PR.hρ, fun e he ht hM => ?_⟩
    obtain ⟨φ, hφ, m, hbound, hid⟩ := PR.iota e he ht hM
    exact window_of_phase Work.GATE.alpha2_quarter.1 Work.GATE.alpha2_quarter.2 hM hφ hid hbound

/-! ## The assembly -/

/-- **`TwoSided` from the two parameter windows.**  This is the assembly of
`Work.GATE.twoSided_of_residual` with the per-parameter gate residual replaced by its *conclusion*:
SEG (`Work.GATE.Segment.seg_tongues`) produces the two tongue parameters on a segment in `Nm`, and
the two window statements put their external angles in the windows. -/
theorem twoSided_of_phaseWindows {c₀ : ℂ} {Nm : Set ℂ} (hOpen : IsOpen Nm)
    (hfront : c₀ ∈ frontier Nm) (TD : Work.GATE.TransitData c₀ Nm)
    (h₁ : ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e →
      e ∉ Mandelbar → |Work.ParamRays.extAngle e - Work.Final.alpha1| < Work.Final.windowEps)
    (h₂ : ∃ ρ > 0, ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e →
      e ∉ Mandelbar → |Work.ParamRays.extAngle e - Work.Final.alpha2| < Work.Final.windowEps) :
    Work.GATE.TwoSided c₀ Nm := by
  obtain ⟨ρ₁, hρ₁, hg₁⟩ := h₁
  obtain ⟨ρ₂, hρ₂, hg₂⟩ := h₂
  intro r hr
  set r' : ℝ := min (min r ρ₁) ρ₂ with hr'def
  have hr' : 0 < r' := lt_min (lt_min hr hρ₁) hρ₂
  obtain ⟨x, y, hseg, e₁, he₁, e₂, he₂, hM₁, hM₂, ht₁, ht₂⟩ :=
    Work.GATE.Segment.seg_tongues hOpen hfront TD hr'
  refine ⟨x, y, fun z hz => ⟨(hseg hz).1, ?_⟩, e₁, he₁, e₂, he₂, hM₁, hM₂,
    Work.GATE.mem_window_of_abs_lt ?_, Work.GATE.mem_window_of_abs_lt ?_⟩
  · exact Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) (hseg hz).2
  · exact hg₁ e₁ ⟨(hseg he₁).1, Metric.ball_subset_ball
      (le_trans (min_le_left _ _) (min_le_right _ _)) (hseg he₁).2⟩ ht₁ hM₁
  · exact hg₂ e₂ ⟨(hseg he₂).1, Metric.ball_subset_ball (min_le_right _ _) (hseg he₂).2⟩ ht₂ hM₂

/-- **`Work.GATE.TwoSided c₀ Nm` from the phase residual** — the entry point of this module, with a
hypothesis list containing no gate object: PARIMPL's transit data (the tongue predicates are
*definitions* of `Work.GATE`), and `PhaseResidual`. -/
theorem twoSided_of_phaseResidual {c₀ : ℂ} {Nm : Set ℂ} (hOpen : IsOpen Nm)
    (hfront : c₀ ∈ frontier Nm) (TD : Work.GATE.TransitData c₀ Nm)
    (PR : PhaseResidual c₀ Nm TD) : Work.GATE.TwoSided c₀ Nm :=
  twoSided_of_phaseWindows hOpen hfront TD PR.toWindows.1 PR.toWindows.2

/-! ## The reduction: GATE's machinery implies the phase identity -/

/-- **`PhaseResidual` from GATE's per-parameter gate residual.**  A `Work.GATE.GateResidual e α`
supplies `bd : BranchData φ α` and `BaseWindow bd e`, i.e. `e = Λ^[m] p` with the base point `p` of
the tube and `|deviation φ α p| < windowEps`; `Work.GATE.deviation_iterate` then gives exactly the
phase identity `deviation φ α e = deviation φ α p / 1024^m` at `p = (F_e)^[m] e` — so the new
residual is *implied by* (hence strictly weaker than) the design's `G1`+`G2`+`G3`, and the
tube/branch objects are not part of it. -/
def phaseResidual_of_branchResidual {c₀ : ℂ} {Nm : Set ℂ} {TD : Work.GATE.TransitData c₀ Nm}
    (TR : TongueBranchResidual c₀ Nm TD) : PhaseResidual c₀ Nm TD where
  ρ := TR.ρ
  hρ := TR.hρ
  b := by
    intro e he ht hM
    obtain ⟨φ, hφ, bd, hF, ⟨bw⟩⟩ := TR.b e he ht hM
    refine ⟨φ, hφ, bw.m, ?_, ?_⟩
    · have h := bw.hwin
      rw [← Work.GATE.BaseWindow.iterate_eq bw] at h
      simpa [hF] using h
    · have h := Work.GATE.deviation_iterate bd bw.hpS bw.m
      rw [← bw.hbase] at h
      rw [← Work.GATE.BaseWindow.iterate_eq bw, hF] at h
      exact h
  iota := by
    intro e he ht hM
    obtain ⟨φ, hφ, bd, hF, ⟨bw⟩⟩ := TR.iota e he ht hM
    refine ⟨φ, hφ, bw.m, ?_, ?_⟩
    · have h := bw.hwin
      rw [← Work.GATE.BaseWindow.iterate_eq bw] at h
      simpa [hF] using h
    · have h := Work.GATE.deviation_iterate bd bw.hpS bw.m
      rw [← bw.hbase] at h
      rw [← Work.GATE.BaseWindow.iterate_eq bw, hF] at h
      exact h

end Work.GATE2
