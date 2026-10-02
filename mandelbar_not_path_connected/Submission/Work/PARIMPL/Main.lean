/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.Main` — the holder structure and the two deliverables

Item §4 of `Submission/Work/NOTES_LEAD_mandelbar_residuals.md`: the `FinalInputs` fields owned by
this area,

* `Nm` — the implosion side (from `Work.PARIMPL.ParNormal`),
* `impl : ImplosionSide c₀ z₁ Nm` — `Work.PARIMPL.ParImplInputs.impl`,
* `noPath` — `Work.PARIMPL.ParImplInputs.noPath`, the path form of `hLB`.

The holder structure `ParImplInputs` collects every residual of §1.1–§1.4 as a *named hypothesis*:
the parameter normal form, MATCH, TRANS, LEAK, the `FatouCoord` fix (`φa_shift`, `Pg`), the
`Z`-decay, the NAKANE input (joint continuity of the Green function), and the FBif input that
`Nm` accumulates at `c₀`.  Everything is then *derived*: nothing below is a `sorry`.

## What a caller needs

`Work.PARIMPL.ParImplInputs.noPath` is the statement

  `∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mb) → c₀ ∉ closure (range γ ∩ Nm)`

of the endgame.  `Work.PARIMPL.ParImplInputs.impl` is the implosion-side data; for the
`Work.Final.ImplosionSide` of the final wiring, use `Work.PARIMPL.Bridge.implSide_toFinal`
(module `Submission.Work.PARIMPL.Bridge`, which imports `Submission.Work.Final.Defs`).
-/
import Submission.Work.PARIMPL.Path
import Submission.Work.PARIMPL.periodFiveGone
import Submission.Work.PARIMPL.norm_S_le_rot
import Submission.Work.PARIMPL.approxEcal_step_rot
import Submission.Work.PARIMPL.approxEcal_transit_rot

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The residuals of the implosion side**, in one holder structure (§4 of
`NOTES_LEAD_mandelbar_residuals.md`).

The flower of the root arc is *not* a field: a structure whose field type mentions
`Work.FatouCoord.ParabolicFlower (Ft c₀) (gtc c₀) z₁` makes the elaborator diverge (see the
encoding remark in `Submission/Work/PARIMPL/Match.lean`).  Its two coordinates `φa` (attracting)
and `Ψ` (repelling) and its petal `Pa` are fields, and the caller instantiates them with
`fl.Pa`, `fl.φa`, `fl.Ψ`.  The two flower facts used by the assembly — `Pa` is open and `φa` is
differentiable on it — are fields as well (they are `fl.isOpen_Pa` and `fl.φa_fatou.1.2.1`). -/
structure ParImplInputs where
  /-- the root-arc parameter. -/
  c₀ : ℂ
  /-- the root-parabolic structure of `c₀` (FSeed / FQC / FBif). -/
  d : Work.EL.RootParabolic c₀
  /-- the parameter normal form (HS Prop. 4.1, uniform in `c`). -/
  P : ParNormal d
  /-- the attracting petal of the flower. -/
  Pa : Set ℂ
  /-- the attracting Fatou coordinate of the flower. -/
  φa : ℂ → ℂ
  /-- the repelling coordinate of the flower. -/
  Ψ : ℂ → ℂ
  /-- **MATCH** (§1.2). -/
  M : MatchData d P Pa φa Ψ
  /-- **TRANS** (§1.3). -/
  T : TransitData d P Pa φa Ψ M
  /-- **LEAK** (§1.4). -/
  L : LeakData d P Pa φa Ψ M T
  /-- the implosion side accumulates at `c₀` (the FBif bifurcation side, `Work.Final.BifSide`;
  equivalently `Np ⊆ Mb`, see `Submission/Work/PARIMPL/NOTES.md`). -/
  c_mem_closure : c₀ ∈ closure P.Nm
  /-- the `FatouCoord` fix of §3.1: `φa ∘ F = φa + 1` on the petal, together with the
  `g`-invariant sub-petal `Pg`. -/
  fix : FlowerFix d (Ft c₀) (gtc c₀) d.z₁ Pa φa
  /-- the `Z`-decay of the repelling side (`NOTES_LEAD_mandelbar_flower.md` §A.7). -/
  zdecay : ZDecay d Ψ
  /-- **NAKANE**: the joint continuity of the Green function of the family, in the open-escape
  form used by the robust-leak argument (I2). -/
  greenOpen : GreenEscapeOpen
  /-- the attracting petal is open (`fl.isOpen_Pa`). -/
  isOpen_Pa : IsOpen Pa
  /-- the attracting coordinate is differentiable on the petal (`fl.φa_fatou.1.2.1`). -/
  diff_φa : DifferentiableOn ℂ φa Pa
  /-- the entry point of the critical orbit at `c₀` lies in the petal (`Work.PARIMPL.nEnter_spec`
  for `M.nIn = nEnter d fl`). -/
  entry_mem : entryPt P M.nIn c₀ ∈ Pa
  /-- the critical Écalle height vanishes (FQC, `Work.Final.RootArc.critHeight = 0`). -/
  critHeight_zero : (φa (entryPt P M.nIn c₀)).im = 0

namespace ParImplInputs

variable (H : ParImplInputs)

/-- **The implosion side `Nm`** of §2.3 (I1), as the set of the parameter normal form. -/
def Nm : Set ℂ := H.P.Nm

/-- The implosion side is open. -/
theorem isOpen_Nm : IsOpen H.Nm := H.P.isOpen_Nm

/-- The root parameter does not lie on the implosion side (`a₂ c₀ = 0`). -/
theorem notMem_Nm : H.c₀ ∉ H.Nm := by
  intro h
  have h2 : H.P.a2 H.c₀ < 0 := h.2
  rw [H.P.a2₀] at h2
  exact absurd h2 (lt_irrefl 0)

/-- The root parameter lies on the frontier of the implosion side. -/
theorem mem_frontier_Nm : H.c₀ ∈ frontier H.Nm := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨H.c_mem_closure, ?_⟩
  change H.c₀ ∈ closure (H.P.Nm)ᶜ
  rw [H.P.isOpen_Nm.isClosed_compl.closure_eq]
  exact H.notMem_Nm

/-- **The implosion side data** (`impl : ImplosionSide c₀ z₁ Nm` of §4): `Nm` is open, it
accumulates at `c₀` (the FBif input), and the period-`5` point near `z₁` has disappeared on it
(`Work.PARIMPL.periodFiveGone`, derived from the normal form's `swap`). -/
theorem impl : ImplSide H.c₀ H.d.z₁ H.Nm :=
  H.P.toImplSide H.c_mem_closure (periodFiveGone H.d H.P)

/-- **`noPath`** — the `hLB` of the endgame, in the path form: *no path inside the mandelbar*
approaches `c₀` through the implosion side.  This is the form consumed by
`Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch`. -/
theorem noPath : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mandelbar) →
    H.c₀ ∉ closure (Set.range γ ∩ H.Nm) :=
  Work.PARIMPL.noPath H.d H.P H.M H.T H.L H.isOpen_Pa H.diff_φa H.entry_mem
    H.critHeight_zero

end ParImplInputs

end Work.PARIMPL
