/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Inputs` — the sibling exports that the implosion endgame consumes

Area `Submission/Work/PARIMPL2/` (namespace `Work.PARIMPL2`) owns the **construction of the three
data bundles** that the delivered area `Submission/Work/PARIMPL/` takes as inputs:

* `Work.PARIMPL.MatchData` — MATCH (items (M-in), (M-out), (T-e), `entering` of
  `Submission/Work/NOTES_LEAD_mandelbar_residuals.md` §1.2);
* `Work.PARIMPL.TransitData` — TRANS (§1.3/§1.4), including `cont` and the uniform lock-step
  transit `UT` (`NOTES_LEAD_mandelbar_gate2transport.md` §5);
* `Work.PARIMPL.LeakData` — LEAK (§1.4), with the leak centre chosen at the ρ-maximiser of
  `NOTES_LEAD_mandelbar_gaps2.md` §4;

so that `Work.PARIMPL.noPath` and `Work.PARIMPL.ParImplInputs.impl` become unconditional modulo the
**sibling exports** (FlowerGlue, ELAssembly, root/seed, NAKANE, GATE2) listed in `NOTES.md` §2.

This file fixes the *interface*: the structures below are exactly the sibling exports, in the
sibling's own vocabulary, and nothing else.  Two facts are worthwhile emphasising:

* `Work.NAKANE.greenEscapeOpen : Work.PARIMPL.GreenEscapeOpen` and
  `Work.PARIMPL.Nm_mem_closure (d) (P) : c₀ ∈ closure P.Nm` are **proved**, so the Norbert/Nakane
  input `greenOpen` and the FBif input `c_mem_closure` are *not* hypotheses here;
* `Work.PARIMPL.exists_parNormal d : Nonempty (ParNormal d)` is **proved**, so the parameter
  normal form `P : ParNormal d` is a *parameter* of every structure below (the caller picks its
  witness), not a hypothesis.

## Read `NOTES_FALSE_match_in.md` and `NOTES_FALSE_match_out.md` first

The two height comparisons of the MATCH item (the imaginary parts of the model coordinate
`approxU`/`approxUin` against the flower's `φa`/`Ψ`) were **stated with the wrong sign** in the
delivered `Work.PARIMPL.MatchData`: the model's approximate perturbed Fatou coordinate is a
*decreasing* Abel coordinate of the model (`Work.PARIMPL.approxEcal_step_rot`), whereas the
flower's `φa` and `Ψ` are *increasing* (`Work.FatouCoord.IsFatouCoordinateOn`,
`Work.FatouCoord.ParabolicFlower.Ψ_shift`); the two therefore compare with the **opposite**
sign, exactly as the (T-e) field already records (`approxU ∘ g = conj ∘ approxU − 1/2`, while
`φa ∘ g = conj ∘ φa + 1/2`).

That finding was reported (`Submission/Work/PARIMPL/NOTES.md` §0.0) and the delivered
`Work.PARIMPL.MatchData` now carries the **corrected** comparisons, so the single export
`Work.PARIMPL2.MatchExport` below feeds it directly.
-/
import Submission.Work.PARIMPL2.MatchCore
import Submission.Work.FatouCoordFix.All
import Submission.Work.NAKANE.GreenEscapeOpen

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

namespace Work.PARIMPL2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.PARIMPL (ParNormal MatchData TransitData LeakData TransitLockstep Win Wout transU
  approxU approxUin entryPt chartZeta ecalUin Ft gtc)

variable {c₀ : ℂ}

/-! ## The MATCH comparison -/

/-- **MATCH** is taken from `Work.PARIMPL2.MatchCore` (see that module): the *coordinate identity*
on the two windows — the shape in which FlowerGlue's identification/estimate, the Implosion
asymptotics and the chart consistency of `ParNormal` combine — from which the two height
comparisons are **derived** (`Work.PARIMPL2.match_in_of_coord`, `match_out_of_coord`). -/
abbrev MatchExport (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) (nIn : ℕ) := MatchCore d P Pa φa Ψ nIn

/-! ## The TRANS export -/

/-- **TRANS export** — the two sibling exports that `Work.PARIMPL.TransitData` consumes beyond
`MatchData`:

* the uniform lock-step transit **UT** (`NOTES_LEAD_mandelbar_gate2transport.md` §5), in the
  design's form `Work.PARIMPL2.LockstepAll` (every bounded box, not `∃ X₁`) — the uniform form of
  the exit matching of §1.3/§1.4 (the earlier unbounded `Work.GATE2.ExitTracked` is *false*, see
  the note §2, and the delivered `Work.PARIMPL.TransitLockstep` follows from `LockstepAll` by
  `Work.PARIMPL2.transitLockstep_of_lockstepAll`);
* the two **slit-plane** (branch) conditions of the construction of `transU`
  (`Work.PARIMPL.continuousOn_transU`): they are the statement that the entry point of the
  critical orbit sits in the two-sided annulus of the window, so that both logarithms of the
  construction are on the principal branch.  They are discharged by the window estimate
  `Re (approxUin) ≈ π/λ_c − R`, i.e. `‖chartZeta‖ ≈ 1/R` and `chartZeta.re < 0` — the content of
  `Work.Implosion.Approx.approxEcal_end_in` applied to `MatchData.entering` (see `NOTES.md` §4,
  item `cont`). -/
structure TransitExport (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) (nIn : ℕ) where
  /-- the radius on which the transit coordinate is continuous. -/
  ρ₁ : ℝ
  hρ₁ : 0 < ρ₁
  le_ρ₀ : ρ₁ ≤ P.ρ₀
  /-- **UT**: the uniform lock-step transit. -/
  UT : LockstepAll c₀ P.Nm (transU P nIn) nIn (fun c z => Ft c z) Pa φa Ψ
        ((φa (entryPt P nIn c₀)).re - (nIn : ℝ))
  /-- the first slit-plane condition of `transU`. -/
  slit₁ : ∀ c ∈ P.Nm ∩ ball c₀ ρ₁,
    Work.Implosion.mobius (P.a c) (chartZeta P c (entryPt P nIn c)) ∈ Complex.slitPlane
  /-- the second slit-plane condition of `transU`. -/
  slit₂ : ∀ c ∈ P.Nm ∩ ball c₀ ρ₁,
    Complex.sinh (P.a c * ecalUin P c (entryPt P nIn c)) / P.a c ∈ Complex.slitPlane

/-! ## The LEAK export -/

/-- **LEAK export** — the GATE2/ELAssembly side of the robust leak disc:

* the **leak centre** `y₀`, the real maximiser of `ρ w = log₁₀₂₄ G(Ψ w) − Re w` over the Stolz
  sector (`NOTES_LEAD_mandelbar_gaps2.md` §4, E3–E5), which is the number that GATE2's
  `TransitData.xLeak` must equal (`LeakData.yLeak = xstar − j₀`); chosen **real**, so that the
  `ι`-tongue `y₀ + 1/2` is the conjugate one and `ParabolicFlower.Psi_anti` applies;
* the equator leak at it (`Ψ y₀ ∉ K c₀`), which is the EL chain's `Work.EL.equatorLeak`
  assembled in `Work.ELAssembly.equatorLeak_of_inputs`;
* the **escape** of the two tongues (`b`-tongue `y₀` and `ι b`-tongue `y₀ + 1/2`) at some
  radius `r₀`: `GATE2`'s `exitTracked_escape*` / the bounded-integer tracking of
  `NOTES_LEAD_mandelbar_residuals.md` §1.4.  It is recorded in the *monotone* form (the
  implication `distZ < r/2 → c ∉ Mb` becomes *easier* as `r` decreases), so that a constructor
  may use any radius `r ≤ r₀`. -/
structure LeakExport (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) (nIn : ℕ) where
  /-- GATE2's leak centre `xLeak`: the real ρ-maximiser. -/
  y₀ : ℝ
  /-- the equator leak at the centre (`Work.EL.equatorLeak`). -/
  leak₀ : Ψ ((y₀ : ℝ) : ℂ) ∉ Work.EL.K c₀
  /-- the radius of the tongue escape. -/
  r₀ : ℝ
  hr₀ : 0 < r₀
  /-- **the tongue escape** of §1.4 at the radius `r₀`. -/
  escape : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ y : ℝ,
    (y = y₀ ∨ y = y₀ + 1 / 2) →
    Work.PARIMPL.distZ (transU P nIn c) ((y : ℝ) : ℂ) < r₀ / 2 → c ∉ Mandelbar

/-! ## The FlowerGlue/root exports and the bundled hypothesis list -/

/-- **The sibling hypothesis list of the implosion endgame.**  Everything in it is an export of
another area; nothing is a `Work.PARIMPL` field.

* `M`, `T`, `L` — the MATCH / TRANS / LEAK sibling exports above (FlowerGlue + Implosion,
  GATE2, ELAssembly);
* `zdecay` — the `Z`-decay of the repelling coordinate at the far end
  (`NOTES_LEAD_mandelbar_flower.md` §A.7; `Work.FlowerGlue.zDecay_of_parabolicBounds` produces it
  in the transfer form);
* `critHeight_zero` — the FQC/FinalFix root export: the critical Écalle height of the flower
  vanishes (`Work.FinalFix.RootArcHeightZero`). -/
structure SiblingInputs (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) (nIn : ℕ) where
  M : MatchExport d P Pa φa Ψ nIn
  T : TransitExport d P Pa φa Ψ nIn
  L : LeakExport d P Pa φa Ψ nIn
  /-- FlowerGlue: the `Z`-decay of the repelling coordinate. -/
  zdecay : Work.PARIMPL.ZDecay d Ψ
  /-- FQC/FinalFix: the critical Écalle height vanishes. -/
  critHeight_zero : (φa (entryPt P nIn c₀)).im = 0

end Work.PARIMPL2

end
