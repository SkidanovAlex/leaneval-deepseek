import ChallengeDeps
import Submission.Work.BoseFixB1B.matchedWindowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.Cube.Defs` — the a-priori chapter at the **matched (single cube
# cutoff)** window

## Why this file exists

The frozen sliding word of this chapter, `sbWord = sbKin + sbPot`, mixes FS's two cutoffs:

* its potential slot `sbPot = qLHSwordB` carries the kernels `wSmallPair`/`wSmall1Pair`, whose
  window is the **cube** bump `chiSmallB M ℓ d u = chiScale ℓ · chiSmall M ((ℓd)⁻¹ • · − u)`
  (`Submission/Work/DLSmallKernels.lean`), and whose `F`-weight and mass `chiMass` are built from
  the same bump (`nCountB`);
* its kinetic spectral slot `sbKin = tBwordBInd` is windowed by the **ball** product
  `chiB ℓ d u = chiScale ℓ · chiScale (ℓd) (· − (ℓd) • u)` (`Submission/Work/UBBInputs8/Defs.lean`).

The two windows have different supports: `supp (chiB ℓ d u) = ball (0,ℓ/2) ∩ ball ((ℓd)•u, ℓd/2)`
while `supp (chiSmallB M ℓ d u) = ball (0,ℓ/2) ∩ ((ℓd)•u + acube (ℓd))`.  At a *corner* box — a
`u ∈ interiorSet ℓ d μ` whose two **balls** are disjoint while the small **cube** still meets the
big ball — one has `chiB ℓ d u ≡ 0` while `chiSmallB M ℓ d u ≢ 0`
(`Work.BoseFixB1S.exists_window_vacuous_but_box_meets_chiSmall`,
`Work.BoseFixB1.chiB_eq_zero_of_ball_disjoint`), hence

    sbKin = tbGapCoeff (ℓd) ε_T · cnPlusBoxInd   (the spectral half is *identically zero*)

(`Work.BoseFixB1.corner_tBwordKinInd_eq_zero`) while the kernels, the `F`-weight and the
`χ`-mass stay alive.  **This is a *modelling* difference, not a refutation**: on such a corner box
the whole two-factor cutoff is superpolynomially small (`Work.BoseFixB1.chiSmallB_corner_flat`:
`chiSmallB ≲ d^N` for every `N`), so the per-box demand is suppressed while the *un-suppressed*
credit `C·μ(a v)‖Φ‖²` of FS's error bracket pays it — see `Cube/FINDING_cubeRepoint.md` §§1–2 for
the machine-checked facts and the arithmetic (`d^{2N}·t^{-0.458} → 0`, `t = μ(a v)³`).  The mismatch
does block *pointwise-in-`u`* comparisons of the two slots, and the instruments that pay FS's
Appendix in the fleet's work — the rung-4 payment `Work.BoseFixB1S.a0A2PaymentAdm_holds` and the
Bogoliubov port `Work.BoseFixB1B.slidingBogPort_proved : SlidingBogPort` — are stated at the
**cube** window.

## The single-cutoff re-point, and this file's place in it

FS's own modelling (`final_v2.tex` l.3522, `eq:chiBdefinition`) uses **one** `χ_B` in both slots.
The fleet's matched vocabulary — `Submission.Work.BoseFixB1B.matchedWindowDefs` — is that
single-cutoff chapter: `sbKinCube` (the frozen kinetic word with its spectral slot read at
`chiSmallB`) and `sbWordCube = sbKinCube + sbPot`.  The two instruments that actually *pay* the
pairing, the rung-4 payment `Work.BoseFixB1S.a0A2PaymentAdm_holds` and the Bogoliubov port
`Work.BoseFixB1B.slidingBogPort_proved : SlidingBogPort`, are both stated at that window, so
running the chapter there removes the window comparison (and the node-fragment it carries).

This module is the **interface** of the re-pointed chapter:

* `SmallBoxCollectedCube` — FS `thm:smallbox` integrated over the small boxes, at the single cube
  cutoff (the cube twin of `Work.BoseFixB1.SmallBoxCollected`).

The rest of the chapter's targets do **not** change: FS `eq:aprioriRn+`
(`Work.BoseFixB1.AprioriHLambdaIneq`), FS's particle window (`Work.BoseFixB1.WindowBridge`) and
`NodeB1B` itself mention only `RPsi` (already `chiSmallB`-based), `cnPlus`, `wordB` and `normB` —
no small-box word at all.  Hence only the two *inputs* `SlidingB`/`SmallBoxCollected` are replaced,
by `Work.BoseFixB1B.SlidingBCube`/`SmallBoxCollectedCube`, and the assembly of
`Cube/Assembly.lean` is the frozen one with the substitution `sbWord ↦ sbWordCube` (possible
because neither `Assembly.lean` nor `Bridge.lean` uses any property of the word beyond the two
inequalities it is given).

## Relation to the frozen chapter

`Work.BoseFixB1B.sbKinCube`'s spectral slot is the frozen one at the *larger* window
(`supp (chiB) ⊆ supp (chiSmallB)`, both continuous and normalised), so `sbWord` is pointwise
`≤ sbWordCube` up to a universal constant; consequently `SmallBoxCollected` (frozen) *implies*
`SmallBoxCollectedCube`, i.e. the matched statement is the **weaker**, true one — see
`Cube/FINDING_cubeRepoint.md` §3.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **FS `thm:smallbox` integrated over the small boxes, at the single cube cutoff** — the cube
twin of `Work.BoseFixB1.SmallBoxCollected`, with the matched word
`Work.BoseFixB1B.sbWordCube` in place of the frozen `sbWord`.

There are `ε₀ > 0` and `C ≥ 0` such that for admissible `μ` with `J ≤ K_B³` and every low box
state,

`0 ≤ R_Ψ` and
`R_Ψ ≤ ∫_{ℝ³} sbWordCube du + 4πμ²(a v)ℓ³(1 + C K_B³(μ(a v)³)^{1/2})‖Φ‖²`,

with `R_Ψ = Work.BoseFixB1.RPsi` (unchanged: it is `chiSmallB`-based in both chapters) and the
integrand the matched small-box word `sbWordCube` (kinetic `eq:appTB` **at the cube window**
`chiSmallB`, plus the potential `eq:HBU` at the same-window kernels).

This is FS's own statement: `eq:chiBdefinition` uses one `χ_B` for both the kinetic and the
potential slot.  Its two halves are (i) the PROVED matched chained bound
`Work.BoseFixB1B.sbWordCube_ge_a0Main_add_boxA2` (the rung-4 payment and the Bogoliubov port at
the cube window) and (ii) the `F`-row (the density/deviation row) which is the live residual of
the matched chapter; see `Cube/FINDING_cubeRepoint.md` §4. -/
def SmallBoxCollectedCube (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      IsLowB v h J μ n Φ →
        0 ≤ RPsi v h μ Φ ∧
        RPsi v h μ Φ
          ≤ (∫ u : ℝ³, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
            + 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
                * (1 + C * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n Φ

/-- The matched word is the frozen word plus the kinetic window swap: recording the *definitional*
identity `sbWordCube = (sbKinCube − sbKin) + sbWord`.  It is the only algebraic relation between
the two chapters' words used anywhere in `Cube/`, and it makes the transfer
`SmallBoxCollected ⟹ SmallBoxCollectedCube` a statement about
`∫_u (sbKinCube − sbKin)` alone. -/
theorem sbWordCube_eq_sbWord_add {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (u : ℝ³) (Φ : X n → ℝ) :
    Work.BoseFixB1B.sbWordCube v h μ u Φ
      = (Work.BoseFixB1B.sbKinCube v μ u Φ - sbKin (v := v) μ (paramsAt μ (a v)).M u Φ)
        + sbWord h μ u Φ := by
  rw [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube, sbWord]
  ring

/-- **FS `thm:smallbox` at the sliding box, at the single cube cutoff** — the cube twin of
`Work.BoseFixB1.PerBoxF`, with `Work.BoseFixB1B.sbWordCube` on the right.  Its only difference from
the frozen per-box target is the window of the word's *kinetic spectral slot*.

This is the per-`u` residual the matched chapter needs; it is the statement in which the
`chiB`/`chiSmallB` mismatch is *absent* — the kinetic slot is read at the same bump `chiSmallB`
that the kernels, the count `nCountB`, the mass `chiMass` and the `F`-weight are built from.  In
particular the corner configurations of `Work.BoseFixB1.corner_tBwordKinInd_eq_zero` (where the
frozen word's spectral half vanishes identically) are *not* degenerate here: the matched word's
spectral slot is alive exactly where the kernels are. -/
def PerBoxFCube (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C : ℝ)
    (μ : ℝ) (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v)))
    (u : EuclideanSpace ℝ (Fin 3)) : Prop :=
  c₁ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
    - (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
        normB v μ n (Φ : X n → ℝ)
    - C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
            + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
          normB v μ n (Φ : X n → ℝ)
        + μ * (a v) * normB v μ n (Φ : X n → ℝ))
  ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)

end Work.BoseFixB1
