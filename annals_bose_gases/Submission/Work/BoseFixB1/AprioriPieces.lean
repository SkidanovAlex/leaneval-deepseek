import ChallengeDeps
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.AprioriPieces` — the interface pieces of the a-priori chapter

This module fixes the *interface* through which the two analytic pieces of the
a-priori inequality (`Work.BoseFixB1.AprioriHLambdaIneq`) are dispatched, so
that they can be proved in parallel by two colleagues:

* `PerBoxF` — FS `thm:smallbox` at the sliding box `B(u)`, in the
  `F`-weighted (fibre) form used by the a-priori inequality: on the good set
  `G`, the localised word of the box `B(u)` dominates
  `c₁·(∬w_{1,B(u)})·∫_Λ Φ²F(n_{B(u)}(x)/|B(u)|) − ½μ²(∬w_{1,B(u)})‖Φ‖²`, up
  to the FS error terms.  (`Piece 1`, proved in `PerBoxFWeight`.)
* `OffGoodLower` — the crude per-box lower bound outside the good set
  (FS `eq:badset`): the localised word is bounded below by
  `−C·(χ_{B(u)}²-mass)`.

The integration over `u` (mass identities, bad-band bookkeeping) is
`Piece 2` (`AprioriIntegrate`); the final assembly (constant bookkeeping,
`ε₀` choice, the low-state step) is in
`Work.BoseFixB1.aprioriHLambdaIneq_holds`.

## NOTE — the `F`-coefficient is FS's universal `c ∈ (0,1/2)`

`Defs.RPsiB` takes the convexity constant of `psiWeight` as a parameter and
`Defs.RPsi` instantiates it at `c = 1`.  FS's `thm:smallbox` supplies the
`F`-weight only with a universal `0 < c < 1/2` (FS l.3907 and l.4122 use the same
`c`; the corpus's `DLWire.smallbox_dl_energy_bound` gives `1/18`).  Both readings
of the remainder are true — the per-box analysis gives
`c₁·R_Ψ ≤ ∫sbWord + 4πμ²aℓ³(1+Cκ)‖Φ‖²` (`PerBoxF` integrated, `c₁ < 1/2`), from
which the coefficient-`1` form `SmallBoxCollected` follows through the
*difference* `R_Ψ − ∫sbWord` (using `J√t ≤ κ`); see
`FINDING_RPsiB_c_normalisation.md` §3.  What one must **not** do is divide the
per-box bound by `c₁` *before* cancelling the background `4πμ²aℓ³`.  The
`c`-explicit form is available as `Work.BoseFixB1.smallBoxCollectedC_holds`.

## Conventions

Everything is at FS's parameters: `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`,
`M = (paramsAt μ (a v)).M`, `t = μ (a v)³`, `K_B = (paramsAt μ (a v)).KB`.  The state
`Φ` is a `BoxState n ℓ` (smooth, symmetric) and `normB v μ n Φ` is its `L²(abox n ℓ)`-norm
square.  All constants are free universal constants (HANDOFF: only `lhyC` and the
error exponents are rigid).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false


/-- **FS `thm:smallbox` at the sliding box `B(u)`, `F`-weighted (fibre) form.**

On the good set `G`, the localised word `sbWord h μ u Φ` of the box `B(u)`
dominates `c₁·(∬w_{1,B(u)})·∫_Λ Φ²F(n_{B(u)}(x)/|B(u)|)` minus the background
`½μ²(∬w_{1,B(u)})‖Φ‖²`, up to the FS error terms
`C μ²(a v)((R/(dℓ))² + K_B³(μ(a v)³)^{1/2})·(χ_{B(u)}²-mass)·‖Φ‖² + C μ(a v)‖Φ‖²`.

Here `F = psiWeight 1 μ` (FS's `F(t) = c(t−μ)²/(1+tμ⁻¹)` with `c = 1`) and
`n_{B(u)}(x)/|B(u)| = nCountB M ℓ d u x / chiMass M ℓ d u` is the smooth local
density (the `χ_B²`-mass normalisation of the repaired `Defs.RPsiB`; the nominal
volume `boxVol` is **not** the right normaliser, see
`FINDING_windowBridge_RPsiB_normalisation.md`).  The `−½μ²` background has
coefficient exactly `1/2` (FS's `−½μ²∬w_{1,B}`), which is what makes the
telescoping `∫_{I₋} ½μ²∬w_{1,B} = 4πμ²(a v)ℓ³` cancel the mean-field energy. -/
def PerBoxF (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C : ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : EuclideanSpace ℝ (Fin 3)) : Prop :=
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
  ≤ sbWord h μ u (Φ : X n → ℝ)

/-- **The crude per-box lower bound off the good set** (FS `eq:badset`): on the
discarded boxes the localised word is bounded below by `−C·(χ_{B(u)}²-mass)`. -/
def OffGoodLower (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (C : ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : EuclideanSpace ℝ (Fin 3)) : Prop :=
  -C * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
    ≤ sbWord h μ u (Φ : X n → ℝ)

end Work.BoseFixB1
