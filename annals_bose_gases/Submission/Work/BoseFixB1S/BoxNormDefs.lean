import ChallengeDeps
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.BoxNormDefs` — the a-priori `R_Ψ` at FS's **own** normaliser

Written by the holder of `Submission/Work/BoseFixB1S/LowCountWindowAllJ.lean`; see
`FINDING_LowCountWindowAllJ_session10.md` §§1, 3, 7 for why these objects exist.

FS's a-priori chapter reads its `F`-weight at the **sharp** local density `n(u)/|B(u)|`
(`final_v2.tex` l. 3658 with `eq:smallboxnn0n+`), where *both* the count and the volume are the
sharp box objects.  The corpus's `Work.BoseFixB1.RPsiB` instead reads it at the *smooth* density
`wbDens = nCountB/chiMass` — a smooth count over the `χ_B²`-mass.  The two differ by
`χ̂ := chiMass/boxMass`, which is **unbounded below on `goodSet`/`interiorSet`**, so the
`chiMass` form is strictly stronger than FS's theorem and cannot be supplied by any per-box input
at FS's own normaliser (the exact conversion needs `F(λt) ≤ K(F(t)+μ²)` with `K ≳ 1/χ̂`).

This file provides the **`boxMass`-normalised twins** of the `WB` objects (the smooth count kept,
the volume changed), so that a re-pointed chain can be built without touching the corpus's
`chiMass` vocabulary.  Only definitions here — nothing is asserted.

`Work.BoseFixB1.WB.Defs` for comparison:

    wbDens := (∫Φ²·nCountB)/(normB·chiMass)      → wbDensBox := (∫Φ²·nCountB)/(normB·boxMass)
    wbSig  := ∫_{I₋}wbMass·wbDens                → wbSigBox  := ∫_{I₋}wbMass·wbDensBox
    RPsiB  := ∫_{I₋}wbMass·(∫Φ²·F(nCountB/chiMass)) → RPsiBox := the same with `boxMass`
    wbU    := ∫_{I₋}(wbMass/chiMass)·χ_B(·)²     → wbUSharp := ∫_{I₋}(wbMass/boxMass)·1_{B(u)}(·)

`wbMass`/`wbW` carry no normaliser and are reused verbatim from `Work.BoseFixB1.WB.Defs`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The state-averaged local density at FS's own (`boxMass`) normaliser**: the `χ_B`-weighted
count of `Φ` divided by the *box volume* and by `‖Φ‖²`.  This is the corpus's `wbDens` with
`chiMass ↦ boxMass`. -/
def wbDensBox {v : ℝ³ → ℝ} (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) (u : ℝ³) : ℝ :=
  (∫ x in abox n (sideAt μ (a v)),
      (Φ x) ^ 2 * Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u x)
    / (Work.BoseBoxFix.normB v μ n Φ
        * Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)

/-- **`wbSigBox`**: the `u`-average of the `boxMass`-density against the localised one-body mass —
FS's `⟨ΣᵢU(xᵢ)⟩` up to the factor `wbW`. -/
def wbSigBox {v : ℝ³ → ℝ} (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) : ℝ :=
  ∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
    Work.BoseFixB1.wbMass v h μ u * wbDensBox h μ n Φ u

/-- **FS's `R_Ψ` at FS's own normaliser**: the configuration integral of `|Φ|²` against
`F(n(u)/|B(u)|)∬w_{1,B(u)}`, integrated over the interior `I₋`, with the density read at the
**box volume**. -/
def RPsiBox {v : ℝ³ → ℝ} (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) : ℝ :=
  ∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
    Work.BoseFixB1.wbMass v h μ u *
      (∫ x in abox n (sideAt μ (a v)),
        (Φ x) ^ 2 * psiWeight 1 μ
          (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x
            / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u))

/-- **FS's `U` at the box volume** (their `U(z) = 𝒞⁻¹∫_{I₋}|B(u)|⁻¹1_{B(u)}(z)∬w_{1,B(u)}du`,
unnormalised): the *sharp* box indicator, which is what makes `∫_Λ U = wbW` immediate
(`∫_Λ1_{B(u)} = boxMass`). -/
def wbUSharp {v : ℝ³ → ℝ} (h : ScatSol v) (μ : ℝ) (z : ℝ³) : ℝ :=
  ∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
    (Work.BoseFixB1.wbMass v h μ u
        / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
      * (Submission.BoseGases.dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u).indicator
          (fun _ => (1 : ℝ)) z

end Work.BoseFixB1S
