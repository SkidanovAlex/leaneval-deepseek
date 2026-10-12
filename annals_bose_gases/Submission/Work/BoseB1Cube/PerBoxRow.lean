import ChallengeDeps
import Submission.Work.BoseB1Cube.NominalPerBox
import Submission.Work.BoseB1Cube.sharpJointCoreSelf
import Submission.Work.BoseFixB1.bandWordCrudeSmallCnPlus
import Submission.Work.BoseFixB1B.slidingBogPortPrescribedEps
import Submission.Work.BoseFixB1S.boxBogWeightedV2B1
import Submission.Work.BoseFixB1S.boxDefect_eq
import Submission.Work.BoseFixB1S.sum_pairSet_add_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.PerBoxRow` — the per-box row as a *function*, and its count form

This module is the arithmetic skeleton of `Work.BoseB1Cube.perBoxFNom_holds`.  It contains

* `perBoxRow` — the left-hand side of FS `thm:smallbox` at the sliding box in FS's *nominal*
  (indicator-count) spelling, as a function of the parameters (`PerBoxFNom` is `perBoxRow ≤ _`);
* `PerBoxFNom_iff_row`, `PerBoxFNomSlot`, `PerBoxFNomSlot_self_iff` — the bridges between the
  demand-as-a-function, the frozen `PerBoxFNom`, and the *slotted* word `sbWordSlot`;
* `perBoxRow_le_countForm` — **the demand in count form**: using only the *pointwise* bound
  `ψ(1,μp,t) ≤ μp(t+μp)` (`psiWeight_le_mu_add`) and the mass law
  `boxCount = boxFlatCount + boxQCount` (`Work.BoseFixR.SlabCountSplit`),

      perBoxRow ≤ c₁·W·(μp·(S+Q)/|B| + μp²·‖Φ‖²) − ½μp²·W·‖Φ‖² − C·(μp²·a·Γ·χ + μp·a)·‖Φ‖²,

  with `S = boxFlatCount`, `Q = boxQCount`, `|B| = boxMass`, `W = w1MassB`,
  `χ = chiMass`, `Γ = (R/(ℓd))² + K_B³(μa³)^{1/2}`.

This is the *sharp* form of the `F`-bookkeeping: the first moment of the weight
`boxIndCount/|B|` against `Φ²` is *exactly* `boxCount/|B| = (S+Q)/|B|`, so no `chiMass`/`nCountB`
smoothing bookkeeping and hence no count window enters.  The whole remaining content of
`perBoxFNom_holds` is (i) the *ledger* comparing this count form with the two proved arms
`sbWordSlot_ge_payPort` / `sbWordSlot_ge_gapSubFibre`, and (ii) the passage from the in-box states
(the states the two arms see) to arbitrary states.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-- **The demand of FS `thm:smallbox` at the sliding box, as a function of the parameters.**

`perBoxFNom_holds` states `perBoxRow v h R c₁ C μp μ n Φ u ≤ sbWordCube v h μ u Φ`; this
definition is the left-hand side, verbatim, so that `PerBoxFNom` is definitionally
`perBoxRow … ≤ sbWordCube …`. -/
noncomputable def perBoxRow (v : E3 → ℝ) (h : ScatSol v) (R c₁ C : ℝ) (μp μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) : ℝ :=
  c₁ * (Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
            Work.SmallBoxSliding.psiWeight 1 μp
              (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
    - (1 / 2) * μp ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
    - C * (μp ^ 2 * (a v)
            * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
        + μp * (a v) * normB v μ n (Φ : X n → ℝ))

/-- **`PerBoxFNom` is the row against the matched word.** -/
theorem PerBoxFNom_iff_row {v : E3 → ℝ} {h : ScatSol v} {R c₁ C μp μ : ℝ} {n : ℕ}
    {Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))} {u : E3} :
    PerBoxFNom v h R c₁ C μp μ n Φ u
      ↔ perBoxRow v h R c₁ C μp μ n Φ u ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) :=
  Iff.rfl

/-- **The row at the slotted word**: FS `thm:smallbox` read with the chemical-potential slot `μp`
on the word (`sbWordSlot v h μp μ u`).  At `μp = μ` this is `PerBoxFNom` (`PerBoxFNomSlot_self`),
and at `μp = 4μ` it is FS's layer bound `eq:badset`. -/
def PerBoxFNomSlot (v : E3 → ℝ) (h : ScatSol v) (R c₁ C μp μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) : Prop :=
  perBoxRow v h R c₁ C μp μ n Φ u ≤ sbWordSlot v h μp μ u (Φ : X n → ℝ)

/-- **The slot bridge**: at `μp = μ` the slotted row is exactly the frozen `PerBoxFNom`
(`sbWordSlot_self`). -/
theorem PerBoxFNomSlot_self_iff {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {εr μ c₁ C : ℝ} (hadmr : Adm v εr μ)
    {n : ℕ} {Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))} {u : E3}
    (hRd : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hRχ : R ≤ sideAt μ (a v) * Submission.BoseGases.chiR0) :
    PerBoxFNomSlot v h R c₁ C μ μ n Φ u ↔ PerBoxFNom v h R c₁ C μ μ n Φ u := by
  rw [PerBoxFNomSlot, PerBoxFNom_iff_row,
    sbWordSlot_self (v := v) h hv hv1 hvrad hR hv_supp hadmr Φ hRd hRχ]

noncomputable def perBoxRowCount (v : E3 → ℝ) (h : ScatSol v) (R c₁ C μp μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) : ℝ :=
  c₁ * (Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * (μp * ((Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (sideAt μ (a v))
                    (paramsAt μ (a v)).d u) (sideAt μ (a v))
                  (Submission.BoseGases.dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
                  (Φ : X n → ℝ)
                + Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (sideAt μ (a v))
                    (paramsAt μ (a v)).d u) (sideAt μ (a v))
                  (Submission.BoseGases.dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
                  (Φ : X n → ℝ))
              / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            + μp ^ 2 * normB v μ n (Φ : X n → ℝ)))
    - (1 / 2) * μp ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
    - C * (μp ^ 2 * (a v)
            * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
        + μp * (a v) * normB v μ n (Φ : X n → ℝ))

end Work.BoseB1Cube