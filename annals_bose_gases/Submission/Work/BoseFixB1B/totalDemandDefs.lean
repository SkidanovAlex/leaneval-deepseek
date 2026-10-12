import ChallengeDeps
import Submission.Work.BoseFixB1B.perBoxFTotalInterfaces
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.totalDemandDefs` — the *demand* of the total-density per-box bound,
# as a function of a bare state

`Work.BoseFixB1B.PerBoxFTotal` is stated for a `Work.BoseKinLoc.BoxState` (a smooth symmetric
nonzero function), so its left-hand side — the **demand** — can only be evaluated at smooth states,
while the arity (localisation-removal) argument of
`Work.BoseFixB1B.perBoxFTotal_of_inBox` has to evaluate it at the *sharp* (box-indicator times
smooth) states that the slot-fibre decomposition produces.

This module isolates the demand as a function of a bare function `Ψ : X k → ℝ` (no smoothness, no
normalisation), together with the two bookkeeping lemmas that relate it to the corpus's objects:

* `totalDemand` — the left-hand side of `PerBoxFTotal` at the sliding parameters, as a function of
  `Ψ`; it is *homogeneous of degree two* and the `F`-weight is read at the state's own total
  in-box density `chiDensB`;
* `totalDemand_le_iff_PerBoxFTotal` — at a `BoxState` the demand inequality *is* `PerBoxFTotal`
  (definitional, after unfolding the sliding-parameter abbreviations);
* `fibreWord_eq_sbWord` — the slot-word `fibreWord` at the sliding parameters is the frozen word
  `sbWord`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The demand of the target at the sliding parameters**, as a function of a bare state `Ψ` of
`k` particles: precisely the left-hand side of `PerBoxFTotal`, with

* `W = PBW h μ u = ∬w_{1,B(u)}` the localised kernel mass,
* `F = psiWeight 1 μ` FS's weight, read at the state's own total in-box density
  `chiDensB v μ u Ψ = (∫Ψ²·nCountB)/(chiMass·‖Ψ‖²)`,
* `J = normB v μ k Ψ = ∫_{abox k (sideAt μ a)}Ψ²` the state's box mass,
* `Γ = (R/(ℓd))² + PBΓ v μ`, `χ_M = PBV v μ u = chiMass`.

All three slots carry the factor `J`, so the demand is homogeneous of degree `2` in `Ψ`; no
smoothness, symmetry, nonvanishing or normalisation is required to *state* it (only to use it). -/
noncomputable def totalDemand (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C μ : ℝ) (u : E3)
    {k : ℕ} (Ψ : Submission.BoseGases.X k → ℝ) : ℝ :=
  c₁ * (PBW h μ u * Work.SmallBoxSliding.psiWeight 1 μ (chiDensB (v := v) μ u Ψ))
      * Work.BoseBoxFix.normB v μ k Ψ
    - (1 / 2) * μ ^ 2 * PBW h μ u * Work.BoseBoxFix.normB v μ k Ψ
    - C * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (PBℓ v μ * PBd v μ)) ^ 2 + PBΓ v μ))
        * PBV v μ u * Work.BoseBoxFix.normB v μ k Ψ
    - C * μ * (_root_.BoseGases.a v) * Work.BoseBoxFix.normB v μ k Ψ

/-- **The demand inequality at a `BoxState` is `PerBoxFTotal`** — the two are the same formula in
different vocabulary (the sliding-parameter abbreviations `PBℓ, PBd, PBM, PBV, PBW, PBΓ` unfold to
the `sideAt`/`paramsAt` expressions of `PerBoxFTotal`). -/
theorem totalDemand_le_iff_PerBoxFTotal {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ}
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (u : E3) :
    PerBoxFTotal v h R c₁ C μ n Φ u
      ↔ totalDemand v h R c₁ C μ u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  unfold PerBoxFTotal totalDemand PBW PBV PBℓ PBd PBΓ PBKB PBM Work.FockBridge.dlGamma
  rfl

/-- **The slot word at the sliding parameters is the frozen word `sbWord`** (definitional). -/
theorem fibreWord_eq_sbWord {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {u : E3} {k : ℕ}
    (Ψ : Submission.BoseGases.X k → ℝ) :
    Work.SlotWord.fibreWord h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
        (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u Ψ
      = Work.BoseFixB1.sbWord h μ u Ψ := by
  unfold Work.SlotWord.fibreWord Work.BoseFixB1.sbWord Work.BoseFixB1.sbKin Work.BoseFixB1.sbPot
    PBM PBeT PBℓ PBd
  rfl

end Work.BoseFixB1B
