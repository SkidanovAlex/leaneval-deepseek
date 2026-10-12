import ChallengeDeps
import Submission.Work.BoseFixB1B.PerBoxSmoothHolds
import Submission.Work.BoseFixB1B.lowProviderChain
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.lowProviderResidual` — the residual of `lowCountBound`

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

This module reduces FS `eq:aprioriRn+` (in the restricted form `AprioriHLambdaIneqLow` of
`Submission/Work/BoseFixB1B/lowProviderDefs.lean`) to the two *true* per-box inputs

* `FlatBranchLow v h R J` — FS `thm:smallbox` at the sliding box in the FLAT branch for **low**
  states: verbatim the statement of `Work.BoseFixB1B.flatBranchLowB`
  (`Submission/Work/BoseFixB1B/flatBranchLowB.lean`, itself the single remaining obligation of the
  corpus's per-box chapter after the refutation of the *unconditional* `PerBoxF` —
  `Submission/Work/BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md`); the thin and gap arms are
  PROVED (`Work.BoseFixB1.perBoxF_thin_holds`, `Work.BoseFixB1B.gapAtAll`), and their assembly is
  the PROVED `Work.BoseFixB1B.perBoxF_of_branches`;
* `OffGoodCrudeLow v h J C ε` — FS `eq:badset` off the good set, for low states.

The chain is `perBoxFLow_of_branches` (this file) → `collectedLow_of_providers` →
`aprioriHLambdaIneqLow_of_collected` (all in `Submission/Work/BoseFixB1B/lowProviderChain.lean`),
together with the PROVED sliding localisation `slidingB_holds_from_assembly`.

**The node `Work.BoseFixB1B.lowCountBound` is one further step away** (the particle window
`Work.BoseFixB1.WindowBridge v h J` from `AprioriHLambdaIneqLow`): that step is delegated as
`Work.BoseFixB1B.windowBridgeLow` (`Submission/Work/BoseFixB1B/windowBridgeLow.lean`), and the
composition lives in `Submission/Work/BoseFixB1B/lowProviderFinal.lean`.

Everything here is `sorry`-free and rests only on `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The flat branch of FS `thm:smallbox` for low states** — verbatim the statement of
`Work.BoseFixB1B.flatBranchLowB` (`Submission/Work/BoseFixB1B/flatBranchLowB.lean`), the single
remaining analytic obligation of the per-box chapter. -/
def FlatBranchLow (v : E3 → ℝ) (h : ScatSol v) (R J : ℝ) : Prop :=
  ∃ γ₀ ε₀ C : ℝ, 0 < γ₀ ∧ 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → 0 < μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        0 < normB v μ n (Φ : X n → ℝ) →
        IsLowB v h J μ n Φ →
        ∀ u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
        ¬ IsThinBox v h μ u →
        UBBInputs8.cnPlusBoxInd (sideAt μ (a v))
            (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) (Φ : X n → ℝ)
          < γ₀ * (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
        PerBoxF v h R (1 / 4) C μ n Φ u

/-- **The good-set provider from the thin, gap and flat arms.**  The `hgap` slot is discharged by
the PROVED `Work.BoseFixB1B.gapAtAll`; the `hflat` slot is `FlatBranchLow`. -/
theorem perBoxFLow_of_branches {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    (hJ : Work.UBB.lhyC ≤ J) (hflat : FlatBranchLow v h R J) :
    ∃ εw c₁ C : ℝ, 0 < εw ∧ 0 < c₁ ∧ 0 ≤ C ∧ PerBoxFLow v h R J c₁ C εw := by
  obtain ⟨ε, c, C, hε, hc, hC, hbody⟩ :=
    Work.BoseFixB1B.perBoxF_of_branches (v := v) (h := h) (R := R)
      hv hvrad hR hv_supp hav hJ hflat
      (Work.BoseFixB1B.gapAtAll v h hv hv1 hvrad hR hv_supp hav)
  exact ⟨ε, c, C, hε, hc, hC,
    fun μ hAdm hJK n Φ hN hlow u hu => hbody μ hAdm hAdm.1 n Φ hN hlow u hu⟩

/-- **FS `eq:aprioriRn+` (restricted class), modulo the flat branch and the band bound.** -/
theorem aprioriHLambdaIneqLow_of_residual {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    (hJ : Work.UBB.lhyC ≤ J) (hflat : FlatBranchLow v h R J)
    (hband : ∃ εf Cbad : ℝ, 0 < εf ∧ 0 ≤ Cbad ∧ OffGoodCrudeLow v h J Cbad εf) :
    AprioriHLambdaIneqLow v h J :=
  aprioriHLambdaIneqLow_of_collected h hv1 hvrad hR hv_supp hav hJ
    (collectedLow_of_providers h hv hv1 hvrad hR hv_supp hav
      (perBoxFLow_of_branches h hv hv1 hvrad hR hv_supp hav hJ hflat) hband)

end Work.BoseFixB1B
