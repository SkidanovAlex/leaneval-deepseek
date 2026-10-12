import ChallengeDeps
import Submission.Work.BoseFixB1B.lowProviderResidual
import Submission.Work.BoseFixB1B.windowBridgeLow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.lowProviderFinal` — `lowCountBound` from the corrected residual

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

The frozen node `Work.BoseFixB1B.lowCountBound`'s conclusion, from the **corrected** residual:

* `FlatBranchLow v h R J` — the flat branch of FS `thm:smallbox` at the sliding box for **low**
  states of positive box norm, verbatim `Work.BoseFixB1B.flatBranchLowB`
  (`Submission/Work/BoseFixB1B/flatBranchLowB.lean`).  This is the project's single remaining
  analytic obligation of the per-box chapter; the thin and gap arms are PROVED, and the
  *unconditional* formulation was refuted three times
  (`Submission/Work/BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md`) — which is exactly why the
  corrected chain requires `IsLowB`;
* `OffGoodCrudeLow v h J C ε` — FS `eq:badset`, the crude per-box bound off the good set for low
  states (`Submission/Work/BoseFixB1B/lowProviderDefs.lean`).

Everything else in the chain is PROVED and axiom-clean:

    lowCountBound_of_residual
      = lowCountBound_of_windowBridge                  (arithmetic)
        ∘ windowBridgeLow                              (delegated, PROVED)
        ∘ aprioriHLambdaIneqLow_of_residual            (arithmetic + SlidingB, PROVED)
        ∘ collectedLow_of_providers                    (integration + mass law + eq:badset-trim)
        ∘ perBoxFLow_of_branches                       (thin + gap PROVED, flat = `hflat`)

The `#print axioms` of `lowCountBound_of_residual` is `[propext, Classical.choice, Quot.sound]`.
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

/-- **The frozen node `Work.BoseFixB1B.lowCountBound`, from the corrected residual.**  Identical
conclusion to the frozen statement (`(n : ℝ) ≤ C·μ·ℓ³` for a low box state), obtained from the
*true* per-box inputs: the flat branch (`FlatBranchLow`, the project's remaining obligation) and
the bad-set crude bound. -/
theorem lowCountBound_of_residual {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    (hJ : Work.UBB.lhyC ≤ J) (hflat : FlatBranchLow v h R J)
    (hband : ∃ εf Cbad : ℝ, 0 < εf ∧ 0 ≤ Cbad ∧ OffGoodCrudeLow v h J Cbad εf) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Adm v ε₀ μ →
        J ≤ (paramsAt μ (a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
          0 < normB v μ n (Φ : X n → ℝ) →
          IsLowB v h J μ n Φ →
            (n : ℝ) ≤ C * μ * (sideAt μ (a v)) ^ 3 :=
  lowCountBound_of_windowBridge h hv hv1 hvrad hR hv_supp hav hJ
    (windowBridgeLow h hv hv1 hvrad hR hv_supp hav hJ
      (aprioriHLambdaIneqLow_of_residual h hv hv1 hvrad hR hv_supp hav hJ hflat hband))

end Work.BoseFixB1B
