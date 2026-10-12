import ChallengeDeps
import Submission.Work.BoseFixB1.Core.MM.integrable_bsW_chiB
import Submission.Work.BoseFixB1.Core.MM.meanSq_le
import Submission.Work.BoseFixB1.Core.MM.mmArith
import Submission.Work.BoseFixB1.Core.MM.pieces
import Submission.Work.BoseFixB1S.corrChiScaleL2
import Submission.Work.BoseFixB1S.corrCutWordsSharp
import Submission.Work.BoseFixB1S.corrMarg.integrable_and_marginal_chiB
import Submission.Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean
import Submission.Work.BoseFixB1S.corrPlanchMarg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Core

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.BoseBoxFix Work.UBB Work.SmallBoxSliding

/-!
# `Work.BoseFixB1.Core.meanMismatch_le` — proof structure

The statement is the mean-mismatch step of the sliding crux.  The **assembly** (the pointwise
mean-shift step `MM.crux_pt`, the `u`-integration, the `u`-Cauchy–Schwarz, Plancherel + the
window partition and the parameter arithmetic) is in
`Submission/Work/BoseFixB1/Core/MM/pieces.lean` (`MM.mm_of_pieces`), conditional on six interface
propositions.  Here those six are discharged:

* `MM.CutWords`   ← `Work.BoseFixB1S.corrCutWordsSharp` (proved, axiom-clean);
* `MM.MeanSq`     ← `Work.BoseFixB1.Core.MM.meanSq_le` (the `u`-integral of the squared sliding
                    box mean, plus its integrability);
* `MM.Marginal`   ← `Work.BoseFixB1.Core.MM.integrable_bsW_chiB` (the two `bsW` `u`-marginals)
                    together with `Work.BoseFixB1S.integrable_and_marginal_chiB` (the window
                    partition identity);
* `MM.ChiL2`      ← `Work.BoseFixB1S.corrChiScaleL2`;
* `MM.PlanchMarg` ← `Work.BoseFixB1S.corrPlanchMarg`;
* `MM.Arith`      ← `Work.BoseFixB1.Core.MM.mmArith`.
-/

/-! ## Discharging the interface propositions -/

/-- `MM.MeanSq` at `v` from the generic sliding-box mean-square bound `MM.meanSq_le`.
The admissibility threshold is `1`: it makes `(paramsAt μ (a v)).d ≤ 1`, which is the shape of
`meanSq_le`. -/
theorem mmMeanSq (v : E3 → ℝ) : MM.MeanSq v := by
  obtain ⟨C, hC, hmean⟩ := MM.meanSq_le
  refine ⟨1, one_pos, C, hC, ?_⟩
  intro μ hμ w hw
  have hμ0 : 0 < μ := hμ.1
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hμ
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hμ
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := hμ.2.1
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ0 (pow_pos ha 3)
  have hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
    rw [Work.BoseFixB1.paramsAt_eq_fsParams]
    exact Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num)
  exact hmean (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d hℓ hd hd1 w hw

/-- `MM.Marginal` at `v` from the generic `bsW` marginal integrability
(`MM.integrable_bsW_chiB`) and the window partition identity
(`Work.BoseFixB1S.integrable_and_marginal_chiB`). -/
theorem mmMarginal (v : E3 → ℝ) : MM.Marginal v := by
  refine ⟨1, one_pos, ?_⟩
  intro μ hμ w hw
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hμ
  have hwc : Continuous w := hw.continuous
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0 := MM.integrable_bsW_chiB (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hℓ hd hw
      (ρ := fun _ : E3 => (0 : ℝ)) measurable_const ⟨0, fun u => by simp⟩
    simpa using h0
  · obtain ⟨hρm, hρb⟩ := Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ hd hwc
    obtain ⟨Cb, hCb0, hCb⟩ := hρb
    have hρmeas : Measurable (fun u : E3 =>
        (1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
          ∫ z' in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z') := by
      simpa only [one_div] using hρm
    have hρbd : ∃ C : ℝ, ∀ u : E3,
        |(1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
          ∫ z' in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z'| ≤ C := by
      refine ⟨Cb, fun u => ?_⟩
      simpa only [one_div] using hCb u
    have h1 := MM.integrable_bsW_chiB (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hℓ hd hw hρmeas hρbd
    simpa only [one_div] using h1
  · exact (Work.BoseFixB1S.integrable_and_marginal_chiB hℓ hd hwc).1
  · exact (Work.BoseFixB1S.integrable_and_marginal_chiB hℓ hd hwc).2

/-- `MM.Arith` at `v` from the parameter arithmetic `MM.mmArith`. -/
theorem mmArithProp (v : E3 → ℝ) : MM.Arith v := by
  intro hav C₀ C₁ Cχ h₀ h₁ hχ
  exact MM.mmArith (v := v) hav (Cq := C₀) (Ce := Cχ) (Cm := C₁) h₀ hχ h₁

theorem meanMismatch_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) ψ →
        (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (sbCut μ (_root_.BoseGases.a v)))
            (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiB
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
              (ψ z - (1 / Work.SmallBoxSliding.boxMass
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                ∫ z' in Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, ψ z')))
          ≤ (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.Decomp.bsW
                (Submission.BoseGases.fsKinCoeff (sbCut μ (_root_.BoseGases.a v)))
                (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiB
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
                  (ψ z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                    ∫ z' in Submission.BoseGases.acube
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), ψ z')))
            + ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b /
                (8 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) *
              (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (ψ z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                  ∫ z' in Submission.BoseGases.acube
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), ψ z') ^ 2)  := by
  exact MM.mm_of_pieces (v := v) h (Work.BoseFixB1S.corrCutWordsSharp h) (mmMeanSq v)
    (mmMarginal v) (mmArithProp v)
    (fun ℓ hℓ w hw => Work.BoseFixB1S.corrChiScaleL2 (ℓ := ℓ) hℓ hw)
    (fun ℓ d hℓ hd w hw hint heq =>
      Work.BoseFixB1S.corrPlanchMarg (ℓ := ℓ) (d := d) hℓ hd hw hint heq)

end Work.BoseFixB1.Core
