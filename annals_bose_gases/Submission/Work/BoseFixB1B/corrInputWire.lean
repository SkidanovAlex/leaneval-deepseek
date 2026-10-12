import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.MargPiece.integrable_bsW_chiB_sub_holds
import Submission.Work.BoseFixB1B.MeanSqPiece.meanSqReal
import Submission.Work.BoseFixB1B.corrInputPieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.corrInputWire` — the last two pieces of `CorrInput`, wired

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

`Work.BoseFixB1B.corrInput_of_pieces` (in `kineticHalfAssembly.lean`) reduces the intersection-mean
correction `Work.BoseFixB1S.CorrInput v` to its two remaining pieces `MeanSq v` and `Marginal v`
(the other four are theorems).  This file wires those two pieces from their *concrete analytic
content*, so that no further bookkeeping is left:

* `MeanSq v` from the ℝ-valued sliding-box mean-square bound
  `corrMeanSqRealE3`-shaped input (the content of `Work.BoseFixB1S.corrMeanSq`);
* `Marginal v` from the `u`-integrability of the windowed cut word
  (`Work.BoseFixB1S.corrMarg.integrable_bsW_chiB_sub`-shaped input), the other two conjuncts
  being the proved `Work.BoseFixB1S.integrable_and_marginal_chiB`.

Both wrappers are `sorry`-free; the hypotheses are exactly the two statements delegated this
session to `Submission/Work/BoseFixB1B/MeanSqPiece/corrMeanSqRealE3_holds.lean` and
`Submission/Work/BoseFixB1B/MargPiece/integrable_bsW_chiB_sub_holds.lean`, so they can be
instantiated by `exact` the moment those land.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. `MeanSq` from the real sliding-box mean-square bound -/

/-- **`Work.BoseFixB1S.MeanSq v` from the real-valued sliding-box mean-square bound.**
This is the assembly of `Work.BoseFixB1S.corrMeanSq` (constant `9³`, threshold `1`) with its
single analytic input `corrMeanSqRealE3` supplied as a hypothesis. -/
theorem meanSq_of_realE3 {v : E3 → ℝ}
    (hreal : ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d → d ≤ 1 → ∀ w : E3 → ℝ, Continuous w →
      MeasureTheory.Integrable (fun u : E3 =>
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
        ∧ (∫ u : E3,
            ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
          ≤ (9 / (ℓ * d)) ^ 3 * (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2)) :
    Work.BoseFixB1S.MeanSq v := by
  classical
  refine ⟨1, one_pos, (9 : ℝ) ^ 3, by positivity, ?_⟩
  intro μ hAdm w hw
  have hμ : 0 < μ := hAdm.1
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hε : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    Work.BoseFixB1.adm_dilute_le_one hAdm le_rfl
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos ha 3)
  have hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
    rw [Work.BoseFixB1.paramsAt_eq_fsParams]
    exact Work.BoseBox.fsXp_le_one ht0 hε (by norm_num)
  obtain ⟨hint, hbd⟩ := hreal _ _ hℓ hd hd1 w hw.continuous
  refine ⟨hint, ?_⟩
  set L : ℝ := 1 + (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
      + |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)| with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h1 : 0 ≤ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹ :=
      inv_nonneg.mpr (by positivity)
    have h2 : 0 ≤ |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)| := abs_nonneg _
    linarith
  have hL3 : (1 : ℝ) ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL1 3
    simpa using this
  have hkey : (9 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 3
      ≤ (9 : ℝ) ^ 3 * L ^ 3
        * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹) := by
    rw [div_pow, div_eq_mul_inv]
    calc (9 : ℝ) ^ 3 * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
        = (9 : ℝ) ^ 3 * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹ * 1 := by ring
      _ ≤ (9 : ℝ) ^ 3 * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹ * L ^ 3 :=
          mul_le_mul_of_nonneg_left hL3 (by positivity)
      _ = (9 : ℝ) ^ 3 * L ^ 3 * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹ := by ring
  have hI : 0 ≤ ∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (w z) ^ 2 := integral_nonneg fun z => sq_nonneg _
  calc (∫ u : E3,
        ((1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
          ∫ z in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z) ^ 2)
      ≤ (9 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 3
          * (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (w z) ^ 2) := hbd
    _ ≤ ((9 : ℝ) ^ 3 * L ^ 3
          * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹))
          * (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (w z) ^ 2) := mul_le_mul_of_nonneg_right hkey hI
    _ = (9 : ℝ) ^ 3 * (1 + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
                    + |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)|) ^ 3
                * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
                * (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                    (w z) ^ 2) := by
          rw [hL]

/-! ## 2. `Marginal` from the `bsW`-integrability of the cut word -/

/-- **`Work.BoseFixB1S.Marginal v` from the `u`-integrability of the windowed cut word.**
The last two conjuncts are the proved
`Work.BoseFixB1S.integrable_and_marginal_chiB`; the first two are the supplied hypothesis at
`ρ = 0` and at `ρ =` the sliding-box mean, whose measurability and boundedness is the second
supplied hypothesis (the statement
`Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean`). -/
theorem marginal_of_bsW_integrable {v : E3 → ℝ}
    (hbsW : ∀ (ℓ d c : ℝ), 0 < ℓ → 0 < d → ∀ (g : E3 → ℝ), ContDiff ℝ (⊤ : ENat) g →
      ∀ (ρ : E3 → ℝ), Measurable ρ → (∃ C : ℝ, ∀ u : E3, |ρ u| ≤ C) →
      MeasureTheory.Integrable (fun u : E3 =>
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u))))
    (hbm : ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d → ∀ w : E3 → ℝ, Continuous w →
      Measurable (fun u : E3 =>
        (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ z in Submission.BoseGases.dlBox ℓ d u, w z)
      ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E3,
          |(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ z in Submission.BoseGases.dlBox ℓ d u, w z| ≤ C) :
    Work.BoseFixB1S.Marginal v := by
  classical
  refine ⟨1, one_pos, ?_⟩
  intro μ hAdm w hw
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hρm, C, hC0, hρbd⟩ :=
    hbm _ _ hℓ hd w hw.continuous
  have hρbd' : ∃ C : ℝ, ∀ u : E3,
      |(1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
        ∫ z in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z| ≤ C :=
    ⟨C, hρbd⟩
  obtain ⟨hint3, heq3⟩ :=
    Work.BoseFixB1S.integrable_and_marginal_chiB hℓ hd hw.continuous
  have h1 : MeasureTheory.Integrable (fun u : E3 =>
      Work.BSKinetic.Decomp.bsW
        (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
        (fun z : E3 => Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z * w z)) := by
    have hh := hbsW _ _ (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hℓ hd w hw 0 measurable_const ⟨0, fun u => by simp⟩
    simpa using hh
  have h2 : MeasureTheory.Integrable (fun u : E3 =>
      Work.BSKinetic.Decomp.bsW
        (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
        (fun z : E3 => Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
          (w z - (1 / Work.SmallBoxSliding.boxMass
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
            (∫ z' in Submission.BoseGases.dlBox
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z')))) := by
    have hh := hbsW _ _ (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hℓ hd w hw
      (fun u : E3 => (1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
        ∫ z in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z)
      hρm hρbd'
    simpa using hh
  exact ⟨h1, h2, hint3, heq3⟩

/-! ## 3. The two-piece form of `CorrInput` and of `SlidingB` -/

/-- **`CorrInput v`** from the two concrete analytic statements: the real sliding-box
mean-square bound and the `bsW`-integrability of the cut word. -/
theorem corrInput_of_realE3_bsW {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hreal : ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d → d ≤ 1 → ∀ w : E3 → ℝ, Continuous w →
      MeasureTheory.Integrable (fun u : E3 =>
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
        ∧ (∫ u : E3,
            ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              ∫ x in Submission.BoseGases.dlBox ℓ d u, w x) ^ 2)
          ≤ (9 / (ℓ * d)) ^ 3 * (∫ x in Submission.BoseGases.acube ℓ, (w x) ^ 2))
    (hbsW : ∀ (ℓ d c : ℝ), 0 < ℓ → 0 < d → ∀ (g : E3 → ℝ), ContDiff ℝ (⊤ : ENat) g →
      ∀ (ρ : E3 → ℝ), Measurable ρ → (∃ C : ℝ, ∀ u : E3, |ρ u| ≤ C) →
      MeasureTheory.Integrable (fun u : E3 =>
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u))))
    (hbm : ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d → ∀ w : E3 → ℝ, Continuous w →
      Measurable (fun u : E3 =>
        (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ z in Submission.BoseGases.dlBox ℓ d u, w z)
      ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E3,
          |(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ z in Submission.BoseGases.dlBox ℓ d u, w z| ≤ C) :
    Work.BoseFixB1S.CorrInput v :=
  corrInput_of_pieces h (meanSq_of_realE3 hreal) (marginal_of_bsW_integrable hbsW hbm)

/-! ## 4. `Marginal` is a theorem (the `bsW`-integrability piece has landed) -/

/-- **`Work.BoseFixB1S.Marginal v` is PROVED**: its first two conjuncts are the delegated
`Work.BoseFixB1B.MargPiece.integrable_bsW_chiB_sub_holds` (at `ρ = 0` and at the sliding-box
mean), and its last two are the proved
`Work.BoseFixB1S.integrable_and_marginal_chiB`; the box-mean measurability and boundedness is
`Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean`. -/
theorem marginal_holds {v : E3 → ℝ} (h : Work.UBB.ScatSol v) : Work.BoseFixB1S.Marginal v :=
  marginal_of_bsW_integrable
    (fun ℓ d c hℓ hd g hg ρ hρ hρbd =>
      Work.BoseFixB1B.MargPiece.integrable_bsW_chiB_sub_holds hℓ hd hg hρ hρbd)
    (fun ℓ d hℓ hd w hw => by
      obtain ⟨h1, h2⟩ := Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean hℓ hd hw
      refine ⟨?_, ?_⟩
      · simpa only [one_div] using h1
      · obtain ⟨C, hC0, hC⟩ := h2
        exact ⟨C, hC0, fun u => by simpa only [one_div] using hC u⟩)

/-! ## 5. `MeanSq` and `CorrInput` are theorems -/

/-- **`Work.BoseFixB1S.MeanSq v` is PROVED**, from the real sliding-box mean-square bound
`Work.BoseFixB1B.MeanSqPiece.Real.corrMeanSqReal_of_E3` (which rests on the 1-D core
`Work.BoseFixB1B.MeanSqPiece.meanSq1d_holds` and the 3-D peel
`Work.BoseFixB1B.MeanSqPiece.meanSq3d_holds`). -/
theorem meanSq_holds {v : E3 → ℝ} (h : Work.UBB.ScatSol v) : Work.BoseFixB1S.MeanSq v :=
  meanSq_of_realE3
    (fun ℓ d hℓ hd hd1 w hw => Work.BoseFixB1B.MeanSqPiece.Real.corrMeanSqReal_of_E3 hℓ hd hd1 hw)

/-- **The intersection-mean correction `Work.BoseFixB1S.CorrInput v` is PROVED**: its
`CutWords`, `ChiL2`, `PlanchMarg` and `Arith` pieces are theorems, and its last two pieces
`MeanSq` and `Marginal` are `meanSq_holds` and `marginal_holds`. -/
theorem corrInput_holds {v : E3 → ℝ} (h : Work.UBB.ScatSol v) : Work.BoseFixB1S.CorrInput v :=
  corrInput_of_pieces h (meanSq_holds h) (marginal_holds h)

end Work.BoseFixB1B
