import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.pairMass_pos
import Submission.Work.BoseFixB1B.pairRung.integrableFsKinTBampN
import Submission.Work.BoseFixB1B.pairRung.winModeContentLeWord
import Submission.Work.BoseFixB1B.pairRung.winModePGenLeSlotSumN
import Submission.Work.BoseFixB1S.D1InputsB1
import Submission.Work.BoseFixB1S.boxPairIdSlidingB1
import Submission.Work.BoseFixB1S.chainIntegralQdep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.fsKinPGenIntegrable`

`q`-integrability of the FS-weighted genuine windowed mode content

    q ↦ fsKinCoeff c ‖q‖ · boxWinModePGen a volA Ac χ Ψ q .

This is the hypothesis under which the `q`-integral of the pairing rung may be manipulated
(dominated convergence, `Fubini`, `integral_mono`, …).  The symbol `fsKinCoeff c ‖q‖ = [‖q‖−c]₊²`
*grows* like `‖q‖²`, so the content of the statement is that `boxWinModePGen` decays fast enough in
`q`.

## Route

1. **Slot Cauchy–Schwarz** (`Work.BoseFixB1B.pairRung.winModePGenLeSlotSumN`): for every `q`,
   `boxWinModePGen a volA Ac χ Ψ q ≤ n · Σ_i (a³)⁻¹ ∫_{abox n a} ‖tBamp χ q (Q_{Ac,i}Ψ) i x‖²`.
2. **Integrability of each slot term** (`Work.BoseFixB1B.pairRung.integrableFsKinTBampN`): the
   window `χ` vanishes off `Ac`, so the projected fibre is a difference of two windowed Fourier
   transforms of *smooth compactly supported* functions; the uniform `(1+‖q‖)⁻³` decay
   (`tBamp_decay`) makes each slot integrand `≲ fsKinCoeff c ‖q‖ · (1+‖q‖)⁻⁶ ≲ (1+‖q‖)⁻⁴`, which is
   integrable in dimension three.
3. **Assembly**: the dominating function is a finite sum of integrable functions, hence integrable;
   `fsKinCoeff` and `boxWinModePGen` are nonnegative, so `Integrable.mono'` transfers integrability
   to the target integrand off the (empty) exceptional set.  Measurability comes from
   `aeStronglyMeasurable_boxWinModePGen` (with `Ac` measurable, `χ`, `Ψ` continuous) and the
   continuity of `q ↦ fsKinCoeff c ‖q‖`.

Note that the statement needs neither `hc` (only `c` enters through the symbol) nor the smoothness
of `Ψ` beyond continuity on the box; they are kept because the requester's interface demands them.
-/

namespace Work.BoseFixB1B.pairRung

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

set_option linter.unusedVariables false

noncomputable section

theorem fsKinPGenIntegrable {n : ℕ} {a volA c : ℝ}
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Ψ : Submission.BoseGases.X n → ℝ}
    (ha : 0 < a) (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z)
    (hc : 0 < c) {hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ} :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖q‖ *
        Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q) := by
  classical
  -- ### the slot integrands are integrable
  have hIntAp : ∀ i : Fin n, MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) :=
    fun i => integrableFsKinTBampN (n := n) (a := a) (volA := volA) (c₀ := c)
      ha hvolpos hAcm hAcsub hvol hχc hχs hχsupp hΨc i
  -- ### the dominating function: the slot sum
  have hIntSum : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ∑ i : Fin n, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) :=
    integrable_finsetSum _ (fun i _ => hIntAp i)
  have hIntT : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ∑ i : Fin n, (a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) :=
    hIntSum.congr (Filter.Eventually.of_forall fun p =>
      (Finset.mul_sum Finset.univ
        (fun i : Fin n => (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
        (Submission.BoseGases.fsKinCoeff c ‖p‖)).symm)
  have hIntRight : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ((n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) := by
    refine (hIntT.const_mul (n : ℝ)).congr (Filter.Eventually.of_forall fun p => ?_)
    show (n : ℝ) * (Submission.BoseGases.fsKinCoeff c ‖p‖ * ∑ i : Fin n, (a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
      = Submission.BoseGases.fsKinCoeff c ‖p‖ * ((n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
    ring
  -- ### the pointwise (in `q`) slot bound
  have hpt : ∀ p : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ p
      ≤ (n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 :=
    fun p => winModePGenLeSlotSumN (n := n) (a := a) (volA := volA) ha hvolpos hAcm hAcsub
      hvol hχc hχs hχsupp hχnn hΨc p
  -- ### measurability of the target integrand
  have haesm : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ *
        Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ p)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
    have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      simp only [Submission.BoseGases.fsKinCoeff]
      fun_prop
    exact hcont.aestronglyMeasurable.mul
      (aeStronglyMeasurable_boxWinModePGen hAcm hχc.continuous hΨc.continuous)
  -- ### domination and conclusion
  refine MeasureTheory.Integrable.mono' hIntRight haesm ?_
  filter_upwards with p
  have hPnn : 0 ≤ Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ p := by
    simp only [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxModePGen]
    exact add_nonneg (integral_nonneg fun x => sq_nonneg _)
      (integral_nonneg fun x => sq_nonneg _)
  rw [Real.norm_of_nonneg
    (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) hPnn)]
  exact mul_le_mul_of_nonneg_left (hpt p) (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)

end

end Work.BoseFixB1B.pairRung
