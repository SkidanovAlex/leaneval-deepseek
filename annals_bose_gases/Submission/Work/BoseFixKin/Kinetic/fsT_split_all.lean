import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.kinetic_localisation_of_thresholds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixKin.Kinetic.fsT_split_all` — the four words of `fsT` split off

FS `eq:DefT` defines the localised kinetic operator as the **sum of four one-body pieces**

`fsT ℓ d s εT b u ψ = neuWord ℓ d εT u ψ + gapWord ℓ b u ψ + momWord ℓ d εT b u ψ
                        + mainWord ℓ d s εT u ψ`

(`Work.BoseKinLoc.fsT_eq_sum`, definitionally).

The point of this file is that the *converse* of that reading is available: if the sum
`u ↦ fsT … u ψ` is (Bochner-)integrable, then so is **each of the four summands**, and the
integral splits accordingly:

`∫_u fsT = ∫_u neuWord + ∫_u gapWord + ∫_u momWord + ∫_u mainWord`.

(`Work.BoseKinLoc.Kinetic.kinetic_localisation_of_thresholds` uses every step of this argument
*locally* inside its own proof; the lemma below is the extracted statement, which the per-parameter
core `Work.BoseFixKin.Kinetic.kinetic_localisation_core` needs in order to speak about the four
terms of `∫_u fsT` separately.)

## The mathematics

All four words are **nonnegative** at the hypotheses of the statement
(`Work.BoseKinLoc.Word.fsT_nonneg`): `gapWord`, `momWord` and `mainWord` are products of a
nonnegative prefactor with an integral of squares, while `neuWord` is `½ε_T(dℓ)⁻²` times the
variational infimum `neuFrac`, which is `≥ 0` because the box trial functional completes to a
square (`Work.BoseKinLoc.Word.neuFrac_nonneg_of_integrableSq`).

Hence each summand is dominated pointwise by the (nonnegative) sum, and integrability passes down
by `Integrable.mono'`.  The only ingredient beyond the pointwise inequalities is **(a.e.) strong
measurability** of the summands, which is supplied by

* `Work.BoseKinLoc.Kinetic.gapWord_measurable` and `…momWord_measurable` (measurability in the
  box position is unconditional in `ψ` for `momForm`, and follows from the expansion of the box
  variance for `gapBare`);
* `Work.BSKinetic.Decomp.continuous_bsOneBody` for the two `bsOneBody` terms of `mainWord`;
* for `neuWord` — whose factor `neuFrac` is an `sInf` over trial functions, and therefore *not*
  obviously measurable — the trick of writing the summand as the **difference**
  `neuWord = fsT − (gapWord + momWord + mainWord)`, so measurability transfers from the
  (integrable, hence a.e. strongly measurable) sum.

The equality of integrals is then the iterated `integral_add`, using the pairwise integrability.
-/

namespace Work.BoseFixKin.Kinetic

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

set_option linter.unusedVariables false

/-- **The four words of `fsT` are jointly integrable and the `u`-integral splits.** -/
lemma fsT_split_all {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s)
    (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ)
    (hint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.fsT ℓ d s εT b u ψ)) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.neuWord ℓ d εT u ψ)
      ∧ MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.gapWord ℓ b u ψ)
      ∧ MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.momWord ℓ d εT b u ψ)
      ∧ MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.mainWord ℓ d s εT u ψ)
      ∧ ((∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.fsT ℓ d s εT b u ψ)
          = (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.neuWord ℓ d εT u ψ)
            + (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ)
            + (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momWord ℓ d εT b u ψ)
            + (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.mainWord ℓ d s εT u ψ)) := by
  have hdℓ : 0 < d * ℓ := mul_pos hd hℓ
  -- ## nonnegativity of the four words
  have hAn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseKinLoc.neuWord ℓ d εT u ψ := by
    intro u
    have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ u ψ) := hψ.continuous.sub continuous_const
    have hI : MeasureTheory.Integrable
        (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2)
        (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
      (ContinuousOn.integrableOn_compact (isCompact_closedBall (ℓ • u) (2 * (|ℓ| + 1)))
        (hcont.pow 2).continuousOn).mono_set
          (Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ u)
    have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg hdℓ.le _
    have hn := Work.BoseKinLoc.Word.neuFrac_nonneg_of_integrableSq (ℓ := ℓ)
      (a2 := (d * ℓ) ^ (-2 : ℤ)) ha2 u hI
    simp only [Work.BoseKinLoc.neuWord]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεT) ha2) hn
  have hGn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseKinLoc.gapWord ℓ b u ψ :=
    fun u => Work.BoseKinLoc.gapWord_nonneg hb hℓ.le u ψ
  have hMn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseKinLoc.momWord ℓ d εT b u ψ :=
    fun u => Work.BoseKinLoc.momWord_nonneg hb hεT hdℓ.le u ψ
  have hPn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseKinLoc.mainWord ℓ d s εT u ψ :=
    fun u => Work.BoseKinLoc.mainWord_nonneg hεT hεT1 u ψ
  have hRn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseKinLoc.gapWord ℓ b u ψ
      + Work.BoseKinLoc.momWord ℓ d εT b u ψ + Work.BoseKinLoc.mainWord ℓ d s εT u ψ :=
    fun u => by linarith [hGn u, hMn u, hPn u]
  have hRle : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ
      + Work.BoseKinLoc.momWord ℓ d εT b u ψ + Work.BoseKinLoc.mainWord ℓ d s εT u ψ
      ≤ Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
    intro u; rw [Work.BoseKinLoc.fsT_eq_sum]; linarith [hAn u]
  -- ## a.e. strong measurability of the three elementary words
  have hGm : AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapWord ℓ b u ψ) :=
    Work.BoseKinLoc.Kinetic.gapWord_measurable hℓ hψ hcs
  have hMm : AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.momWord ℓ d εT b u ψ) :=
    Work.BoseKinLoc.Kinetic.momWord_measurable hℓ hψ hcs
  have hPm : AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.mainWord ℓ d s εT u ψ) := by
    have hc1 : Continuous (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹))
          u ψ) := Work.BSKinetic.Decomp.continuous_bsOneBody hℓ _ ψ hψ hcs
    have hc2 : Continuous (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹))
          u ψ) := Work.BSKinetic.Decomp.continuous_bsOneBody hℓ _ ψ hψ hcs
    have hfun : (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.mainWord ℓ d s εT u ψ)
        = fun u : EuclideanSpace ℝ (Fin 3) => (1 - εT) * Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
            + εT * Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ := rfl
    rw [hfun]
    exact ((hc1.const_mul _).add (hc2.const_mul _)).aestronglyMeasurable
  have hRm : AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapWord ℓ b u ψ + Work.BoseKinLoc.momWord ℓ d εT b u ψ
        + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) := (hGm.add hMm).add hPm
  -- ## integrability of the three elementary words, from the integrability of the sum
  have hRint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapWord ℓ b u ψ
        + Work.BoseKinLoc.momWord ℓ d εT b u ψ
        + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) :=
    hint.mono' hRm (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (hRn u)]; exact hRle u))
  have hGint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapWord ℓ b u ψ) :=
    hRint.mono' hGm (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (hGn u)]; linarith [hMn u, hPn u]))
  have hMint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.momWord ℓ d εT b u ψ) :=
    hRint.mono' hMm (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (hMn u)]; linarith [hGn u, hPn u]))
  have hPint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.mainWord ℓ d s εT u ψ) :=
    hRint.mono' hPm (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (hPn u)]; linarith [hGn u, hMn u]))
  -- ## the Neumann word: measurability as a difference, then integrability
  have hAm : AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.neuWord ℓ d εT u ψ) := by
    have hfun : (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.neuWord ℓ d εT u ψ)
        = fun u => Work.BoseKinLoc.fsT ℓ d s εT b u ψ - (Work.BoseKinLoc.gapWord ℓ b u ψ
            + Work.BoseKinLoc.momWord ℓ d εT b u ψ
            + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) := by
      funext u; rw [Work.BoseKinLoc.fsT_eq_sum]; ring
    rw [hfun]
    exact hint.aestronglyMeasurable.sub hRm
  have hAint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.neuWord ℓ d εT u ψ) :=
    hint.mono' hAm (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (hAn u)]; rw [Work.BoseKinLoc.fsT_eq_sum]
      linarith [hGn u, hMn u, hPn u]))
  -- ## the split of the integral
  have hsplit : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.fsT ℓ d s εT b u ψ)
      = (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.neuWord ℓ d εT u ψ)
        + (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ)
        + (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momWord ℓ d εT b u ψ)
        + (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.mainWord ℓ d s εT u ψ) := by
    have hsplit1 : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.fsT ℓ d s εT b u ψ)
        = ∫ u : EuclideanSpace ℝ (Fin 3), (Work.BoseKinLoc.neuWord ℓ d εT u ψ
            + Work.BoseKinLoc.gapWord ℓ b u ψ + Work.BoseKinLoc.momWord ℓ d εT b u ψ
            + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) := rfl
    have h12 : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.neuWord ℓ d εT u ψ + Work.BoseKinLoc.gapWord ℓ b u ψ) :=
      (hAint.add hGint).congr (ae_of_all _ (fun u => rfl))
    have h123 : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseKinLoc.neuWord ℓ d εT u ψ + Work.BoseKinLoc.gapWord ℓ b u ψ)
          + Work.BoseKinLoc.momWord ℓ d εT b u ψ) :=
      (h12.add hMint).congr (ae_of_all _ (fun u => rfl))
    have h1234 : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ((Work.BoseKinLoc.neuWord ℓ d εT u ψ + Work.BoseKinLoc.gapWord ℓ b u ψ)
          + Work.BoseKinLoc.momWord ℓ d εT b u ψ)
          + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) :=
      (h123.add hPint).congr (ae_of_all _ (fun u => rfl))
    rw [hsplit1]
    rw [show (∫ u : EuclideanSpace ℝ (Fin 3), (Work.BoseKinLoc.neuWord ℓ d εT u ψ
            + Work.BoseKinLoc.gapWord ℓ b u ψ + Work.BoseKinLoc.momWord ℓ d εT b u ψ
            + Work.BoseKinLoc.mainWord ℓ d s εT u ψ))
        = ∫ u : EuclideanSpace ℝ (Fin 3), (((Work.BoseKinLoc.neuWord ℓ d εT u ψ
              + Work.BoseKinLoc.gapWord ℓ b u ψ) + Work.BoseKinLoc.momWord ℓ d εT b u ψ)
            + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) from by
      refine integral_congr_ae (ae_of_all _ (fun u => by ring))]
    rw [integral_add h123 hPint, integral_add h12 hMint, integral_add hAint hGint]
  exact ⟨hAint, hGint, hMint, hPint, hsplit⟩

end Work.BoseFixKin.Kinetic
