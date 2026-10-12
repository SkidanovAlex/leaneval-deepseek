import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxFrameAux
import Submission.Work.BoseFixB1.boxTauGen_mode_bound_meas
import Submission.Work.BoseFixB1B.pairMass_pos
import Submission.Work.BoseFixB1S.D1InputsB1
import Submission.Work.BoseFixB1S.boxPairIdSlidingB1
import Submission.Work.BoseFixB1S.chainIntegralQdep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.boxWinModeRGen_one`

The `n = 1` case of the `R`-half of `Work.BoseFixB1B.pairRung.winModeIntegrableBox`: for a
one-particle state the genuine windowed pairing content `boxWinModeRGen` **vanishes
identically in the momentum** `q`.

The reason is structural.  On `X 1 = Fin 1 → ℝ³` every configuration has a single particle at some
`z`, so `Function.update x 0 z = (fun _ => z)`; hence both amplitudes `boxTauAnnGen`/`boxTauDagGen`
are functions of `x 0` alone times a *fixed* number, and the product is

`boxTauAnnGen x * boxTauDagGen x = C · (Ac.indicator g) (x 0)`,

with `C = |A|⁻¹ · (∫_A g z ψ₁ z) · (∫_A ψ₁ z)`, `ψ₁ z = Ψ (fun _ => z)`.  Integrating over
`abox 1 a` and pulling the one-particle box back to `acube a`
(`integral_abox_one_of_apply_zero`) gives `C · ∫_A g`, and both windowed modes
`boxWinModeReGen`/`boxWinModeImGen` are mean-free on `Ac` (`winModeRe_mean_zero`,
`winModeIm_mean_zero`), so the content is `0`.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

set_option linter.unusedVariables false

namespace Work.BoseFixB1B.pairRung

/-- On `X 1 = Fin 1 → ℝ³` the updated configuration `Function.update x 0 z` is the constant
configuration with the single particle at `z`. -/
lemma update_fin_one_eq_const {x : Submission.BoseGases.X 1}
    {z : EuclideanSpace ℝ (Fin 3)} :
    Function.update x 0 z = (fun _ : Fin 1 => z) := by
  funext j
  rw [Function.update_apply]
  exact if_pos (Fin.eq_zero j)

/-- **Pullback of the one-particle box integral to the cube.**  For any `F`, the integral of
`F ∘ (x ↦ x 0)` over `abox 1 a` is the integral of `F` over `acube a`.

This is the measure-preserving identification of `X 1 = Fin 1 → ℝ³` (a one-fold product) with
`ℝ³` (`MeasureTheory.measurePreserving_funUnique`), composed with
`Submission.BoseGases.restrict_abox_eq_pi`. -/
lemma integral_abox_one_of_apply_zero (a : ℝ)
    (F : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ x in Submission.BoseGases.abox 1 a, F (x 0))
      = ∫ z in Submission.BoseGases.acube a, F z := by
  rw [Submission.BoseGases.restrict_abox_eq_pi 1 a]
  have hmp := MeasureTheory.measurePreserving_funUnique
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube a))
    (Fin 1)
  rw [← hmp.integral_comp (MeasurableEquiv.measurableEmbedding _) F]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp [MeasurableEquiv.funUnique_apply]

/-- **The one-particle pairing content is zero** for any mode `g` whose mean over `Ac` vanishes.

This is the structural core of `boxWinModeRGen_one`: at `N = 1` both `τ`-amplitudes collapse to a
function of `x 0` times a constant, so the pairing content is `C · ∫_Ac g = 0`. -/
lemma boxModeRGen_one_eq_zero
    {a volA : ℝ} {Ac : Set (EuclideanSpace ℝ (Fin 3))}
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} {Ψ : Submission.BoseGases.X 1 → ℝ}
    (hAcm : MeasurableSet Ac) (hvolpos : 0 < volA)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hgmean : ∫ z in Ac, g z = 0) :
    Work.BoseFixB1.boxModeRGen a volA Ac g Ψ = 0 := by
  set α : ℝ := ∫ z in Ac, g z * Ψ (fun _ : Fin 1 => z) with hα
  set β : ℝ := ∫ z in Ac, Ψ (fun _ : Fin 1 => z) with hβ
  set C : ℝ := volA⁻¹ * α * β with hC
  have hsq : (Real.sqrt volA)⁻¹ * (Real.sqrt volA)⁻¹ = volA⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hvolpos.le]
  have hAnn : ∀ x : Submission.BoseGases.X 1,
      Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x
        = (Real.sqrt volA)⁻¹ * Ac.indicator (fun _ => (1 : ℝ)) (x 0) * α := by
    intro x
    rw [Work.BoseFixB1.boxTauAnnGen, Fin.sum_univ_one]
    have h : (fun z => g z * Ψ (Function.update x 0 z))
        = (fun z => g z * Ψ (fun _ : Fin 1 => z)) := by
      funext z; rw [update_fin_one_eq_const]
    rw [h, ← hα]; ring
  have hDag : ∀ x : Submission.BoseGases.X 1,
      Work.BoseFixB1.boxTauDagGen volA Ac g Ψ x
        = (Real.sqrt volA)⁻¹ * Ac.indicator (fun _ => (1 : ℝ)) (x 0) * g (x 0) * β := by
    intro x
    rw [Work.BoseFixB1.boxTauDagGen, Fin.sum_univ_one]
    have h : (fun z => Ψ (Function.update x 0 z))
        = (fun z => Ψ (fun _ : Fin 1 => z)) := by
      funext z; rw [update_fin_one_eq_const]
    rw [h, ← hβ]; ring
  have hprod : ∀ x : Submission.BoseGases.X 1,
      Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x * Work.BoseFixB1.boxTauDagGen volA Ac g Ψ x
        = C * (Ac.indicator g (x 0)) := by
    intro x
    rw [hAnn x, hDag x]
    have hind : Ac.indicator (fun _ => (1 : ℝ)) (x 0) * Ac.indicator (fun _ => (1 : ℝ)) (x 0)
        = Ac.indicator (fun _ => (1 : ℝ)) (x 0) := by
      by_cases hx : x 0 ∈ Ac
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    have hgi : Ac.indicator g (x 0)
        = Ac.indicator (fun _ => (1 : ℝ)) (x 0) * g (x 0) := by
      by_cases hx : x 0 ∈ Ac
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hgi, hC]
    calc ((Real.sqrt volA)⁻¹ * Ac.indicator (fun _ => (1 : ℝ)) (x 0) * α)
            * ((Real.sqrt volA)⁻¹ * Ac.indicator (fun _ => (1 : ℝ)) (x 0) * g (x 0) * β)
        = ((Real.sqrt volA)⁻¹ * (Real.sqrt volA)⁻¹)
            * (Ac.indicator (fun _ => (1 : ℝ)) (x 0)
                * Ac.indicator (fun _ => (1 : ℝ)) (x 0))
            * (α * g (x 0) * β) := by ring
      _ = volA⁻¹ * Ac.indicator (fun _ => (1 : ℝ)) (x 0) * (α * g (x 0) * β) := by
            rw [hsq, hind]
      _ = (volA⁻¹ * α * β) * (Ac.indicator (fun _ => (1 : ℝ)) (x 0) * g (x 0)) := by ring
  have hrepr : Work.BoseFixB1.boxModeRGen a volA Ac g Ψ
      = ∫ x in Submission.BoseGases.abox 1 a, C * (Ac.indicator g (x 0)) := by
    rw [Work.BoseFixB1.boxModeRGen]
    exact setIntegral_congr_fun (Submission.BoseGases.abox_measurable 1 a) (fun x _ => hprod x)
  rw [hrepr, MeasureTheory.integral_const_mul]
  have h1 : (∫ x in Submission.BoseGases.abox 1 a, Ac.indicator g (x 0))
      = ∫ z in Submission.BoseGases.acube a, Ac.indicator g z :=
    integral_abox_one_of_apply_zero a _
  rw [h1, MeasureTheory.setIntegral_indicator hAcm, Set.inter_eq_right.mpr hAcsub, hgmean,
    mul_zero]

theorem boxWinModeRGen_one {a volA : ℝ} {Ac : Set (EuclideanSpace ℝ (Fin 3))}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} {Ψ : Submission.BoseGases.X 1 → ℝ}
    (ha : 0 < a) (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    (hΨc : Continuous Ψ) :
    Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ = 0 := by
  funext q
  rw [Work.BoseFixB1.boxWinModeRGen]
  rw [boxModeRGen_one_eq_zero hAcm hvolpos hAcsub
        (Work.BoseFixB1.winModeRe_mean_zero (n := 1) ha hAcm hAcsub hvol hvolpos hχc q),
      boxModeRGen_one_eq_zero hAcm hvolpos hAcsub
        (Work.BoseFixB1.winModeIm_mean_zero (n := 1) ha hAcm hAcsub hvol hvolpos hχc q)]
  simp

end Work.BoseFixB1B.pairRung
