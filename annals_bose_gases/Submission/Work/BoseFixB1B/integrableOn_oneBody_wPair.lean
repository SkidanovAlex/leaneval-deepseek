import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.potGapAdditivityStratum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseFixB1B

/-- PROOF ROUTE (for the prover): the import cone `Submission.KernelFibreBound` supplies
`chiSup`, `chiR0`, `wPair`, `X`, `abox`, `Submission.BoseGases.fibre_integral_abs_le` (the uniform
bound `|∫ y, wPair ℓ hh u y| ≤ chiSup²·2·∫|hh|` for every `u`), `abox_compact`, and
`ContinuousOn.integrableOn_compact`.  The only missing ingredient is the a.e. measurability of
`u ↦ ∫ y, wPair ℓ hh u y`: reduce `wScaled ℓ hh` to a measurable representative
(`AEMeasurable.mk`; `wScaled ℓ hh =ᵐ` a product of the `L¹` function `hh` with the continuous
function `(convScale ℓ ·)⁻¹`) and then apply `StronglyMeasurable.integral_prod_right` to the
jointly measurable integrand (or the `lintegral` route `AEMeasurable.lintegral_prod_right`); the
product-measure a.e. congruence uses `MeasurePreserving` of `y ↦ u - y`
(`Submission.BoseGases.km_measurePreserving_sub_left`) plus `Measurable.comp_aemeasurable`.
The corpus already has closely related a.e.-measurability lemmas (`aesm_wPairU_prod`,
`fibre_acube_aem`, `Submission.BoseGases.ae_comp_sub_left`) that should be reusable.
Then conclude by `Integrable.mono'` with the integrable majorant
`fun x => (Φ x)^2 * ((n : ℝ) * (chiSup^2 * 2 * ∫|hh|))` (continuous on the compact box). -/
theorem integrableOn_oneBody_wPair {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {hh : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hi : MeasureTheory.Integrable hh)
    (hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → hh z = 0)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wPair ℓ hh (x i) y))
      (Submission.BoseGases.abox n ℓ) := by
  have hwi : MeasureTheory.Integrable (Submission.BoseGases.wScaled ℓ hh) :=
    Submission.BoseGases.wScaled_integrable_ae hℓ hR hRℓ hi hsupp
  set C : ℝ := Submission.BoseGases.chiSup ^ 2 * 2 *
    (∫ z : EuclideanSpace ℝ (Fin 3), |hh z|) with hCdef
  -- a.e. strong measurability of the fibre integrals
  have hfib : ∀ i : Fin n, AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wPair ℓ hh (x i) y)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    intro i
    have h1 : AEStronglyMeasurable
        (fun x : Submission.BoseGases.X n => ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wPair ℓ hh (x i) y)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      Submission.BoseGases.aem_comp_coord' (N := n) (ℓ := ℓ) i
        (Submission.BoseGases.fibre_acube_aem hi)
    refine h1.congr ?_
    filter_upwards with x
    exact Submission.BoseGases.mean_kernel_full hℓ hwi (x i)
  have hsum : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => ∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wPair ℓ hh (x i) y)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    have hsum' := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
        (fun i _ => hfib i)
    have heq : (∑ i : Fin n, (fun x : Submission.BoseGases.X n =>
          ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wPair ℓ hh (x i) y))
        = (fun x : Submission.BoseGases.X n => ∑ i : Fin n,
          ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wPair ℓ hh (x i) y) := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq] at hsum'
    exact hsum'
  have hΦaesm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    (hΦc.pow 2).aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
  have haesm := hΦaesm.mul hsum
  -- the integrable majorant, continuous on the compact box
  have hg : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ((n : ℝ) * C))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ
      ((hΦc.pow 2).mul continuous_const)
  refine hg.mono' haesm ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (Φ x))
  calc |∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wPair ℓ hh (x i) y|
      ≤ ∑ i : Fin n, |∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wPair ℓ hh (x i) y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, C := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [hCdef]
        exact Submission.BoseGases.fibre_integral_abs_le hℓ hR hRℓ hi hsupp (x i)
    _ = (n : ℝ) * C := by simp [Finset.sum_const, nsmul_eq_mul]

end Work.BoseFixB1B
