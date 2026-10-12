import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.WB.Lead
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.WB.ji_helpers` — pieces of `jensen_integrated`

This module collects the elementary pieces of the proof of
`Work.BoseFixB1.WB.jensen_integrated` that do not depend on any external
integrability input:

* `boxInner` — the `u`-dependent `x`-integral `∫_{abox n ℓ} Φ² F(nCountB u/chiMass u)`,
  i.e. exactly the inner factor of `RPsiB`;
* `boxInner_nonneg` — it is nonnegative;
* `aestronglyMeasurable_boxInner` — it is a.e. strongly measurable in `u`
  (joint measurability plus `AEStronglyMeasurable.integral_prod_right'`);
* `integrableOn_wbMass_mul_boxInner_of` — given (i) integrability of the localised
  mass `wbMass` on `I₋` and (ii) a uniform bound `boxInner u ≤ M`, the product
  `u ↦ wbMass u · boxInner u` is integrable on `I₋` (dominated by `M·wbMass`).
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WB

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `x`-integral `∫_{abox n ℓ} Φ²·F(nCountB(u)/chiMass(u))` of FS's step 4,
i.e. the inner factor of `RPsiB` at FS's parameters. -/
def boxInner (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) (u : ℝ³) : ℝ :=
  ∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 * psiWeight 1 μ
        (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
          / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)

/-- FS's weight `F = psiWeight 1 μ` is nonnegative on the physical range `t ≥ 0`
(for `μ > 0`). -/
lemma psiWeight_one_nonneg_local {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ psiWeight 1 μ t := by
  rw [psiWeight]
  refine div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) ?_
  have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (inv_nonneg.mpr hμ.le)
  linarith

/-- `boxInner` is nonnegative for `μ > 0`. -/
lemma boxInner_nonneg {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ} (hμ : 0 < μ)
    (Φ : X n → ℝ) (u : ℝ³) : 0 ≤ boxInner v h μ n Φ u := by
  rw [boxInner]
  refine integral_nonneg fun x => ?_
  exact mul_nonneg (sq_nonneg _)
    (psiWeight_one_nonneg_local hμ (div_nonneg (nCountB_nonneg _ _ _ _ x) (chiMass_nonneg _ _ _ _)))

/-- The `x`-integrand of `boxInner` is jointly measurable in `(u,x)`. -/
lemma aestronglyMeasurable_boxInner_integrand {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (hM : 1 ≤ (paramsAt μ (a v)).M) (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) :
    AEMeasurable (fun p : ℝ³ × X n =>
        (Φ p.2) ^ 2 * psiWeight 1 μ
          (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d p.1 p.2
            / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d p.1))
      (volume.prod (volume.restrict (abox n (sideAt μ (a v))))) := by
  have hmeasN : Measurable (fun p : ℝ³ × X n =>
      nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d p.1 p.2) := by
    simp only [nCountB]
    refine Finset.measurable_sum _ fun i _ => ?_
    simp only [chiSmallB]
    refine Measurable.pow_const ?_ 2
    refine Measurable.mul ?_ ?_
    · exact (chiScale_continuous (sideAt μ (a v))).measurable.comp
        ((measurable_pi_apply i).comp measurable_snd)
    · exact (chiSmall_continuous hM).measurable.comp
        ((((measurable_pi_apply i).comp measurable_snd).const_smul
          ((sideAt μ (a v) * (paramsAt μ (a v)).d)⁻¹)).sub measurable_fst)
  have hmeasC : AEMeasurable (fun p : ℝ³ × X n =>
      chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d p.1)
      (volume.prod (volume.restrict (abox n (sideAt μ (a v))))) := by
    have hC : AEStronglyMeasurable (fun u : ℝ³ =>
        chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) volume := by
      simpa only [chiMass_def] using
        (Work.SmallBoxSliding.integrable_chiSmallB_mass hM hℓ hd).aestronglyMeasurable
    exact (hC.aemeasurable.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ³))
        (ν := volume.restrict (abox n (sideAt μ (a v))))))
  refine AEMeasurable.mul ?_ ?_
  · exact (((Φ.contDiff.continuous.measurable.pow_const 2).comp measurable_snd).aemeasurable)
  · have hpsi : Measurable (fun t : ℝ => psiWeight 1 μ t) := by
      simp only [psiWeight]
      fun_prop
    exact hpsi.comp_aemeasurable (hmeasN.aemeasurable.div hmeasC)

/-- `u ↦ boxInner … u` is a.e. strongly measurable (it is the integral in `x` of a
jointly measurable function). -/
lemma aestronglyMeasurable_boxInner {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (hM : 1 ≤ (paramsAt μ (a v)).M) (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) :
    AEStronglyMeasurable (boxInner v h μ n (Φ : X n → ℝ)) volume := by
  have h := (aestronglyMeasurable_boxInner_integrand (v := v) (h := h) (μ := μ) (n := n)
    hM hℓ hd Φ).aestronglyMeasurable
  exact h.integral_prod_right'

/-- **Gluing**: if the localised mass is integrable on `I₋` and `boxInner` is
uniformly bounded, then the product is integrable on `I₋` (it is dominated by
`M · wbMass`). -/
lemma integrableOn_wbMass_mul_boxInner_of {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (hμ : 0 < μ) (hM : 1 ≤ (paramsAt μ (a v)).M) (hℓ : 0 < sideAt μ (a v))
    (hd : 0 < (paramsAt μ (a v)).d) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v)))
    (hwb : ∀ u : ℝ³, 0 ≤ wbMass v h μ u)
    (hInt : IntegrableOn (fun u : ℝ³ => wbMass v h μ u)
      (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hMb : ∀ u : ℝ³, boxInner v h μ n Φ u ≤ M) :
    IntegrableOn (fun u : ℝ³ => wbMass v h μ u * boxInner v h μ n (Φ : X n → ℝ) u)
      (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) := by
  have hdom : IntegrableOn (fun u : ℝ³ => M * wbMass v h μ u)
      (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) := hInt.const_mul M
  refine hdom.mono' ?_ ?_
  · refine AEStronglyMeasurable.mul hInt.aestronglyMeasurable ?_
    exact (aestronglyMeasurable_boxInner (v := v) (h := h) (μ := μ) (n := n) hM hℓ hd Φ
      ).mono_measure Measure.restrict_le_self
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwb u) (boxInner_nonneg hμ Φ u))]
    calc wbMass v h μ u * boxInner v h μ n (Φ : X n → ℝ) u
        ≤ wbMass v h μ u * M := mul_le_mul_of_nonneg_left (hMb u) (hwb u)
      _ = M * wbMass v h μ u := by ring

end Work.BoseFixB1.WB
