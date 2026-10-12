import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1S.PiLintegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.PiCoordMeanL2` — the `L²`-membership and contraction of the coordinate mean

The ANOVA bound needs the coordinate mean `E_j u` of an `L²` function to be *itself* in `L²`, with
`∫ (E_j u)² ≤ ∫ u²`.  This module provides that in the strong (conjunctive) form
`integrable_and_integral_sq_pi_coordMean_le`, using:

* `sq_integral_le_measure_mul_integral_sq` — the fibre Cauchy–Schwarz
  `(∫ z, g z ∂ν)² ≤ (ν univ).toReal · ∫ z, (g z)² ∂ν` (Hölder with `p = q = 2`), valid whenever the
  fibre is a.e. strongly measurable and square integrable;
* `integrable_pi_coordIntegral_sq` — the fibre `L²`-mass `x ↦ ∫ z, (u (update x j z))² ∂ν` of an
  `L²` function is integrable (Fubini on the peeled product, transported across `piFinSuccAbove`);
* `ae_pi_slice_lintegral_lt_top` (from `PiLintegral.lean`) plus
  `ae_aestronglyMeasurable_pi_slice` (from `AnovaInfra.lean`) for the a.e. hypotheses of the fibre
  Cauchy–Schwarz;
* the Bochner peel `pi_peel` for the final evaluation of the fibre `L²`-mass.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

variable {α : Type*} [MeasurableSpace α]

/-- **Fibre Cauchy–Schwarz.**  `(∫ z, g z ∂ν)² ≤ (ν univ).toReal · ∫ z, (g z)² ∂ν` for an a.e.
strongly measurable, square-integrable `g`.  (Hölder with `p = q = 2` and the constant test
function.) -/
theorem sq_integral_le_measure_mul_integral_sq {β : Type*} [MeasurableSpace β] {μ : Measure β}
    [IsFiniteMeasure μ] {g : β → ℝ}
    (hgm : AEStronglyMeasurable g μ) (hg2 : Integrable (fun z => (g z) ^ 2) μ) :
    (∫ z, g z ∂μ) ^ 2 ≤ (μ Set.univ).toReal * ∫ z, (g z) ^ 2 ∂μ := by
  have hgi : Integrable g μ := by
    refine Integrable.mono' (g := fun z => (g z) ^ 2 + 1) ?_ hgm ?_
    · exact (hg2.add (integrable_const 1))
    · filter_upwards with z
      have h : (0 : ℝ) ≤ (g z) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (g z), sq_abs (g z), le_abs_self (g z), neg_le_abs (g z)]
  have hMem1 : MemLp (fun _ : β => (1 : ℝ)) (2 : ℝ≥0∞) μ :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_const).mpr
      (by simpa using integrable_const (1 : ℝ))
  have hMemg : MemLp g (2 : ℝ≥0∞) μ := (memLp_two_iff_integrable_sq hgm).mpr hg2
  rw [← ENNReal.ofReal_ofNat 2] at hMem1 hMemg
  have hHolder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := fun _ : β => (1 : ℝ)) (g := g)
    (p := 2) (q := 2) Real.HolderConjugate.two_two hMem1 hMemg
  have h4 : (∫ z, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂μ) = (μ Set.univ).toReal := by
    rw [show (fun z : β => ‖(1 : ℝ)‖ ^ (2 : ℝ)) = fun _ : β => (1 : ℝ) from by
      funext z; rw [Real.rpow_two]; norm_num]
    rw [integral_const, Measure.real_def, smul_eq_mul, mul_one]
  have h5 : (∫ z, ‖g z‖ ^ (2 : ℝ) ∂μ) = ∫ z, (g z) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with z
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hle : ‖∫ z, g z ∂μ‖ ≤ Real.sqrt ((μ Set.univ).toReal) * Real.sqrt (∫ z, (g z) ^ 2 ∂μ) := by
    calc ‖∫ z, g z ∂μ‖
        ≤ ∫ z, ‖g z‖ ∂μ := norm_integral_le_integral_norm g
      _ = ∫ z, ‖(1 : ℝ)‖ * ‖g z‖ ∂μ := by
          apply integral_congr_ae
          filter_upwards with z
          simp
      _ ≤ (∫ z, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
            * (∫ z, ‖g z‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hHolder
      _ = Real.sqrt ((μ Set.univ).toReal) * Real.sqrt (∫ z, (g z) ^ 2 ∂μ) := by
          rw [h4, h5, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hsq : (∫ z, g z ∂μ) ^ 2 ≤ (Real.sqrt ((μ Set.univ).toReal)
      * Real.sqrt (∫ z, (g z) ^ 2 ∂μ)) ^ 2 := by
    rw [← sq_abs (∫ z, g z ∂μ)]
    exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  refine hsq.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt (integral_nonneg fun z => sq_nonneg _)]

/-- **The fibre `L²`-mass of an `L²` function is integrable.** -/
theorem integrable_pi_coordIntegral_sq (ν : Measure α) [SigmaFinite ν] [IsFiniteMeasure ν]
    {k : ℕ} (j : Fin (k + 1)) {u : (Fin (k + 1) → α) → ℝ}
    (hu2 : Integrable (fun x => (u x) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    Integrable (fun x : Fin (k + 1) → α => ∫ z, (u (Function.update x j z)) ^ 2 ∂ν)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j
  let ρ : Measure (Fin k → α) := Measure.pi (fun _ : Fin k => ν)
  let π : Measure (Fin (k + 1) → α) := Measure.pi (fun _ : Fin (k + 1) => ν)
  have hmp : MeasurePreserving e π (ν.prod ρ) :=
    measurePreserving_piFinSuccAbove (μ := fun _ : Fin (k + 1) => ν) j
  have hmp' : MeasurePreserving (e.symm) (ν.prod ρ) π := MeasurePreserving.symm e hmp
  have hemb : MeasurableEmbedding (e.symm) := MeasurableEquiv.measurableEmbedding e.symm
  have hembe : MeasurableEmbedding e := MeasurableEquiv.measurableEmbedding e
  have hG : Integrable (fun p : α × (Fin k → α) => (u (e.symm p)) ^ 2) (ν.prod ρ) :=
    (hmp'.integrable_comp_emb hemb).mpr hu2
  have hI : Integrable (fun r : Fin k → α => ∫ z, (u (e.symm (z, r))) ^ 2 ∂ν) ρ :=
    hG.integral_prod_right
  have hC : Integrable (fun p : α × (Fin k → α) => ∫ z, (u (e.symm (z, p.2))) ^ 2 ∂ν)
      (ν.prod ρ) := hI.comp_snd ν
  have hMain : Integrable (fun x : Fin (k + 1) → α => ∫ z, (u (e.symm (z, (e x).2))) ^ 2 ∂ν) π :=
    (hmp.integrable_comp_emb hembe).mpr hC
  refine hMain.congr (Filter.Eventually.of_forall fun x => ?_)
  apply integral_congr_ae
  filter_upwards with z
  rw [← piFinSuccAbove_update (α := α) j (e x) z, MeasurableEquiv.symm_apply_apply]

/-- **The coordinate mean of an `L²` function is in `L²` and contracts the `L²`-norm.** -/
theorem integrable_and_integral_sq_pi_coordMean_le (ν : Measure α) [SigmaFinite ν]
    [IsFiniteMeasure ν] (hν : 0 < (ν Set.univ).toReal) {k : ℕ} (j : Fin (k + 1))
    {u : (Fin (k + 1) → α) → ℝ}
    (hum : AEStronglyMeasurable u (Measure.pi (fun _ : Fin (k + 1) => ν)))
    (hu2 : Integrable (fun x => (u x) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    Integrable (fun x : Fin (k + 1) → α =>
        ((1 / (ν Set.univ).toReal) * ∫ z, u (Function.update x j z) ∂ν) ^ 2)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) ∧
    ∫ x, ((1 / (ν Set.univ).toReal) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      ≤ ∫ x, (u x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  set V : ℝ := (ν Set.univ).toReal with hVdef
  have hVpos : 0 < V := hν
  have hFib : Integrable (fun x : Fin (k + 1) → α => ∫ z, (u (Function.update x j z)) ^ 2 ∂ν)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) := integrable_pi_coordIntegral_sq ν j hu2
  have hSliceSM : ∀ᵐ x ∂(Measure.pi (fun _ : Fin (k + 1) => ν)),
      AEStronglyMeasurable (fun z => u (Function.update x j z)) ν :=
    ae_aestronglyMeasurable_pi_slice ν j hum
  have hSliceFin : ∀ᵐ x ∂(Measure.pi (fun _ : Fin (k + 1) => ν)),
      ∫⁻ z, ‖u (Function.update x j z)‖ₑ ^ 2 ∂ν < ∞ :=
    ae_pi_slice_lintegral_lt_top ν j hum hu2
  -- a.e. slice square-integrability
  have hSliceL2 : ∀ᵐ x ∂(Measure.pi (fun _ : Fin (k + 1) => ν)),
      Integrable (fun z => (u (Function.update x j z)) ^ 2) ν := by
    filter_upwards [hSliceSM, hSliceFin] with x hsm hfin
    exact ⟨hsm.pow 2, by
      rw [hasFiniteIntegral_iff_enorm]
      simpa only [enorm_pow] using hfin⟩
  -- the a.e. pointwise bound
  have hpoint : ∀ᵐ x ∂(Measure.pi (fun _ : Fin (k + 1) => ν)),
      ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
        ≤ (1 / V) * ∫ z, (u (Function.update x j z)) ^ 2 ∂ν := by
    filter_upwards [hSliceSM, hSliceL2] with x hsm hl2
    have hcs := sq_integral_le_measure_mul_integral_sq hsm hl2
    have hV' : (1 / V) * (ν Set.univ).toReal = 1 := by
      rw [← hVdef]
      field_simp
    calc ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
        = (1 / V) ^ 2 * (∫ z, u (Function.update x j z) ∂ν) ^ 2 := by ring
      _ ≤ (1 / V) ^ 2 * ((ν Set.univ).toReal * ∫ z, (u (Function.update x j z)) ^ 2 ∂ν) := by
          exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = (1 / V) * ∫ z, (u (Function.update x j z)) ^ 2 ∂ν := by
          rw [← hVdef]
          field_simp
  have hDom : Integrable (fun x : Fin (k + 1) → α =>
      (1 / V) * ∫ z, (u (Function.update x j z)) ^ 2 ∂ν) (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    hFib.const_mul _
  have hInt : Integrable (fun x : Fin (k + 1) → α =>
      ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    refine Integrable.mono' hDom
      ((aestronglyMeasurable_pi_coordMean ν j hum).const_mul (1 / V) |>.pow 2) ?_
    filter_upwards [hpoint] with x hx
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  refine ⟨hInt, ?_⟩
  have hmono : ∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      ≤ ∫ x, (1 / V) * ∫ z, (u (Function.update x j z)) ^ 2 ∂ν
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    integral_mono_ae hInt hDom hpoint
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, pi_peel ν j hu2]
  rw [← hVdef]
  field_simp

end Work.BoseFixB1S
