import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_law
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.uniform_of_exp

/-!
# Basic analytic facts about the reference law `cNu` (and `cUnif`)

`cNu = canonM.map cY` is the law of the reference sum `cY = Σ_{k ≥ 1} e^{-S_k}`, hence a
probability measure carried by `[0,∞)`.  This file collects the small facts needed to run
the Laplace-transform argument for `∫ (1+z)⁻¹ d(cNu) = e^{-γ}`:

* measurability of `cY`, `cNu` is a probability measure, `cNu (Iio 0) = 0`;
* set-level facts about `cUnif = volume.restrict (Ioo 0 1)`;
* the Laplace transform `phi t = ∫ z, e^{-tz} d(cNu)`: value at `0`, bounds, continuity;
* a.e. non-negativity of `x * (1 + y)` under `cUnif.prod cNu`, and integrability of the
  associated exponentials (the inputs for the Fubini computation of the ODE).
-/

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ### Measurability and the probability-measure structure -/

lemma cSum_measurable (k : ℕ) : Measurable (fun x : ℕ → ℝ => cSum x k) := by
  unfold cSum
  exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i

lemma cY_measurable : Measurable cY := by
  unfold cY
  exact Measurable.tsum fun k => Real.measurable_exp.comp (cSum_measurable (k + 1)).neg

instance instIsProbabilityMeasureCNu : IsProbabilityMeasure cNu :=
  (Measure.isProbabilityMeasure_map_iff cY_measurable.aemeasurable).mpr inferInstance

lemma cY_nonneg (x : ℕ → ℝ) : 0 ≤ cY x := tsum_nonneg fun k => Real.exp_nonneg _

lemma cY_preimage_Iio_empty : cY ⁻¹' Set.Iio (0 : ℝ) = ∅ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
  exact cY_nonneg x

lemma cNu_Iio_zero : cNu (Set.Iio (0 : ℝ)) = 0 := by
  rw [cNu, Measure.map_apply cY_measurable measurableSet_Iio, cY_preimage_Iio_empty,
    measure_empty]

lemma ae_cNu_nonneg : ∀ᵐ z ∂cNu, 0 ≤ z := by
  rw [ae_iff]
  have h : {z : ℝ | ¬ 0 ≤ z} = Set.Iio 0 := by
    ext z; simp [Set.Iio]
  rw [h, cNu_Iio_zero]

lemma cNu_restrict_Ici : cNu.restrict (Set.Ici (0 : ℝ)) = cNu :=
  Measure.restrict_eq_self_of_ae_mem ae_cNu_nonneg

lemma cNu_Iio_neg_one : cNu (Set.Iio (-1 : ℝ)) = 0 :=
  measure_mono_null (fun z hz => by
    simp only [Set.mem_Iio] at hz ⊢
    linarith) cNu_Iio_zero

/-! ### Set-level facts about `cUnif` -/

lemma cUnif_Iio_zero_union_Ioi_one : cUnif (Set.Iio (0 : ℝ) ∪ Set.Ioi 1) = 0 := by
  rw [uniform_of_exp, Measure.restrict_apply (measurableSet_Iio.union measurableSet_Ioi)]
  have h : (Set.Iio (0 : ℝ) ∪ Set.Ioi 1) ∩ Set.Ioo (0 : ℝ) 1 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, h1, h2⟩
    rcases hx with hx | hx
    · simp only [Set.mem_Iio] at hx; linarith
    · simp only [Set.mem_Ioi] at hx; linarith
  rw [h, measure_empty]

/-! ### The Laplace transform `phi` -/

/-- The Laplace transform of the reference law `cNu`. -/
def phi (lam : ℝ) : ℝ := ∫ z, Real.exp (-(lam * z)) ∂cNu

lemma phi_zero : phi 0 = 1 := by
  have h1 : (fun z : ℝ => Real.exp (-((0 : ℝ) * z))) = fun _ => (1 : ℝ) := by
    funext z; simp
  rw [phi, h1, integral_const, Measure.real_def, measure_univ]
  simp

lemma phi_nonneg (lam : ℝ) : 0 ≤ phi lam :=
  integral_nonneg fun z => Real.exp_nonneg _

lemma integrable_exp_neg_mul_cNu (lam : ℝ) (hlam : 0 ≤ lam) :
    Integrable (fun z : ℝ => Real.exp (-(lam * z))) cNu := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg).aestronglyMeasurable
  · filter_upwards [ae_cNu_nonneg] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
    nlinarith

lemma phi_le_one (lam : ℝ) (hlam : 0 ≤ lam) : phi lam ≤ 1 := by
  have hint := integrable_exp_neg_mul_cNu lam hlam
  have h1 : phi lam ≤ ∫ _z : ℝ, (1 : ℝ) ∂cNu := by
    rw [phi]
    refine integral_mono_ae hint (integrable_const 1) ?_
    filter_upwards [ae_cNu_nonneg] with z hz
    rw [Real.exp_le_one_iff]
    nlinarith
  rw [integral_const, Measure.real_def, measure_univ] at h1
  simpa using h1

lemma phi_continuousOn : ContinuousOn phi (Set.Ici (0 : ℝ)) := by
  have h : ContinuousOn (fun lam : ℝ => ∫ z, Real.exp (-(lam * z)) ∂cNu)
      (Set.Ici (0 : ℝ)) :=
    continuousOn_of_dominated (μ := cNu)
      (F := fun lam (z : ℝ) => Real.exp (-(lam * z))) (bound := fun _ => (1 : ℝ))
      (s := Set.Ici (0 : ℝ))
      (fun lam _ => (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg).aestronglyMeasurable)
      (fun lam hlam => by
        have hlam' : (0 : ℝ) ≤ lam := hlam
        filter_upwards [ae_cNu_nonneg] with z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
        nlinarith [hlam', hz])
      (integrable_const 1)
      (by
        filter_upwards with z
        exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-(x * z))).continuousOn)
  change ContinuousOn (fun lam : ℝ => ∫ z, Real.exp (-(lam * z)) ∂cNu) (Set.Ici (0 : ℝ))
  exact h

/-! ### Non-negativity on the product and integrability of the exponentials -/

lemma ae_prod_nonneg_mul : ∀ᵐ p ∂(cUnif.prod cNu), 0 ≤ p.1 * (1 + p.2) := by
  rw [ae_iff]
  set T : Set (ℝ × ℝ) :=
    (Set.Iio (0 : ℝ) ∪ Set.Ioi 1) ×ˢ (Set.univ : Set ℝ)
      ∪ (Set.univ : Set ℝ) ×ˢ Set.Iio (-1 : ℝ) with hT
  have hsub : {p : ℝ × ℝ | ¬ (0 ≤ p.1 * (1 + p.2))} ⊆ T := by
    intro p hp
    simp only [Set.mem_ofPred_eq, not_le] at hp
    rw [hT]
    rcases lt_trichotomy p.1 0 with h | h | h
    · exact Or.inl ⟨Or.inl h, trivial⟩
    · rw [h, zero_mul] at hp
      exact absurd hp (lt_irrefl 0)
    · rcases lt_trichotomy p.2 (-1) with h2 | h2 | h2
      · exact Or.inr ⟨trivial, h2⟩
      · rw [h2] at hp
        norm_num at hp
      · have h3 : 0 < 1 + p.2 := by linarith
        have h4 : 0 < p.1 * (1 + p.2) := mul_pos h h3
        exact absurd hp (not_lt.mpr h4.le)
  refine measure_mono_null hsub ?_
  rw [hT]
  refine le_antisymm ((measure_union_le _ _).trans ?_) bot_le
  rw [Measure.prod_prod, Measure.prod_prod, cUnif_Iio_zero_union_Ioi_one, cNu_Iio_neg_one]
  simp

lemma integrable_exp_neg_mul_prod (lam : ℝ) (hlam : 0 ≤ lam) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-(lam * (p.1 * (1 + p.2)))))
      (cUnif.prod cNu) := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_fst.mul (continuous_const.add continuous_snd))).neg).aestronglyMeasurable
  · filter_upwards [ae_prod_nonneg_mul] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
    nlinarith [hp, hlam]

end

end Work.ChenPlan.LinearSieve.Selberg.Alt
