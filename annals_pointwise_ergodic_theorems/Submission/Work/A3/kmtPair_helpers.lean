import Mathlib
import Submission.Work.A3.HausdorffYoungDefs

/-!
# Elementary lemmas for the level-set decomposition of `kmtPair`

This module collects the small facts that the decomposition of the pairing
`Work.A3.kmtPair s u v` into level sets of simple functions needs:

* a *real* norm bound for the truncated Fourier sum `kmtSum` (the `enorm` version is
  `Work.A3.enorm_kmtSum_le`);
* the a.e.-measurability of a single level-set indicator, and of a finite combination
  `∑ d ∈ U, δ d • 1_{D d}` of such indicators (with measurable level sets);
* the integrability, for the probability measure `kmtNu`, of
  `θ ↦ kmtSum s u θ * 1_D θ`
  which is what makes the finite sums pull out of the Bochner integral in
  `Work.A3.kmtPair_sum_right` and `Work.A3.kmtPair_left_sum`.
-/

set_option autoImplicit false

namespace Work.A3

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Real-norm bound of the truncated Fourier sum by the `ℓ¹` norm of its coefficient
function.  (Real-norm companion of `Work.A3.enorm_kmtSum_le`.) -/
lemma norm_kmtSum_le (s : Finset ℤ) (u : ℤ → ℂ) (θ : ℝ) :
    ‖kmtSum s u θ‖ ≤ ∑ x ∈ s, ‖u x‖ := by
  rw [kmtSum_apply]
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  exact Finset.sum_congr rfl fun x _ => by rw [norm_mul, norm_kmtChar, mul_one]

/-- The indicator `1_D` of a measurable set is a.e.-measurable for `kmtNu`. -/
lemma aemeasurable_indicator_one {D : Set ℝ} (hD : MeasurableSet D) :
    AEMeasurable (Set.indicator D (fun _ => (1 : ℂ))) kmtNu :=
  (measurable_const.indicator hD).aemeasurable

/-- A finite combination `∑ d ∈ U, δ d • 1_{D d}` of level-set indicators (with measurable
level sets) is a.e.-measurable for `kmtNu`. -/
lemma aemeasurable_sum_smul_indicator (U : Finset ℂ) (δ : ℂ → ℂ) (D : ℂ → Set ℝ)
    (hD : ∀ d ∈ U, MeasurableSet (D d)) :
    AEMeasurable (∑ d ∈ U, δ d • Set.indicator (D d) (fun _ => (1 : ℂ))) kmtNu := by
  refine Finset.aemeasurable_sum U fun d hd => ?_
  exact ((measurable_const.indicator (hD d hd)).const_mul (δ d)).aemeasurable

/-- For a measurable set `D`, the product of the truncated Fourier sum with `1_D` is
integrable for `kmtNu`: it is a.e.-measurable and bounded by the `ℓ¹` norm of the
coefficients. -/
lemma integrable_kmtSum_mul_indicator (s : Finset ℤ) (u : ℤ → ℂ) {D : Set ℝ}
    (hD : MeasurableSet D) :
    Integrable (fun θ : ℝ => kmtSum s u θ * Set.indicator D (fun _ => (1 : ℂ)) θ) kmtNu := by
  refine Integrable.of_bound ?_ (∑ x ∈ s, ‖u x‖) ?_
  · exact ((continuous_kmtSum s u).measurable.mul
      (measurable_const.indicator hD)).aestronglyMeasurable
  · filter_upwards with θ
    rw [norm_mul]
    have h1 : ‖Set.indicator D (fun _ => (1 : ℂ)) θ‖ ≤ 1 := by
      by_cases h : θ ∈ D
      · rw [Set.indicator_of_mem h]; simp
      · rw [Set.indicator_of_notMem h]; simp
    calc ‖kmtSum s u θ‖ * ‖Set.indicator D (fun _ => (1 : ℂ)) θ‖
        ≤ (∑ x ∈ s, ‖u x‖) * 1 :=
          mul_le_mul (norm_kmtSum_le s u θ) h1 (norm_nonneg _)
            (Finset.sum_nonneg fun x _ => norm_nonneg _)
      _ = ∑ x ∈ s, ‖u x‖ := mul_one _

end

end Work.A3
