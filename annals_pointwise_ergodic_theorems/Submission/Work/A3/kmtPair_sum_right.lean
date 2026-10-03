import Mathlib
import Submission.Work.A3.kmtPair_helpers

namespace Work.A3

lemma kmtPair_sum_right (s : Finset ℤ) (u : ℤ → ℂ) (U : Finset ℂ) (δ : ℂ → ℂ) (D : ℂ → Set ℝ) (hD : ∀ d ∈ U, MeasurableSet (D d)) : Work.A3.kmtPair s u (∑ d ∈ U, δ d • Set.indicator (D d) (fun _ => (1 : ℂ))) = ∑ d ∈ U, δ d * Work.A3.kmtPair s u (Set.indicator (D d) (fun _ => (1 : ℂ))) := by
  open MeasureTheory in
  have hpoint : ∀ θ : ℝ, kmtSum s u θ *
      ((∑ d ∈ U, δ d • Set.indicator (D d) (fun _ => (1 : ℂ))) θ)
      = ∑ d ∈ U, δ d * (kmtSum s u θ * Set.indicator (D d) (fun _ => (1 : ℂ)) θ) := by
    intro θ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hR : (∑ d ∈ U, δ d * kmtPair s u (Set.indicator (D d) (fun _ => (1 : ℂ))))
      = ∑ d ∈ U, δ d * ∫ θ, kmtSum s u θ * Set.indicator (D d) (fun _ => (1 : ℂ)) θ
          ∂kmtNu :=
    Finset.sum_congr rfl fun d hd => by
      rw [kmtPair_of_aemeasurable (aemeasurable_indicator_one (hD d hd))]
  rw [hR, kmtPair_of_aemeasurable (aemeasurable_sum_smul_indicator U δ D hD)]
  simp only [hpoint]
  rw [integral_finsetSum U (fun d hd =>
    (integrable_kmtSum_mul_indicator s u (hD d hd)).const_mul (δ d))]
  exact Finset.sum_congr rfl fun d _ => by rw [integral_const_mul]

end Work.A3
