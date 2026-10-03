import Mathlib
import Submission.Work.A3.kmtPair_helpers

namespace Work.A3

open MeasureTheory

/-- `kmtPair` is additive in its first (coefficient-space) argument: a finite `ℂ`-linear
combination of indicators on the `ℤ` side pulls out of the pairing.  (Companion of
`Work.A3.kmtPair_sum_right`.) -/
lemma kmtPair_left_sum (s : Finset ℤ) (T : Finset ℂ) (γ : ℂ → ℂ) (B : ℂ → Set ℤ) (D : Set ℝ) (hD : MeasurableSet D) : Work.A3.kmtPair s (∑ c ∈ T, γ c • Set.indicator (B c) (fun _ => (1 : ℂ))) (Set.indicator D (fun _ => (1 : ℂ))) = ∑ c ∈ T, γ c * Work.A3.kmtPair s (Set.indicator (B c) (fun _ => (1 : ℂ))) (Set.indicator D (fun _ => (1 : ℂ))) := by
  have hI : ∀ u : ℤ → ℂ, kmtPair s u (Set.indicator D (fun _ => (1 : ℂ)))
      = ∫ θ, kmtSum s u θ * Set.indicator D (fun _ => (1 : ℂ)) θ ∂kmtNu :=
    fun u => kmtPair_of_aemeasurable (aemeasurable_indicator_one hD)
  simp_rw [hI]
  have hfun : (fun θ : ℝ =>
        kmtSum s (∑ c ∈ T, γ c • Set.indicator (B c) (fun _ => (1 : ℂ))) θ
          * Set.indicator D (fun _ => (1 : ℂ)) θ)
      = fun θ : ℝ => ∑ c ∈ T, γ c * (kmtSum s (Set.indicator (B c) (fun _ => (1 : ℂ))) θ
          * Set.indicator D (fun _ => (1 : ℂ)) θ) := by
    funext θ
    rw [kmtSum_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hInt : (∫ θ, ∑ c ∈ T, γ c * (kmtSum s (Set.indicator (B c) (fun _ => (1 : ℂ))) θ
        * Set.indicator D (fun _ => (1 : ℂ)) θ) ∂kmtNu)
      = ∑ c ∈ T, γ c * ∫ θ, kmtSum s (Set.indicator (B c) (fun _ => (1 : ℂ))) θ
        * Set.indicator D (fun _ => (1 : ℂ)) θ ∂kmtNu := by
    rw [integral_finsetSum T
      (fun c _ => (integrable_kmtSum_mul_indicator s _ hD).const_mul (γ c))]
    exact Finset.sum_congr rfl fun c _ => integral_const_mul (γ c) _
  rw [hfun, hInt]

end Work.A3
