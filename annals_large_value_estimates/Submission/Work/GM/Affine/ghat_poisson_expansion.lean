import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.ghat_fourier_expansion
import Submission.Work.GM.Affine.psi1_poisson

namespace Work.GM.Affine

theorem ghat_poisson_expansion {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (ξ : ℝ) :
    ghat K M₁ M₂ M₃ f ξ =
      ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂,
        ((((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ))) *
          ((M₃ : ℂ) * ∑' ℓ : ℤ, psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ)))) := by
  rw [ghat_fourier_expansion hK hM₁ hM₂ hM₃ hf hcs ξ]
  refine Finset.sum_congr rfl (fun m₁ hm₁ => ?_)
  refine Finset.sum_congr rfl (fun m₂ hm₂ => ?_)
  have hm₁ne : (m₁ : ℝ) ≠ 0 := by
    intro h0
    have h' : M₁ < |(m₁ : ℝ)| := (Finset.mem_filter.mp hm₁).2
    rw [h0] at h'
    simp at h'
    linarith
  have hm₂pos : (0 : ℝ) < (m₂ : ℝ) := by
    have h : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
    exact_mod_cast h
  have hsum : (∑ m₃ ∈ R3ext K M₃,
        ((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) * ((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
          Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ)) * efun (ξ * (m₃ : ℝ) / (m₁ : ℝ)))
      = (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) * Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ))) *
          (∑ m₃ ∈ R3ext K M₃,
            ((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) * efun ((ξ / (m₁ : ℝ)) * (m₃ : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m₃ _ => ?_)
    have harg : ξ * (m₃ : ℝ) / (m₁ : ℝ) = (ξ / (m₁ : ℝ)) * (m₃ : ℝ) :=
      (div_mul_eq_mul_div ξ (m₁ : ℝ) (m₃ : ℝ)).symm
    rw [harg]
    ring
  rw [hsum, psi1_poisson hK hM₃ (ξ / (m₁ : ℝ))]
  rw [show ((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) = (((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) by
    rw [abs_div, abs_of_pos hm₂pos]]

end Work.GM.Affine
