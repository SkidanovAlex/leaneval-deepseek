import Mathlib
import Submission.Work.EQ.summable_lamInv_pow_mul

namespace Work.EQ

/-- The resolvent identity for the linear operator `Λ F (u) = F (λ u) / λ - λ F (u / λ)`:
the two series telescope and cancel, leaving `F u`. -/
theorem lam_resolvent {lam R C : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R)
    {F : ℂ → ℂ} (hF : ∀ z, ‖z‖ < R → ‖F z‖ ≤ C * ‖z‖ ^ 2) (u : ℂ) (hu : ‖u‖ < R) :
    (lam : ℂ)⁻¹ * (-∑' (j : ℕ), (((lam : ℂ) ^ (2 * j + 1))⁻¹) * F (((lam : ℂ) ^ (2 * j + 1)) * ((lam : ℂ) * u)))
      - (lam : ℂ) * (-∑' (j : ℕ), (((lam : ℂ) ^ (2 * j + 1))⁻¹) * F (((lam : ℂ) ^ (2 * j + 1)) * (u / (lam : ℂ))))
      = F u := by
  have hcne : (lam : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hlam0)
  have hTsumm0 : Summable (fun k : ℕ => (((lam : ℂ) ^ (2 * k))⁻¹) * F (((lam : ℂ) ^ (2 * k)) * u)) :=
    summable_lamInv_pow_mul hlam0 hlam1 hR hF u hu
  set T : ℕ → ℂ := fun k => (((lam : ℂ) ^ (2 * k))⁻¹) * F (((lam : ℂ) ^ (2 * k)) * u) with hT
  have hTsumm : Summable T := by rw [hT]; exact hTsumm0
  have hT0 : T 0 = F u := by simp only [hT]; simp
  have htel : (∑' k, T k) = T 0 + ∑' k, T (k+1) := hTsumm.tsum_eq_zero_add
  -- pointwise: `λ⁻¹` applied to the first summand is the `(j+1)`-term of `T`
  have hptA : ∀ j, (lam : ℂ)⁻¹ *
      ((((lam : ℂ) ^ (2 * j + 1))⁻¹) * F (((lam : ℂ) ^ (2 * j + 1)) * ((lam : ℂ) * u)))
      = T (j+1) := by
    intro j
    simp only [hT]
    have h1 : (lam : ℂ) ^ (2*(j+1)) = (lam : ℂ) ^ (2*j+1) * (lam : ℂ) := by
      rw [show 2*(j+1) = (2*j+1)+1 by ring, pow_succ]
    have h2 : ((lam : ℂ) ^ (2*(j+1)))⁻¹ = (lam : ℂ)⁻¹ * ((lam : ℂ) ^ (2*j+1))⁻¹ := by
      rw [h1, mul_inv_rev]
    have h3 : (lam : ℂ) ^ (2*(j+1)) * u = (lam : ℂ) ^ (2*j+1) * ((lam : ℂ) * u) := by
      rw [h1, mul_assoc]
    rw [h2, h3, mul_assoc]
  -- pointwise: `λ` applied to the second summand is the `j`-term of `T`
  have hptB : ∀ j, (lam : ℂ) *
      ((((lam : ℂ) ^ (2 * j + 1))⁻¹) * F (((lam : ℂ) ^ (2 * j + 1)) * (u / (lam : ℂ))))
      = T j := by
    intro j
    simp only [hT]
    have h1 : (lam : ℂ) ^ (2*j+1) = (lam : ℂ) ^ (2*j) * (lam : ℂ) := by
      rw [show 2*j+1 = (2*j)+1 by ring, pow_succ]
    have h2 : (lam : ℂ) * ((lam : ℂ) ^ (2*j+1))⁻¹ = ((lam : ℂ) ^ (2*j))⁻¹ := by
      rw [h1, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
    have h3 : (lam : ℂ) ^ (2*j+1) * (u / (lam : ℂ)) = (lam : ℂ) ^ (2*j) * u := by
      rw [h1, mul_assoc, mul_div_cancel₀ u hcne]
    rw [← mul_assoc, h2, h3]
  have hX : (lam : ℂ)⁻¹ * (∑' j, (((lam : ℂ) ^ (2 * j + 1))⁻¹) * F (((lam : ℂ) ^ (2 * j + 1)) * ((lam : ℂ) * u)))
      = ∑' j, T (j+1) := by
    rw [← tsum_mul_left]
    exact tsum_congr hptA
  have hY : (lam : ℂ) * (∑' j, (((lam : ℂ) ^ (2 * j + 1))⁻¹) * F (((lam : ℂ) ^ (2 * j + 1)) * (u / (lam : ℂ))))
      = ∑' j, T j := by
    rw [← tsum_mul_left]
    exact tsum_congr hptB
  have key : (lam : ℂ)⁻¹ * (-∑' (j : ℕ), (((lam : ℂ) ^ (2 * j + 1))⁻¹) * F (((lam : ℂ) ^ (2 * j + 1)) * ((lam : ℂ) * u)))
      - (lam : ℂ) * (-∑' (j : ℕ), (((lam : ℂ) ^ (2 * j + 1))⁻¹) * F (((lam : ℂ) ^ (2 * j + 1)) * (u / (lam : ℂ))))
      = -(∑' j, T (j+1)) + ∑' j, T j := by
    rw [mul_neg, mul_neg, hX, hY]
    ring
  rw [key, htel, hT0]
  ring

end Work.EQ
