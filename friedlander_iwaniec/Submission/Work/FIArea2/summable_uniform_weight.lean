import Mathlib
import Submission.Work.FIArea2.G8Defs
import Submission.Work.FIArea2.sec9_frequency_sum_bound

namespace Work.FIArea2

/-- **Summability of the uniform `h`-sum of (9.2)/(9.3).**  For `Δ(z₁,z₂) ≠ 0` and any `H > 0`
the uniformly weighted sum `Σ'_{(h₁,h₂)≠(0,0)}(Λ,Δ)(1+h₁²H^{−2})^{−1}(1+h₂²H^{−2})^{−1}` is
absolutely convergent: `(Λ,Δ) = gcdDelta z₁ z₂ h₁ h₂ ≤ |Δ|` is bounded, and each of the two
one-dimensional factors is dominated termwise by a multiple of `(1+h²H^{−2})^{−1}`, whose sum over
`h ∈ ℤ` converges for `H > 0` (`Work.FIArea2.summable_inv_one_add_mul_sq` with `c = H^{−2}`). -/
theorem summable_uniform_weight (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (H : ℝ) (hH : 0 < H) :
    Summable (fun p : ℤ × ℤ => (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹)) := by
  -- the one-dimensional weight series `∑_h (1 + h²/H²)⁻¹` converges (with `c = H⁻²`)
  have hc : 0 < (H ^ 2)⁻¹ := by positivity
  have hsum : Summable (fun t : ℤ => (1 + (t : ℝ) ^ 2 / H ^ 2)⁻¹) := by
    refine (summable_inv_one_add_mul_sq (H ^ 2)⁻¹ hc).congr (fun t => ?_)
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  have hwnn : ∀ t : ℤ, 0 ≤ (1 + (t : ℝ) ^ 2 / H ^ 2)⁻¹ := fun t => by positivity
  -- hence the product series converges, and so does any constant multiple of it
  have hsumprod : Summable (fun p : ℤ × ℤ =>
      (1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹) :=
    Summable.mul_of_nonneg hsum hsum hwnn hwnn
  have hMaj : Summable (fun p : ℤ × ℤ => ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) *
      ((1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹)) :=
    hsumprod.mul_left _
  -- `(Λ,Δ) ≤ |Δ|` gives the termwise domination by `|Δ|` times the product series
  refine Summable.of_nonneg_of_le (f := fun p : ℤ × ℤ => ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) *
      ((1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹)) ?_ ?_ hMaj
  · intro p
    by_cases hp : p = (0, 0)
    · simp [hp]
    · rw [if_neg hp]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hwnn p.1)) (hwnn p.2)
  · intro p
    by_cases hp : p = (0, 0)
    · rw [if_pos hp]
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hwnn p.1) (hwnn p.2))
    · rw [if_neg hp]
      calc (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
            * (1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹
          ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * (1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (hwnn p.2)
            exact mul_le_mul_of_nonneg_right (gcdDelta_cast_le_absDelta z1 z2 hΔ p.1 p.2)
              (hwnn p.1)
        _ = ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) *
            ((1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹) := by ring

end Work.FIArea2
