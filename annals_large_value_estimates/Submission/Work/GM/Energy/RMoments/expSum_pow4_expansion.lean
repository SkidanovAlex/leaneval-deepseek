import Mathlib
import Submission.Work.GM.Energy.RMoments.FejerDefs

namespace Work.GM.Energy.RMoments

/-- Expansion of the fourth power of the exponential sum `expSum W u = Σ_{t∈W} e^{itu}` as a
quadruple sum over the sum-difference `sumdiff q = q₁ + q₂ - q₃ - q₄`. -/
theorem expSum_pow4_expansion (W : Finset ℝ) (u : ℝ) :
    ((‖expSum W u‖ ^ 4 : ℝ) : ℂ)
      = ∑ q ∈ (W ×ˢ W ×ˢ W ×ˢ W : Finset (ℝ × ℝ × ℝ × ℝ)),
          Complex.exp (Complex.I * ((sumdiff q * u : ℝ) : ℂ)) := by
  -- `‖z‖⁴ = z² · (conj z)²` for a complex number `z`.
  have hnorm : ((‖expSum W u‖ ^ 4 : ℝ) : ℂ)
      = (expSum W u) ^ 2 * ((starRingEnd ℂ) (expSum W u)) ^ 2 := by
    have h : ((Complex.normSq (expSum W u)) ^ 2 : ℝ) = ‖expSum W u‖ ^ 4 := by
      rw [Complex.normSq_eq_norm_sq]; ring
    rw [← h, Complex.ofReal_pow, ← Complex.mul_conj (expSum W u), mul_pow]
  -- `Σ_{a,b} e^{i(a+b)u} = (Σ_t e^{itu})²`
  have hF : (∑ a ∈ W, ∑ b ∈ W, Complex.exp (Complex.I * (((a + b) * u : ℝ) : ℂ)))
      = (expSum W u) ^ 2 := by
    rw [show expSum W u = ∑ a ∈ W, Complex.exp (Complex.I * ((a * u : ℝ) : ℂ)) from rfl]
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- `Σ_{c,d} e^{-i(c+d)u} = (conj Σ_t e^{itu})²`
  have hG : (∑ c ∈ W, ∑ d ∈ W, Complex.exp (-(Complex.I * (((c + d) * u : ℝ) : ℂ))))
      = ((starRingEnd ℂ) (expSum W u)) ^ 2 := by
    have hconj : (starRingEnd ℂ) (expSum W u)
        = ∑ c ∈ W, (starRingEnd ℂ) (Complex.exp (Complex.I * ((c * u : ℝ) : ℂ))) := by
      rw [show expSum W u = ∑ c ∈ W, Complex.exp (Complex.I * ((c * u : ℝ) : ℂ)) from rfl]
      exact map_sum _ _ _
    rw [hconj, pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  -- the quadruple sum of the products factors as the product of the double sums
  have hfac : (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ∑ d ∈ W,
        Complex.exp (Complex.I * (((a + b) * u : ℝ) : ℂ))
          * Complex.exp (-(Complex.I * (((c + d) * u : ℝ) : ℂ))))
      = (∑ a ∈ W, ∑ b ∈ W, Complex.exp (Complex.I * (((a + b) * u : ℝ) : ℂ)))
        * (∑ c ∈ W, ∑ d ∈ W, Complex.exp (-(Complex.I * (((c + d) * u : ℝ) : ℂ)))) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mul_sum]
  -- each exponential factorises
  have hterm : ∀ a b c d : ℝ,
      Complex.exp (Complex.I * (((a + b - c - d) * u : ℝ) : ℂ))
        = Complex.exp (Complex.I * (((a + b) * u : ℝ) : ℂ))
          * Complex.exp (-(Complex.I * (((c + d) * u : ℝ) : ℂ))) := by
    intro a b c d
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- rewrite the sum over the product `W ×ˢ W ×ˢ W ×ˢ W` as four nested sums
  have hRHS : (∑ q ∈ (W ×ˢ W ×ˢ W ×ˢ W : Finset (ℝ × ℝ × ℝ × ℝ)),
        Complex.exp (Complex.I * ((sumdiff q * u : ℝ) : ℂ)))
      = ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ∑ d ∈ W,
          Complex.exp (Complex.I * (((a + b - c - d) * u : ℝ) : ℂ)) := by
    simp [Finset.sum_product, sumdiff]
  rw [hnorm, ← hF, ← hG, ← hfac, hRHS]
  refine Finset.sum_congr rfl fun a ha => ?_
  refine Finset.sum_congr rfl fun b hb => ?_
  refine Finset.sum_congr rfl fun c hc => ?_
  refine Finset.sum_congr rfl fun d hd => ?_
  exact (hterm a b c d).symm

end Work.GM.Energy.RMoments
