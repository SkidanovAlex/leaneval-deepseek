import Mathlib

namespace Work.ZeroDensity

/-- Factoring a constant out of a double sum of a product:
`∑ᵢ ∑ⱼ c * (Aᵢ * Bⱼ) = c * ((∑ᵢ Aᵢ) * (∑ⱼ Bⱼ))`. -/
private lemma sum_sum_const_mul {ι κ : Type*} (c : ℂ) (A : ι → ℂ) (B : κ → ℂ)
    (s : Finset ι) (t : Finset κ) :
    (∑ i ∈ s, ∑ j ∈ t, c * (A i * B j)) = c * ((∑ i ∈ s, A i) * (∑ j ∈ t, B j)) := by
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]

/-- The Gram double sum of the pole terms factorises as the squared modulus of the
exponential sum: `∑ᵢ ∑ⱼ zᵢ conj(zⱼ) (g y^{1-ρᵢ} conj(y^{1-ρⱼ}) / y)
= g (∑ᵢ zᵢ y^{1-ρᵢ}) conj(∑ᵢ zᵢ y^{1-ρᵢ}) / y`. -/
lemma HB7PoleGramDoubleSum (m : ℕ) (ρ : Fin m → ℂ) (z : Fin m → ℂ) (g y : ℝ) :
    (∑ i, ∑ j, z i * (starRingEnd ℂ) (z j)
        * ((g : ℂ) * (y : ℂ) ^ (1 - ρ i) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - ρ j)) / (y : ℂ)))
      = (g : ℂ) * (∑ i, z i * (y : ℂ) ^ (1 - ρ i))
          * (starRingEnd ℂ) (∑ i, z i * (y : ℂ) ^ (1 - ρ i)) / (y : ℂ) := by
  -- Expand the conjugate of the exponential sum using multiplicativity of `conj`.
  have h1 : (starRingEnd ℂ) (∑ i, z i * (y : ℂ) ^ (1 - ρ i))
      = ∑ i, (starRingEnd ℂ) (z i) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - ρ i)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_mul _ _ _
  rw [h1]
  -- Put every inner summand into the shape `c * (A i * B j)`.
  have key : ∀ i j, z i * (starRingEnd ℂ) (z j)
        * ((g : ℂ) * (y : ℂ) ^ (1 - ρ i) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - ρ j)) / (y : ℂ))
      = ((g : ℂ) / (y : ℂ))
          * ((z i * (y : ℂ) ^ (1 - ρ i))
              * ((starRingEnd ℂ) (z j) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - ρ j)))) := by
    intro i j; ring
  simp only [key]
  -- Factor the constant out of the double sum and use multiplicativity of the sums.
  trans ((g : ℂ) / (y : ℂ))
      * ((∑ i, z i * (y : ℂ) ^ (1 - ρ i))
          * (∑ j, (starRingEnd ℂ) (z j) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - ρ j))))
  · exact sum_sum_const_mul _ _ _ _ _
  · ring

end Work.ZeroDensity
