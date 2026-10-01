import Mathlib

namespace Work.LinnikAreas

/-- Splitting off the ratio in a staircase/layer-cake sum: with `d k = exp (-a (Λ + k)) - exp (-a (Λ + k + 1))`
the summand `d k * (D * lam₁ * exp (c * (Λ + k + 1)))` factors as
`D * lam₁ * exp c * (1 - exp (-a)) * exp ((c - a) * Λ) * (exp (c - a))^k`, so the whole (finite) sum is
that constant times the geometric partial sum. -/
lemma sum_staircase_factor (a c Λ D lam₁ : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1),
        (Real.exp (-a * (Λ + (k:ℝ))) - Real.exp (-a * (Λ + (k:ℝ) + 1)))
          * (D * lam₁ * Real.exp (c * (Λ + (k:ℝ) + 1))))
      = D * lam₁ * Real.exp c * (1 - Real.exp (-a)) * Real.exp ((c - a) * Λ)
          * ∑ k ∈ Finset.range (K + 1), (Real.exp (c - a)) ^ k := by
  have hterm : ∀ k : ℕ,
      (Real.exp (-a * (Λ + (k:ℝ))) - Real.exp (-a * (Λ + (k:ℝ) + 1)))
        * (D * lam₁ * Real.exp (c * (Λ + (k:ℝ) + 1)))
      = D * lam₁ * Real.exp c * (1 - Real.exp (-a)) * Real.exp ((c - a) * Λ) * (Real.exp (c - a))^k := by
    intro k
    have h1 : Real.exp (-a * (Λ + (k:ℝ) + 1)) = Real.exp (-a * (Λ + (k:ℝ))) * Real.exp (-a) := by
      rw [show -a * (Λ + (k:ℝ) + 1) = -a * (Λ + (k:ℝ)) + (-a) by ring, Real.exp_add]
    have h2 : Real.exp (c * (Λ + (k:ℝ) + 1)) = Real.exp (c * (Λ + (k:ℝ))) * Real.exp c := by
      rw [show c * (Λ + (k:ℝ) + 1) = c * (Λ + (k:ℝ)) + c by ring, Real.exp_add]
    calc
      (Real.exp (-a * (Λ + (k:ℝ))) - Real.exp (-a * (Λ + (k:ℝ) + 1)))
          * (D * lam₁ * Real.exp (c * (Λ + (k:ℝ) + 1)))
          = (Real.exp (-a * (Λ + (k:ℝ))) - Real.exp (-a * (Λ + (k:ℝ))) * Real.exp (-a))
              * (D * lam₁ * (Real.exp (c * (Λ + (k:ℝ))) * Real.exp c)) := by rw [h1, h2]
      _ = D * lam₁ * Real.exp c * (1 - Real.exp (-a))
            * (Real.exp (-a * (Λ + (k:ℝ))) * Real.exp (c * (Λ + (k:ℝ)))) := by ring
      _ = D * lam₁ * Real.exp c * (1 - Real.exp (-a)) * Real.exp ((c - a) * Λ + (c - a) * (k:ℝ)) := by
            rw [show Real.exp (-a * (Λ + (k:ℝ))) * Real.exp (c * (Λ + (k:ℝ)))
                  = Real.exp ((c - a) * Λ + (c - a) * (k:ℝ)) by
                  rw [← Real.exp_add]
                  rw [show -a * (Λ + (k:ℝ)) + c * (Λ + (k:ℝ)) = (c - a) * Λ + (c - a) * (k:ℝ) by ring]]
      _ = D * lam₁ * Real.exp c * (1 - Real.exp (-a))
            * (Real.exp ((c - a) * Λ) * Real.exp ((c - a) * (k:ℝ))) := by rw [Real.exp_add]
      _ = D * lam₁ * Real.exp c * (1 - Real.exp (-a)) * (Real.exp ((c - a) * Λ) * (Real.exp (c - a))^k) := by
            rw [show (c - a) * (k:ℝ) = (k:ℝ) * (c - a) by ring, Real.exp_nat_mul]
      _ = D * lam₁ * Real.exp c * (1 - Real.exp (-a)) * Real.exp ((c - a) * Λ) * (Real.exp (c - a))^k := by ring
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  exact hterm k

end Work.LinnikAreas
