import Mathlib

namespace Work.LinnikAreas

/-- For every real `θ` and natural `n`,
`(∑_{m<n} cos mθ) cos nθ + (∑_{m<n} sin mθ) sin nθ = ∑_{m<n} cos (m+1)θ`. -/
theorem cosSinMulSum (θ : ℝ) (n : ℕ) :
    (∑ m ∈ Finset.range n, Real.cos ((m : ℝ) * θ)) * Real.cos ((n : ℝ) * θ)
      + (∑ m ∈ Finset.range n, Real.sin ((m : ℝ) * θ)) * Real.sin ((n : ℝ) * θ)
    = ∑ m ∈ Finset.range n, Real.cos (((m + 1 : ℕ) : ℝ) * θ) := by
  -- Termwise, `cos mθ cos nθ + sin mθ sin nθ = cos ((n-m)θ)`.
  have hterm : ∀ m ∈ Finset.range n,
      Real.cos ((m : ℝ) * θ) * Real.cos ((n : ℝ) * θ)
        + Real.sin ((m : ℝ) * θ) * Real.sin ((n : ℝ) * θ)
      = Real.cos (((n - m : ℕ) : ℝ) * θ) := by
    intro m hm
    have hmn : m ≤ n := le_of_lt (Finset.mem_range.mp hm)
    have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := Nat.cast_sub hmn
    rw [hcast]
    have h2 : ((n : ℝ) - (m : ℝ)) * θ = (n : ℝ) * θ - (m : ℝ) * θ := by ring
    rw [h2, Real.cos_sub]
    ring
  -- Pull the outer factors inside the sums and combine.
  have hsum : (∑ m ∈ Finset.range n, Real.cos ((m : ℝ) * θ)) * Real.cos ((n : ℝ) * θ)
      + (∑ m ∈ Finset.range n, Real.sin ((m : ℝ) * θ)) * Real.sin ((n : ℝ) * θ)
      = ∑ m ∈ Finset.range n, Real.cos (((n - m : ℕ) : ℝ) * θ) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  -- Reindex `cos ((n-m)θ)` as `cos ((m+1)θ)`.
  have hreindex : (∑ m ∈ Finset.range n, Real.cos (((n - m : ℕ) : ℝ) * θ))
      = ∑ m ∈ Finset.range n, Real.cos (((m + 1 : ℕ) : ℝ) * θ) := by
    have h := Finset.sum_range_reflect (fun k => Real.cos (((k + 1 : ℕ) : ℝ) * θ)) n
    rw [← h]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' : m < n := Finset.mem_range.mp hm
    have h3 : n - 1 - m + 1 = n - m := by omega
    rw [h3]
  rw [hsum, hreindex]

end Work.LinnikAreas
