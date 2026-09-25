import Mathlib

namespace NK.Reconstruct

/-- The set of `ℓ`-primary torsion elements of a commutative group is closed
under multiplication: if `x ^ (ℓ ^ n) = 1` and `y ^ (ℓ ^ m) = 1`, then
`(x * y) ^ (ℓ ^ (n + m)) = 1`. -/
theorem ellPrimary_mul_mem {A : Type*} [CommGroup A] (ℓ : ℕ) {x y : A}
    (hx : ∃ n : ℕ, x ^ (ℓ ^ n) = 1) (hy : ∃ n : ℕ, y ^ (ℓ ^ n) = 1) :
    ∃ n : ℕ, (x * y) ^ (ℓ ^ n) = 1 := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  refine ⟨n + m, ?_⟩
  have hx' : x ^ (ℓ ^ (n + m)) = 1 := by
    rw [pow_add, pow_mul, hn, one_pow]
  have hy' : y ^ (ℓ ^ (n + m)) = 1 := by
    rw [pow_add, mul_comm (ℓ ^ n) (ℓ ^ m), pow_mul, hm, one_pow]
  rw [mul_pow, hx', hy', one_mul]

end NK.Reconstruct
