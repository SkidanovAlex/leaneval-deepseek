import Mathlib

namespace Work.FIArea4.Vflip.Vfd

/-- Arithmetic–geometric mean inequality for a symmetric double sum:
for nonnegative weights `N` (with `N p q = N q p`) the double sum
`∑ p ∑ q a p a q N p q` is bounded by the diagonal-weighted sum
`∑ p a p ^ 2 (∑ q N p q)`.

The proof doubles both sides, uses the pointwise bound `2 a p a q ≤ a p ^ 2 + a q ^ 2`
and pairs the two symmetric halves of the resulting double sum by symmetry of `N`. -/
theorem amgm_double_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (N : ι → ι → ℝ)
    (hN : ∀ x y, N x y = N y x) (ha : ∀ x, 0 ≤ a x) (hNnn : ∀ x y, 0 ≤ N x y) :
    ∑ p ∈ s, ∑ q ∈ s, a p * a q * N p q ≤ ∑ p ∈ s, a p ^ 2 * (∑ q ∈ s, N p q) := by
  -- pointwise AM–GM bound, multiplied by the nonnegative weight `N p q`
  have hterm : ∀ p ∈ s, ∀ q ∈ s, 2 * (a p * a q * N p q) ≤ ((a p) ^ 2 + (a q) ^ 2) * N p q := by
    intro p hp q hq
    have h1 : 2 * (a p * a q) ≤ (a p) ^ 2 + (a q) ^ 2 := by
      nlinarith [sq_nonneg (a p - a q)]
    calc 2 * (a p * a q * N p q) = (2 * (a p * a q)) * N p q := by ring
      _ ≤ ((a p) ^ 2 + (a q) ^ 2) * N p q := mul_le_mul_of_nonneg_right h1 (hNnn p q)
  -- pull the factor `2` inside the double sum
  have e1 : (∑ p ∈ s, ∑ q ∈ s, 2 * (a p * a q * N p q))
      = 2 * (∑ p ∈ s, ∑ q ∈ s, a p * a q * N p q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
  -- the `p`-half of the symmetrised right hand side
  have hA : (∑ p ∈ s, ∑ q ∈ s, (a p) ^ 2 * N p q)
      = ∑ p ∈ s, a p ^ 2 * (∑ q ∈ s, N p q) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
  -- the `q`-half, which equals the same thing by symmetry of `N`
  have hB : (∑ p ∈ s, ∑ q ∈ s, (a q) ^ 2 * N p q)
      = ∑ p ∈ s, a p ^ 2 * (∑ q ∈ s, N p q) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    have hh : (∑ p ∈ s, (a q) ^ 2 * N p q) = ∑ p ∈ s, (a q) ^ 2 * N q p :=
      Finset.sum_congr rfl (fun p hp => by rw [hN p q])
    rw [hh, Finset.mul_sum]
  have hsplit : (∑ p ∈ s, ∑ q ∈ s, ((a p) ^ 2 + (a q) ^ 2) * N p q)
      = (∑ p ∈ s, ∑ q ∈ s, (a p) ^ 2 * N p q)
        + (∑ p ∈ s, ∑ q ∈ s, (a q) ^ 2 * N p q) := by
    simp only [add_mul, Finset.sum_add_distrib]
  -- the symmetrised right hand side is exactly twice the diagonal sum
  have e2 : (∑ p ∈ s, ∑ q ∈ s, ((a p) ^ 2 + (a q) ^ 2) * N p q)
      = 2 * (∑ p ∈ s, a p ^ 2 * (∑ q ∈ s, N p q)) := by
    rw [hsplit, hA, hB]
    ring
  have hsum := Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => hterm p hp q hq))
  rw [e1, e2] at hsum
  linarith

end Work.FIArea4.Vflip.Vfd
