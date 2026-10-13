import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- Second-order weighted sum estimate: the double sum of the squares of
`b j * u i * w * s^{-γ/2}` over the admissible pairs `(i,j)` (namely `1 ≤ i` and
`i + j ≤ k`) is bounded by `w² (∑ C i) (∑ b j²)`, given the pointwise bound
`u i² s^{-γ} ≤ C i` for `i ≤ k` and the nonnegativity of `s` and `C`. -/
theorem sum_sq_second_le (k : ℕ) (b C u : ℕ → ℝ) (w s γ : ℝ)
    (hs0 : 0 ≤ s) (hC : ∀ i, 0 ≤ C i)
    (hu : ∀ i ≤ k, (u i) ^ 2 * s ^ (-γ) ≤ C i) :
    (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (b j * u i * (w * s ^ (-(γ / 2)))) ^ 2 else 0)
      ≤ w ^ 2 * (∑ i ∈ Finset.range (k + 1), C i) * ∑ j ∈ Finset.range (k + 1), (b j) ^ 2 := by
  -- the real-power bookkeeping: `(s^{-γ/2})² = s^{-γ}` for `s ≥ 0`
  have hsq : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
    rw [← Real.rpow_mul_natCast hs0 (-(γ / 2)) 2]
    have h2 : (-(γ / 2)) * ((2 : ℕ) : ℝ) = -γ := by push_cast; ring
    rw [h2]
  -- pointwise bound for a single term
  have hpoint : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (b j * u i * (w * s ^ (-(γ / 2)))) ^ 2 else 0)
        ≤ w ^ 2 * C i * (b j) ^ 2 := by
    intro i hi j hj
    rw [Finset.mem_range] at hi hj
    split_ifs with hc
    · obtain ⟨_, hij⟩ := hc
      have hik : i ≤ k := by omega
      have hkey : (b j * u i * (w * s ^ (-(γ / 2)))) ^ 2
          = w ^ 2 * (b j) ^ 2 * ((u i) ^ 2 * s ^ (-γ)) := by
        simp only [mul_pow]
        rw [hsq]
        ring
      rw [hkey]
      calc w ^ 2 * (b j) ^ 2 * ((u i) ^ 2 * s ^ (-γ))
          ≤ w ^ 2 * (b j) ^ 2 * C i :=
            mul_le_mul_of_nonneg_left (hu i hik)
              (mul_nonneg (sq_nonneg w) (sq_nonneg (b j)))
        _ = w ^ 2 * C i * (b j) ^ 2 := by ring
    · exact mul_nonneg (mul_nonneg (sq_nonneg w) (hC i)) (sq_nonneg (b j))
  calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then (b j * u i * (w * s ^ (-(γ / 2)))) ^ 2 else 0)
      ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), w ^ 2 * C i * (b j) ^ 2 :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpoint i hi j hj))
    _ = (∑ i ∈ Finset.range (k + 1), w ^ 2 * C i) * (∑ j ∈ Finset.range (k + 1), (b j) ^ 2) :=
        (Finset.sum_mul_sum _ _ (fun i => w ^ 2 * C i) (fun j => (b j) ^ 2)).symm
    _ = w ^ 2 * (∑ i ∈ Finset.range (k + 1), C i) * ∑ j ∈ Finset.range (k + 1), (b j) ^ 2 := by
        have h : (∑ i ∈ Finset.range (k + 1), w ^ 2 * C i)
            = w ^ 2 * ∑ i ∈ Finset.range (k + 1), C i := by
          rw [Finset.mul_sum]
        rw [h]

end Work.FTS.EllipticEst
