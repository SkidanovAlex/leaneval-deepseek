import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- **Power mean / Hölder for a finite sum of complex numbers**: for `p ≥ 1`, `q ≥ 1`,
`‖∑_{i<p} z_i‖^q ≤ p^{q-1} · ∑_{i<p} ‖z_i‖^q`.

Proof: `‖Σ z_i‖ ≤ Σ ‖z_i‖` (triangle inequality), then the power-mean inequality
`(Σ_{i<p} a_i)^q ≤ p^{q-1} Σ_{i<p} a_i^q` for nonnegative reals `a_i` (Hölder, or convexity of
`t^q`).  Mathlib has finite-sum Hölder (`Real.inner_le_Lp_mul_Lq`) for the exponents `p/(p-1)` and
`p`. -/
theorem norm_sum_pow_le (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (z : Fin p → ℂ) :
    ‖∑ i, z i‖ ^ q ≤ (p : ℝ) ^ (q - 1) * ∑ i, ‖z i‖ ^ q := by
  -- `hp` is not needed: the inequality also holds for the empty sum (p = 0)
  have _hp := hp
  -- Triangle inequality: `‖Σ z_i‖ ≤ Σ ‖z_i‖`.
  have hle : ‖∑ i, z i‖ ≤ ∑ i, ‖z i‖ := by
    simpa using norm_sum_le (Finset.univ : Finset (Fin p)) z
  -- `(Finset.univ : Finset (Fin p)).card = p`.
  have hScard : ((Finset.univ : Finset (Fin p)).card : ℝ) = (p : ℝ) := by simp
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  -- `(q : ℝ) - 1 = ((q - 1 : ℕ) : ℝ)` since `1 ≤ q`.
  have hqq : ((q : ℝ) - 1) = ((q - 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub hq]
  -- Power-mean inequality for nonnegative reals (Hölder with exponents `q` and `q/(q-1)`).
  have key := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.univ : Finset (Fin p))
      (f := fun i : Fin p => ‖z i‖) hqR (by intro i _; positivity)
  calc ‖∑ i, z i‖ ^ q
      ≤ (∑ i, ‖z i‖) ^ q := pow_le_pow_left₀ (norm_nonneg _) hle q
    _ = (∑ i, ‖z i‖) ^ (q : ℝ) := (Real.rpow_natCast _ q).symm
    _ ≤ ((Finset.univ : Finset (Fin p)).card : ℝ) ^ ((q : ℝ) - 1) *
          ∑ i : Fin p, ‖z i‖ ^ (q : ℝ) := by simpa using key
    _ = (p : ℝ) ^ (q - 1) * ∑ i : Fin p, ‖z i‖ ^ q := by
        rw [hScard, hqq]
        simp only [Real.rpow_natCast]

end Work.BMF.recursion
