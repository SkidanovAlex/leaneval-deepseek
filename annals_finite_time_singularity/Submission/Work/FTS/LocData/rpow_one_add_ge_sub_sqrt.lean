import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- For `x ∈ [0,1]` and `0 < α ≤ 1` the real power `x ^ (1 + α/3)` dominates the
expression `x - √x/5`.  Since `1 + α/3 ≤ 4/3` and `x ≤ 1` one has
`x ^ (1 + α/3) ≥ x ^ (4/3)`, and `x ^ (4/3) ≥ x - √x/5` because writing `x = v ^ 6`
the second inequality becomes `v ^ 3 * (1 - v ^ 2) ≤ 1/5` for `v ∈ [0,1]`
(the maximum of `v^3(1-v^2)` is `6√3/(25√5) ≈ 0.1859`). -/
theorem rpow_one_add_ge_sub_sqrt (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) : x - Real.sqrt x / 5 ≤ x ^ (1 + α / 3) := by
  -- ### Step 1: the elementary `rpow`-free core `v³(1-v)² ≤ 1/25` on `[0,1]`.
  --
  -- Both factors are bounded separately: `v(1-v) ≤ 1/4` (from `(v-1/2)² ≥ 0`) and
  -- `v²(1-v) ≤ 4/27` (from `4/27 - v² + v³ = (v-2/3)²(v+1/3) ≥ 0`), and
  -- `v³(1-v)² = v(1-v) · v²(1-v)`, so the product is `≤ (1/4)(4/27) = 1/27 ≤ 1/25`.
  have core_poly : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → v ^ 3 * (1 - v) ^ 2 ≤ 1 / 25 := by
    intro v hv0 hv1
    have h1 : v * (1 - v) ≤ 1 / 4 := by nlinarith [sq_nonneg (v - 1 / 2)]
    have h2 : v ^ 2 * (1 - v) ≤ 4 / 27 := by
      have h : 0 ≤ (v - 2 / 3) ^ 2 * (v + 1 / 3) := mul_nonneg (sq_nonneg _) (by linarith)
      nlinarith [h]
    have h4 : 0 ≤ v ^ 2 * (1 - v) := mul_nonneg (sq_nonneg v) (by linarith)
    have key : v ^ 3 * (1 - v) ^ 2 = (v * (1 - v)) * (v ^ 2 * (1 - v)) := by ring
    rw [key]
    calc (v * (1 - v)) * (v ^ 2 * (1 - v)) ≤ (1 / 4) * (4 / 27) :=
          mul_le_mul h1 h2 h4 (by norm_num)
      _ = 1 / 27 := by norm_num
      _ ≤ 1 / 25 := by norm_num
  -- ### Step 2: `v³(1-v²) ≤ 1/5` on `[0,1]`, the form produced by `x = v⁶`.
  --
  -- Substitute `w = v²` in Step 1: `(v³(1-v²))² = w³(1-w)² ≤ 1/25`; the left side is
  -- nonnegative, so `v³(1-v²) ≤ 1/5`.
  have core_cube : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → y ^ 3 * (1 - y ^ 2) ≤ 1 / 5 := by
    intro y hy0 hy1
    have h := core_poly (y ^ 2) (sq_nonneg y) (by nlinarith)
    have h2 : (y ^ 3 * (1 - y ^ 2)) ^ 2 ≤ 1 / 25 := by
      have hsq : (y ^ 3 * (1 - y ^ 2)) ^ 2 = (y ^ 2) ^ 3 * (1 - y ^ 2) ^ 2 := by ring
      rw [hsq]; exact h
    nlinarith [h2, sq_nonneg (y ^ 3 * (1 - y ^ 2) - 1 / 5)]
  -- ### Step 3: `x - √x/5 ≤ x^(4/3)` on `[0,1]`, via the substitution `x = y⁶`.
  have h43 : x - Real.sqrt x / 5 ≤ x ^ (4 / 3 : ℝ) := by
    set y := x ^ (1 / 6 : ℝ) with hy
    have hy0 : 0 ≤ y := Real.rpow_nonneg hx0 _
    have hy1 : y ≤ 1 := Real.rpow_le_one hx0 hx1 (by norm_num)
    -- the three `rpow` identities yielded by `x = y⁶`
    have hx_eq : x = y ^ 6 := by
      rw [hy, show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
      exact (Real.rpow_inv_natCast_pow hx0 (n := 6) (by norm_num)).symm
    have hsqrt : Real.sqrt x = y ^ 3 := by
      rw [Real.sqrt_eq_rpow, hy]
      rw [show (1 / 2 : ℝ) = (1 / 6 : ℝ) * ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_mul_natCast hx0]
    have hpow : x ^ (4 / 3 : ℝ) = y ^ 8 := by
      rw [hy, show (4 / 3 : ℝ) = (1 / 6 : ℝ) * ((8 : ℕ) : ℝ) by norm_num,
        Real.rpow_mul_natCast hx0]
    -- `y⁶ - y³/5 ≤ y⁸` is `y³ · (y³(1-y²)) ≤ y³ · (1/5)`
    have hcore := core_cube y hy0 hy1
    have h3 : (0 : ℝ) ≤ y ^ 3 := pow_nonneg hy0 3
    have hmul : y ^ 3 * (y ^ 3 * (1 - y ^ 2)) ≤ y ^ 3 * (1 / 5) :=
      mul_le_mul_of_nonneg_left hcore h3
    have key : y ^ 6 - y ^ 3 / 5 ≤ y ^ 8 := by nlinarith [hmul]
    rw [hpow, hsqrt, hx_eq]
    exact key
  -- ### Step 4: exponent monotonicity for base `x ∈ [0,1]`.
  have hmono : x ^ (4 / 3 : ℝ) ≤ x ^ (1 + α / 3) :=
    Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 (by linarith) (by linarith)
  linarith

end Work.FTS.LocData
