import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- Pointwise telescoping estimate for the `(3,4)` profile sum.

For `m > 0` and `u ≥ 1`,
`(24 u² + 2) · 1/((1 + m u)³ u⁴) ≤ 52/u − 52/(u+1)`.

Indeed `(1 + m u)³ ≥ 1 > 0`, so the term is at most `(24u² + 2)/u⁴ ≤ 26/u²`
(using `u² ≥ 1`), and `26/u² ≤ 52/(u(u+1)) = 52/u − 52/(u+1)` because `u ≤ u²`. -/
private lemma term_le_gen (m : ℝ) (hm : 0 < m) {u : ℝ} (hu : 1 ≤ u) :
    (24 * u ^ 2 + 2) * (1 / ((1 + m * u) ^ 3 * u ^ 4))
      ≤ 52 / u - 52 / (u + 1) := by
  have hupos : 0 < u := by linarith
  have hu2 : (1 : ℝ) ≤ u ^ 2 := one_le_pow₀ hu
  have hmu : 0 ≤ m * u := mul_nonneg hm.le hupos.le
  have h1 : (1 : ℝ) ≤ 1 + m * u := by linarith
  have hcube : (1 : ℝ) ≤ (1 + m * u) ^ 3 := one_le_pow₀ h1
  have hden : u ^ 4 ≤ (1 + m * u) ^ 3 * u ^ 4 := by
    have := mul_le_mul_of_nonneg_right hcube (show (0 : ℝ) ≤ u ^ 4 by positivity)
    simpa using this
  have hstep1 : 1 / ((1 + m * u) ^ 3 * u ^ 4) ≤ 1 / u ^ 4 :=
    one_div_le_one_div_of_le (by positivity) hden
  have hstep2 : (24 * u ^ 2 + 2) * (1 / ((1 + m * u) ^ 3 * u ^ 4))
      ≤ (24 * u ^ 2 + 2) * (1 / u ^ 4) :=
    mul_le_mul_of_nonneg_left hstep1 (by positivity)
  have hstep3 : (24 * u ^ 2 + 2) * (1 / u ^ 4) ≤ 26 / u ^ 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg u) (by linarith : (0 : ℝ) ≤ u ^ 2 - 1)]
  have hstep4 : 26 / u ^ 2 ≤ 52 / u - 52 / (u + 1) := by
    have hup1 : u + 1 ≠ 0 := by positivity
    have heq : 52 / u - 52 / (u + 1) = 52 / (u * (u + 1)) := by
      rw [div_sub_div (52 : ℝ) (52 : ℝ) hupos.ne' hup1]
      ring
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hupos.le (by linarith : (0 : ℝ) ≤ u - 1)]
  linarith

/-- One-dimensional profile sum, `(3,4)` case: the lattice-shell profile `24 j² + 2` against
`1 / ((1 + m j)³ j⁴)`.  True value of the full series is `≤ 52`; `100` is generous.
Used to bound `Σ_n 1/((1+m‖n‖)³ ‖n‖⁴)`. -/
theorem latSumOneDThreeFour (m : ℝ) (hm : 0 < m) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1),
        (24 * (j : ℝ) ^ 2 + 2) * (1 / ((1 + m * (j : ℝ)) ^ 3 * (j : ℝ) ^ 4)))
      ≤ 100 := by
  -- split off the `j = 0` term (which is `0` by the `1/0 = 0` convention) and reindex
  rw [Finset.sum_range_succ']
  have h0 : (24 * ((0 : ℕ) : ℝ) ^ 2 + 2) *
      (1 / ((1 + m * ((0 : ℕ) : ℝ)) ^ 3 * ((0 : ℕ) : ℝ) ^ 4)) = 0 := by norm_num
  rw [h0, add_zero]
  -- the remaining sum telescopes against `52/u − 52/(u+1)`
  calc (∑ k ∈ Finset.range J,
        (24 * ((k + 1 : ℕ) : ℝ) ^ 2 + 2) *
          (1 / ((1 + m * ((k + 1 : ℕ) : ℝ)) ^ 3 * ((k + 1 : ℕ) : ℝ) ^ 4)))
      ≤ ∑ k ∈ Finset.range J, (52 / ((k : ℝ) + 1) - 52 / (((k + 1 : ℕ) : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro k _
        push_cast
        exact term_le_gen m hm (by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
    _ = 52 / ((0 : ℕ) + 1 : ℝ) - 52 / ((J : ℕ) + 1 : ℝ) := by
        rw [Finset.sum_range_sub' (fun t : ℕ => 52 / ((t : ℝ) + 1)) J]
    _ ≤ 100 := by
        have h0' : 52 / ((0 : ℕ) + 1 : ℝ) = 52 := by norm_num
        rw [h0']
        have hJ : (0 : ℝ) ≤ 52 / ((J : ℕ) + 1 : ℝ) :=
          div_nonneg (by norm_num) (by positivity)
        linarith

end Work.BoseBogFS
