import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.latTelescopeOne
import Submission.Work.BoseBogFS.latTelescopeSuccSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- One-dimensional profile sum, `(2,2)` case: the lattice-shell profile `24 j² + 2` against
`1 / ((1 + m j)² j²)`.  True value of the full series is `≤ 26 (1 + 1/m)`; `100` is generous.
Used to bound `Σ_n 1/((1+m‖n‖)² ‖n‖²)`. -/
theorem latSumOneDTwoSq (m : ℝ) (hm : 0 < m) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1),
        (24 * (j : ℝ) ^ 2 + 2) * (1 / ((1 + m * (j : ℝ)) ^ 2 * (j : ℝ) ^ 2)))
      ≤ 100 * (1 / m + 1) := by
  -- The `j = 0` summand is `0` by the junk-value convention `1/0 = 0`, so shift the index
  -- and split the profile: `(24k² + 2)/((1+mk)²k²) = 24/(1+mk)² + 2/((1+mk)²k²)`.
  rw [Finset.sum_range_succ']
  have h0 : (24 * ((0 : ℕ) : ℝ) ^ 2 + 2) * (1 / ((1 + m * ((0 : ℕ) : ℝ)) ^ 2 * ((0 : ℕ) : ℝ) ^ 2))
      = 0 := by
    norm_num
  rw [h0, add_zero]
  push_cast
  -- Termwise splitting with `(1 + m(k+1))² ≥ 1`.
  have hstep : (∑ x ∈ Finset.range J,
        (24 * ((x : ℝ) + 1) ^ 2 + 2) * (1 / ((1 + m * ((x : ℝ) + 1)) ^ 2 * ((x : ℝ) + 1) ^ 2)))
      ≤ (∑ x ∈ Finset.range J,
        (24 / (1 + m * ((x : ℝ) + 1)) ^ 2 + 2 / ((x : ℝ) + 1) ^ 2)) := by
    apply Finset.sum_le_sum
    intro x _
    have hx : (0 : ℝ) < (x : ℝ) + 1 := by positivity
    have hA : (1 : ℝ) ≤ (1 + m * ((x : ℝ) + 1)) ^ 2 := by
      have hmx : 0 < m * ((x : ℝ) + 1) := mul_pos hm hx
      nlinarith
    have heq : (24 * ((x : ℝ) + 1) ^ 2 + 2) * (1 / ((1 + m * ((x : ℝ) + 1)) ^ 2 * ((x : ℝ) + 1) ^ 2))
        = 24 / (1 + m * ((x : ℝ) + 1)) ^ 2
            + 2 / ((1 + m * ((x : ℝ) + 1)) ^ 2 * ((x : ℝ) + 1) ^ 2) := by
      have hAz : (1 + m * ((x : ℝ) + 1)) ^ 2 ≠ 0 := by positivity
      have huz : ((x : ℝ) + 1) ^ 2 ≠ 0 := by positivity
      field_simp
    rw [heq]
    have h2' : 2 / ((1 + m * ((x : ℝ) + 1)) ^ 2 * ((x : ℝ) + 1) ^ 2)
        ≤ 2 / ((x : ℝ) + 1) ^ 2 := by
      have hu : 0 < ((x : ℝ) + 1) ^ 2 := by positivity
      have hle : ((x : ℝ) + 1) ^ 2 ≤ (1 + m * ((x : ℝ) + 1)) ^ 2 * ((x : ℝ) + 1) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hA (le_of_lt hu)
        simpa using this
      calc 2 / ((1 + m * ((x : ℝ) + 1)) ^ 2 * ((x : ℝ) + 1) ^ 2)
          = 2 * (1 / ((1 + m * ((x : ℝ) + 1)) ^ 2 * ((x : ℝ) + 1) ^ 2)) := by ring
        _ ≤ 2 * (1 / ((x : ℝ) + 1) ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact one_div_le_one_div_of_le hu hle
        _ = 2 / ((x : ℝ) + 1) ^ 2 := by ring
    linarith
  -- The geometric part: `∑ 24/(1+m(k+1))² ≤ 24/m`.
  have hA : (∑ x ∈ Finset.range J, 24 / (1 + m * ((x : ℝ) + 1)) ^ 2) ≤ 24 / m := by
    have hcongr : (∑ x ∈ Finset.range J, 24 / (1 + m * ((x : ℝ) + 1)) ^ 2)
        = 24 * ∑ x ∈ Finset.range J, 1 / (1 + m * ((x : ℝ) + 1)) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hcongr]
    calc 24 * (∑ x ∈ Finset.range J, 1 / (1 + m * ((x : ℝ) + 1)) ^ 2) ≤ 24 * (1 / m) :=
          mul_le_mul_of_nonneg_left (latTelescopeOne m hm J) (by norm_num)
      _ = 24 / m := by ring
  -- The Basel part: `∑ 2/(k+1)² ≤ 2 * 2 = 4`.
  have hB : (∑ x ∈ Finset.range J, 2 / ((x : ℝ) + 1) ^ 2) ≤ 4 := by
    have hcongr : (∑ x ∈ Finset.range J, 2 / ((x : ℝ) + 1) ^ 2)
        = 2 * ∑ x ∈ Finset.range J, 1 / ((x : ℝ) + 1) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hcongr]
    calc 2 * (∑ x ∈ Finset.range J, 1 / ((x : ℝ) + 1) ^ 2) ≤ 2 * 2 :=
          mul_le_mul_of_nonneg_left (latTelescopeSuccSq J) (by norm_num)
      _ = 4 := by norm_num
  rw [Finset.sum_add_distrib] at hstep
  have hfin : 24 / m + 4 ≤ 100 * (1 / m + 1) := by
    have h100 : (100 : ℝ) * (1 / m + 1) = 100 / m + 100 := by ring
    rw [h100]
    have h24 : (24 : ℝ) / m ≤ 100 / m := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hm)
      norm_num
    linarith
  linarith

end Work.BoseBogFS
