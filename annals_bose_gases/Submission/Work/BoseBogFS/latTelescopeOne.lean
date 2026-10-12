import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- Geometric (telescoping) bound: `∑_{k=1}^{J} 1/(1+m k)² ≤ 1/m` for `m > 0`.

Each summand is dominated by the telescoping difference
`(1/m)(1/(1+m(k-1)) − 1/(1+mk))`, whose sum over `k = 1,…,J` collapses to
`(1/m)(1 − 1/(1+mJ)) ≤ 1/m`. -/
theorem latTelescopeOne (m : ℝ) (hm : 0 < m) (J : ℕ) :
    (∑ j ∈ Finset.range J, 1 / (1 + m * ((j : ℝ) + 1)) ^ 2) ≤ 1 / m := by
  have step : ∀ j : ℕ,
      1 / (1 + m * ((j : ℝ) + 1)) ^ 2
        ≤ (1 / m) * (1 / (1 + m * (j : ℝ)) - 1 / (1 + m * ((j : ℝ) + 1))) := by
    intro j
    have hb : (0:ℝ) < 1 + m * (j:ℝ) := by positivity
    have hb2 : (0:ℝ) < 1 + m * ((j:ℝ) + 1) := by positivity
    have hkey : (1/m) * (1/(1 + m*(j:ℝ)) - 1/(1 + m*((j:ℝ)+1)))
        = 1 / ((1 + m*(j:ℝ)) * (1 + m*((j:ℝ)+1))) := by
      field_simp
      ring
    rw [hkey]
    apply one_div_le_one_div_of_le
    · positivity
    · have hm' : (0:ℝ) ≤ m := le_of_lt hm
      have hj' : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have h1 : 1 + m * (j:ℝ) ≤ 1 + m * ((j:ℝ) + 1) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hb2)]
  have htel : (∑ j ∈ Finset.range J, (1 / (1 + m*(j:ℝ)) - 1 / (1 + m*((j:ℝ)+1))))
      = 1 - 1 / (1 + m*(J:ℝ)) := by
    have h := Finset.sum_range_sub' (fun j : ℕ => 1/(1 + m*(j:ℝ))) J
    simpa [Nat.cast_add, Nat.cast_one] using h
  calc
    ∑ j ∈ Finset.range J, 1 / (1 + m * ((j : ℝ) + 1)) ^ 2
        ≤ ∑ j ∈ Finset.range J, (1/m) * (1 / (1 + m*(j:ℝ)) - 1 / (1 + m*((j:ℝ)+1))) :=
          Finset.sum_le_sum (fun j _ => step j)
    _ = (1/m) * ∑ j ∈ Finset.range J, (1 / (1 + m*(j:ℝ)) - 1 / (1 + m*((j:ℝ)+1))) := by
          rw [Finset.mul_sum]
    _ = (1/m) * (1 - 1 / (1 + m*(J:ℝ))) := by rw [htel]
    _ ≤ (1/m) * 1 := by
          have hJ : (0:ℝ) ≤ 1 / (1 + m*(J:ℝ)) := by positivity
          have hm1 : (0:ℝ) ≤ 1/m := by positivity
          nlinarith
    _ = 1/m := by ring

end Work.BoseBogFS
