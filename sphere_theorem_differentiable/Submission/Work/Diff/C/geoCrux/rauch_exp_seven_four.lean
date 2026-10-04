import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux

theorem rauch_exp_seven_four : Real.exp (7 / 4) ≤ 7 := by
  -- Bound `exp (1/4)` by a finite Taylor sum: `exp x ≤ ∑_{m<n} x^m/m! + x^n (n+1)/(n! n)`.
  have key : Real.exp (1 / 4) ≤ 83 / 64 := by
    have h := Real.exp_bound' (x := 1 / 4) (by norm_num) (by norm_num) (n := 2) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hpow : Real.exp (1 / 4) ^ 7 ≤ (83 / 64 : ℝ) ^ 7 :=
    pow_le_pow_left₀ (Real.exp_pos _).le key 7
  have heq : Real.exp (7 / 4) = Real.exp (1 / 4) ^ 7 := by
    rw [show (7 : ℝ) / 4 = (7 : ℕ) * (1 / 4) by norm_num, Real.exp_nat_mul]
  rw [heq]
  linarith [hpow, show (83 / 64 : ℝ) ^ 7 ≤ 7 by norm_num]

end Work.Diff.C.geoCrux
