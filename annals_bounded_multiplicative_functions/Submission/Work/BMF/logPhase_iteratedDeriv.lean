import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open scoped Nat

/-- The `k`-th iterated derivative of `Real.log` (for `k ≥ 1`) is
`(-1)^{k-1} (k-1)! / y^k`. -/
lemma iteratedDeriv_log (k : ℕ) (hk : 1 ≤ k) (y : ℝ) :
    iteratedDeriv k Real.log y = (-1 : ℝ) ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) / y ^ k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [iteratedDeriv_eq_iterate, Function.iterate_succ_apply, Real.deriv_log', iter_deriv_inv]
  have hz : y ^ ((-1 : ℤ) - (k' : ℤ)) = 1 / y ^ (k' + 1) := by
    rw [show (-1 : ℤ) - (k' : ℤ) = -((k' + 1 : ℕ) : ℤ) by push_cast; ring]
    rw [zpow_neg, zpow_natCast, one_div]
  rw [hz, Nat.add_sub_cancel_right]
  ring

/-- **Iterated derivatives of the logarithmic phase.**  For real `t`, `u`, every `k ≥ 1` and
every `x` with `x + u > 0`,
`d^k/dx^k ( − t·log(x+u)/(2π) ) = − (t/(2π)) · (−1)^{k−1} (k−1)! / (x+u)^k`. -/
theorem logPhase_iteratedDeriv (t u : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x : ℝ, 0 < x + u →
      iteratedDeriv k (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) x
        = -(t / (2 * Real.pi)) * (-1 : ℝ) ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) / (x + u) ^ k := by
  intro x hx
  have hfun : (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi))
      = fun y => (-(t / (2 * Real.pi))) * Real.log (y + u) := by
    funext y; ring
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const]
  simp only []
  rw [iteratedDeriv_log k hk (x + u)]
  ring

end Work.BMF
