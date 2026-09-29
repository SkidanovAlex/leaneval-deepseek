import Mathlib
import Submission.Work.Haupt.thetaCore

/-!
# `ThetaProd x x` in terms of the even product

For `‖x‖ < 1` and `x ≠ 0` the two-variable theta product `ThetaProd x z = ∏'ₙ (1 + x^{2n+1}z)
(1 + x^{2n+1}/z)` evaluated at `z = x` collapses to

`ThetaProd x x = ∏'ₙ (1 + x^{2n+2})(1 + x^{2n}) = 2 (∏'ₙ (1 + x^{2n+2}))²`.

Indeed `x^{2n+1}·x = x^{2n+2}` and `x^{2n+1}/x = x^{2n}`, and in the second family the factor at
`n = 0` is `2` while for `n ≥ 1` it is `1 + x^{2n} = 1 + x^{2(n-1)+2}`, i.e. the first family again
after reindexing.

The hypothesis `x ≠ 0` is genuinely needed: at `x = 0` the left-hand side is
`∏'ₙ (1 + 0)(1 + 0) = 1` while the right-hand side is `2`.
-/

set_option maxHeartbeats 800000

namespace Work.Haupt

open scoped BigOperators

noncomputable section

theorem ThetaProd_self (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    ThetaProd x x = 2 * (∏' m : ℕ, (1 + x ^ (2 * m + 2))) ^ 2 := by
  have hx2 : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  -- summability of the exponent families attached to the two factors
  have hsA : Summable (fun n : ℕ => x ^ (2 * n + 2)) := by
    have h : Summable (fun n : ℕ => (x ^ 2) ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hx2)
    refine h.congr (fun n => ?_)
    rw [pow_succ, ← pow_mul, ← pow_add]
  have hsA' : Summable (fun n : ℕ => x ^ (2 * (n + 1))) := by
    have h : Summable (fun n : ℕ => (x ^ 2) ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hx2)
    refine h.congr (fun n => ?_)
    rw [pow_succ, ← pow_mul, ← pow_add]
    congr 1
  have hsC : Summable (fun n : ℕ => x ^ (2 * n)) := by
    have h : Summable (fun n : ℕ => (x ^ 2) ^ n) := summable_geometric_of_norm_lt_one hx2
    exact h.congr (fun n => by rw [← pow_mul])
  -- the corresponding infinite products converge
  have mA : Multipliable (fun n : ℕ => 1 + x ^ (2 * n + 2)) :=
    Complex.multipliable_one_add_of_summable hsA
  have mC : Multipliable (fun n : ℕ => 1 + x ^ (2 * n)) :=
    Complex.multipliable_one_add_of_summable hsC
  have mC' : Multipliable (fun n : ℕ => 1 + x ^ (2 * (n + 1))) :=
    Complex.multipliable_one_add_of_summable hsA'
  -- the two factors of `ThetaProd x x`
  have hstep : ThetaProd x x = ∏' n : ℕ, (1 + x ^ (2 * n + 2)) * (1 + x ^ (2 * n)) := by
    unfold ThetaProd
    refine tprod_congr (fun n => ?_)
    have h1 : x ^ (2 * n + 1) * x = x ^ (2 * n + 2) := by
      rw [← pow_succ]
    have h2 : x ^ (2 * n + 1) / x = x ^ (2 * n) := by
      rw [pow_succ]
      exact mul_div_cancel_right₀ _ hx0
    rw [h1, h2]
  rw [hstep, mA.tprod_mul mC]
  -- the second family is `2` times a reindexed copy of the first
  have hC : (∏' n : ℕ, (1 + x ^ (2 * n))) = 2 * ∏' m : ℕ, (1 + x ^ (2 * m + 2)) := by
    have hsplit := tprod_eq_zero_mul' (f := fun n : ℕ => 1 + x ^ (2 * n)) mC'
    rw [hsplit]
    have : (∏' b : ℕ, (1 + x ^ (2 * (b + 1)))) = ∏' m : ℕ, (1 + x ^ (2 * m + 2)) :=
      tprod_congr (fun b => by congr 1)
    rw [this]
    norm_num
  rw [hC]
  ring

end

end Work.Haupt
