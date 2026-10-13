import Mathlib
import Submission.Work.WilG4c.iteratedFDeriv_const_smul
import Submission.Work.WilG4c.iteratedFDeriv_fun_add_const

set_option linter.unusedVariables false

namespace Work.WilG4c

/-- If the iterated Fréchet derivatives of `P` at `z` up to order `r` all have operator norm at
most `1`, then the same is true up to a factor `5 / 2` for the affine modification
`y ↦ 2 * P y - 1 / 2`.

For `m ≥ 1` the additive constant is invisible
(`iteratedFDeriv_fun_add_const`) and the factor `2` pulls out of the iterated derivative
(`iteratedFDeriv_const_smul`), giving the bound `2 * 1 = 2 ≤ 5 / 2`.  For `m = 0` the iterated
derivative is the function value itself (`norm_iteratedFDeriv_zero`), and
`|2 * P z - 1 / 2| ≤ 2 * |P z| + 1 / 2 ≤ 2 + 1 / 2 = 5 / 2`. -/
theorem NormIteratedFDerivTwoMulSubHalf {N : ℕ} (r : ℕ) (P : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ)
    (hP : ContDiffAt ℝ r P z) (hb : ∀ m, m ≤ r → ‖iteratedFDeriv ℝ m P z‖ ≤ 1) :
    ∀ m, m ≤ r → ‖iteratedFDeriv ℝ m (fun y : Fin N → ℝ => 2 * P y - 1 / 2) z‖ ≤ 5 / 2 := by
  intro m hm
  rcases eq_or_ne m 0 with h0 | h0
  · -- `m = 0`: the statement is a pointwise estimate on the values.
    subst h0
    rw [norm_iteratedFDeriv_zero]
    have hz : ‖P z‖ ≤ 1 := by
      have h := hb 0 (Nat.zero_le r)
      rwa [norm_iteratedFDeriv_zero] at h
    have h2 : ‖(2 : ℝ) * P z‖ = 2 * ‖P z‖ := by rw [norm_mul, Real.norm_ofNat]
    have h3 : ‖((1 : ℝ) / 2)‖ = (1 : ℝ) / 2 := by
      rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have h4 := norm_sub_le ((2 : ℝ) * P z) ((1 : ℝ) / 2)
    linarith
  · -- `m ≥ 1`: the constant `- 1 / 2` drops out and the factor `2` pulls out.
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr h0
    have key1 : iteratedFDeriv ℝ m (fun y : Fin N → ℝ => 2 * P y - 1 / 2) z
        = iteratedFDeriv ℝ m (fun y : Fin N → ℝ => 2 * P y) z :=
      iteratedFDeriv_fun_add_const hm1 (fun y : Fin N → ℝ => 2 * P y) (-(1 / 2 : ℝ)) z
    have key2 : iteratedFDeriv ℝ m (fun y : Fin N → ℝ => 2 * P y) z
        = (2 : ℝ) • iteratedFDeriv ℝ m P z := by
      rw [show (fun y : Fin N → ℝ => 2 * P y) = (2 : ℝ) • P from rfl]
      exact iteratedFDeriv_const_smul 2 m P z
    rw [key1, key2, norm_smul, Real.norm_ofNat]
    have hb' := hb m hm
    linarith

end Work.WilG4c
