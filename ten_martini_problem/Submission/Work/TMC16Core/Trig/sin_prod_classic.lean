import Mathlib
import Submission.Work.TMC16Core.Basic.sin_prod
import Submission.Work.TMC16Core.Basic.rational_block_prod

namespace Work.TMC16Core.Trig

open Finset

/-- For `1 ≤ j < m`, `‖1 - μ^j‖ = 2 sin (π j / m)`, where `μ = exp (2 i π / m)`. -/
lemma norm_one_sub_pow_exp (m j : ℕ) (hm : 0 < m) (hj : j ∈ Finset.Ico 1 m) :
    ‖1 - (Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))) ^ j‖
      = 2 * Real.sin (Real.pi * (j : ℝ) / (m : ℝ)) := by
  set μ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) with hμdef
  rw [Finset.mem_Ico] at hj
  obtain ⟨hj1, hjm⟩ := hj
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hjmR : (j : ℝ) < (m : ℝ) := by exact_mod_cast hjm
  have hy : 0 < Real.pi * (j : ℝ) / (m : ℝ) :=
    div_pos (mul_pos Real.pi_pos hjR) hmr
  have hym : Real.pi * (j : ℝ) / (m : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hmr]
    exact mul_lt_mul_of_pos_left hjmR Real.pi_pos
  have hpow : μ ^ j
      = Complex.exp (Complex.I * ((2 * (Real.pi * (j : ℝ) / (m : ℝ)) : ℝ) : ℂ)) := by
    rw [hμdef, ← Complex.exp_nat_mul]
    congr 1
    have harg : (j : ℂ) * (2 * ↑Real.pi * Complex.I / (m : ℂ))
        = Complex.I * ((2 * (Real.pi * (j : ℝ) / (m : ℝ)) : ℝ) : ℂ) := by
      push_cast
      field_simp
    exact harg
  rw [norm_sub_rev, hpow, Work.TMC16Core.Basic.norm_exp_two_mul_I_sub_one,
    abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hy hym)]

theorem sin_prod_classic (m : ℕ) (hm : 0 < m) :
    ∏ j ∈ Finset.Ico 1 m, Real.sin (Real.pi * (j : ℝ) / (m : ℝ)) = (m : ℝ) / 2 ^ (m - 1) := by
  classical
  set μ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) with hμdef
  have hμ : IsPrimitiveRoot μ m := by
    rw [hμdef]; exact Complex.isPrimitiveRoot_exp m hm.ne'
  have hprim : IsPrimitiveRoot μ ((m - 1) + 1) := by
    rw [Nat.sub_add_cancel hm]; exact hμ
  have hprod_range : ∏ k ∈ Finset.range (m - 1), (1 - μ ^ (k + 1)) = (m : ℂ) := by
    rw [IsPrimitiveRoot.prod_one_sub_pow_eq_order hprim]
    rw [show ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) from by
      rw [Nat.cast_sub hm, Nat.cast_one]; ring]
  have hprod : ∏ j ∈ Finset.Ico 1 m, (1 - μ ^ j) = (m : ℂ) := by
    rw [Finset.prod_Ico_eq_prod_range]
    simpa [Nat.add_comm] using hprod_range
  have hnorm : ∏ j ∈ Finset.Ico 1 m, ‖1 - μ ^ j‖ = (m : ℝ) := by
    rw [← norm_prod, hprod, Complex.norm_natCast]
  have hpoint : ∀ j ∈ Finset.Ico 1 m,
      ‖1 - μ ^ j‖ = 2 * Real.sin (Real.pi * (j : ℝ) / (m : ℝ)) := by
    intro j hj
    exact norm_one_sub_pow_exp m j hm hj
  have hpoint_prod : ∏ j ∈ Finset.Ico 1 m, ‖1 - μ ^ j‖
      = 2 ^ (m - 1) * ∏ j ∈ Finset.Ico 1 m, Real.sin (Real.pi * (j : ℝ) / (m : ℝ)) := by
    rw [Finset.prod_congr rfl hpoint, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
  have hgoal : 2 ^ (m - 1) * ∏ j ∈ Finset.Ico 1 m, Real.sin (Real.pi * (j : ℝ) / (m : ℝ))
      = (m : ℝ) := by
    rw [← hpoint_prod, hnorm]
  rw [eq_div_iff (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), mul_comm]
  exact hgoal

end Work.TMC16Core.Trig
