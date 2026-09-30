import Mathlib
import Submission.Work.BMF.Psi1_local_defs
import Submission.Work.BMF.geom_dist_pow_sum_bound
import Submission.Work.BMF.rho_exp_eighth_bounds
import Submission.Work.BMF.serTerm_le_of_le
import Submission.Work.BMF.serTerm_le_of_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The log-dyadic series bound

This file proves `Work.BMF.log_dyadic_series_bound`: there is an absolute constant `C > 0`
such that for every `α ∈ (0,1]`, every `j : ℕ` and every finite set `S ⊆ ℕ` of log-dyadic
block indices,

`∑_{k ∈ S} serTerm α j k ≤ C * 2^(-jα)`.

The summand is

`serTerm α j k = 2^(-kα) * exp (-(log 2)^2 * (max 0 (|j-k|-1))^2)`,

so the Gaussian factor kills the blocks `k` far from the block `j` of `p`, while the factor
`2^(-kα)` is of size `2^(-jα)` near `k = j`.  Concretely we prove the pointwise geometric
majorant

`serTerm α j k ≤ 10 * 2^(-jα) * exp(-1/8)^(Nat.dist j k)`

and sum it, using `∑_{k ∈ S} exp(-1/8)^(Nat.dist j k) ≤ 2 * (1 - exp(-1/8))⁻¹ ≤ 18`.
The resulting explicit constant is `C = 180`.
-/

namespace Work.BMF

/-- The Euclidean absolute value of the difference of two cast naturals is the cast of their
natural distance. -/
lemma abs_cast_sub_cast_eq_dist (j k : ℕ) : |(j : ℝ) - (k : ℝ)| = (Nat.dist j k : ℝ) := by
  rcases le_total k j with h | h
  · rw [Nat.dist_eq_sub_of_le_right h,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h)), Nat.cast_sub h]
  · rw [Nat.dist_eq_sub_of_le h,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h)), Nat.cast_sub h]
    ring

/-- Pointwise geometric majorant for `serTerm`: the Gaussian decay in `|j - k|` is dominated
by `exp(-1/8)^(Nat.dist j k)`, up to the explicit factor `10`. -/
lemma serTerm_le_dist (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (j k : ℕ) :
    serTerm α j k ≤
      10 * (2 : ℝ) ^ (-(j : ℝ) * α) * (Real.exp (-(1 / 8 : ℝ))) ^ (Nat.dist j k) := by
  rcases le_total k j with h | h
  · refine (Work.BMF.serTerm_le_of_le α hα0 hα1 h).trans_eq ?_
    rw [Nat.dist_eq_sub_of_le_right h]
  · refine (Work.BMF.serTerm_le_of_ge α hα0 hα1 h).trans_eq ?_
    rw [Nat.dist_eq_sub_of_le h]

/-- There is an absolute constant `C > 0` bounding the log-dyadic series over any finite set
of block indices, uniformly in `α ∈ (0,1]` and in the block `j` of `p`. -/
theorem log_dyadic_series_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ j : ℕ, ∀ S : Finset ℕ,
      (∑ k ∈ S, Work.BMF.serTerm α j k) ≤ C * (2 : ℝ) ^ (-(j : ℝ) * α) := by
  obtain ⟨hρpos, hρlt1, -, hρ19⟩ := Work.BMF.rho_exp_eighth_bounds
  have hρpos' : (0 : ℝ) ≤ Real.exp (-(1 / 8 : ℝ)) := le_of_lt hρpos
  have hpos : 0 < 1 - Real.exp (-(1 / 8 : ℝ)) := by linarith
  have hinv : (1 - Real.exp (-(1 / 8 : ℝ)))⁻¹ ≤ 9 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    linarith
  refine ⟨180, by norm_num, ?_⟩
  intro α hα0 hα1 j S
  have hA : (0 : ℝ) ≤ (2 : ℝ) ^ (-(j : ℝ) * α) := Real.rpow_nonneg (by norm_num) _
  have hgeom : (∑ k ∈ S, (Real.exp (-(1 / 8 : ℝ))) ^ (Nat.dist j k)) ≤
      2 * (1 - Real.exp (-(1 / 8 : ℝ)))⁻¹ :=
    Work.BMF.geom_dist_pow_sum_bound _ hρpos' hρlt1 j S
  calc (∑ k ∈ S, serTerm α j k)
      ≤ ∑ k ∈ S,
          10 * (2 : ℝ) ^ (-(j : ℝ) * α) * (Real.exp (-(1 / 8 : ℝ))) ^ (Nat.dist j k) :=
        Finset.sum_le_sum (fun k _ => serTerm_le_dist α hα0 hα1 j k)
    _ = 10 * (2 : ℝ) ^ (-(j : ℝ) * α) *
          ∑ k ∈ S, (Real.exp (-(1 / 8 : ℝ))) ^ (Nat.dist j k) := by
        rw [Finset.mul_sum]
    _ ≤ 10 * (2 : ℝ) ^ (-(j : ℝ) * α) * (2 * (1 - Real.exp (-(1 / 8 : ℝ)))⁻¹) :=
        mul_le_mul_of_nonneg_left hgeom (mul_nonneg (by norm_num) hA)
    _ ≤ 180 * (2 : ℝ) ^ (-(j : ℝ) * α) := by
        have h20 : 20 * (1 - Real.exp (-(1 / 8 : ℝ)))⁻¹ ≤ 180 := by linarith
        calc 10 * (2 : ℝ) ^ (-(j : ℝ) * α) * (2 * (1 - Real.exp (-(1 / 8 : ℝ)))⁻¹)
            = 20 * (1 - Real.exp (-(1 / 8 : ℝ)))⁻¹ * (2 : ℝ) ^ (-(j : ℝ) * α) := by ring
          _ ≤ 180 * (2 : ℝ) ^ (-(j : ℝ) * α) := mul_le_mul_of_nonneg_right h20 hA

end Work.BMF
