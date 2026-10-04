import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `k`-th jet at `0` of a flatly cut monomial

Let `φ` be a function which equals `1` on `[-1, 1]` (no smoothness is needed) and let `ε > 0`.
Then for `|t| < ε` the factor `φ (t / ε)` is `1`, so the function

`t ↦ (φ (t / ε) * t ^ n / n !) • v`

agrees with the pure monomial jet `t ↦ (t ^ n / n !) • v` in a neighbourhood of `0`. Hence their
`k`-th iterated derivatives at `0` coincide, and the latter is `v` when `k = n` and `0` otherwise.
-/

open Filter
open scoped Topology

namespace Work.Diff.EXT

theorem iteratedDeriv_flat_mul_pow_jet
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ℝ → ℝ) (hφ : ∀ t, |t| ≤ 1 → φ t = 1) (ε : ℝ) (hε : 0 < ε) (v : F) (k n : ℕ) :
    iteratedDeriv k (fun t : ℝ => (φ (t / ε) * t ^ n / (n.factorial : ℝ)) • v) 0
      = if k = n then v else 0 := by
  -- The cut is invisible in a neighbourhood of `0`: on `|t| < ε` we have `φ (t / ε) = 1`.
  have hev : (fun t : ℝ => (φ (t / ε) * t ^ n / (n.factorial : ℝ)) • v)
      =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => (t ^ n / (n.factorial : ℝ)) • v) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    have h1 : |t| < ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht
    have h2 : |t / ε| ≤ 1 := by
      rw [abs_div, abs_of_pos hε]
      exact (div_le_one hε).mpr h1.le
    rw [hφ (t / ε) h2, one_mul]
  rw [hev.iteratedDeriv_eq]
  -- It remains to compute the jet of the monomial `t ↦ (t ^ n / n !) • v` at `0`.
  have hpoly : iteratedDeriv k (fun t : ℝ => (t ^ n / (n.factorial : ℝ)) • v) 0
      = if k = n then v else 0 := by
    have hdiff : ContDiffAt ℝ (k : ℕ∞) (fun t : ℝ => t ^ n / (n.factorial : ℝ)) 0 := by
      fun_prop
    rw [iteratedDeriv_smul_const hdiff v]
    rw [iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
    split_ifs <;> simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]
  exact hpoly

end Work.Diff.EXT
