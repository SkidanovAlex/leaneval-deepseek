import Mathlib
import Submission.Work.EQ.GermSetup
import Submission.Work.EQ.glin_step
import Submission.Work.EQ.tsum_shift_sub

/-!
# Telescoping the linear part of the germ residual

`GlinOf a ρ` is the linear (in `ρ`) part of the residual `GOf a ρ` of the cleared germ equation
of the equichordal half map (see `Submission/Work/EQ/GermSetup.lean`).  It is

`GlinOf a ρ v = a (λ² ρ(λ v) - λ⁻² ρ(v/λ))`,   `λ = eqLam a = lamC a`,

and along the orbit `v_j = λ^{2j+1} u` the weighted terms telescope: with

`b_j = a λ^{4j} ρ(λ^{2j} u)`

one has `λ^{4j+2} GlinOf a ρ (λ^{2j+1} u) = b_{j+1} - b_j` (`glin_step`, because
`λ^{4j+2} λ² = λ^{4(j+1)}` and `λ^{4j+2} λ⁻² = λ^{4j}`).  Summing over `j ≥ 0`, the series
telescopes to `-b_0 = -a ρ u` (`tsum_shift_sub`); the tail `b_N → 0` is where the boundedness
hypothesis on `ρ` enters, since it makes `∑ j, b_j` summable and hence makes the `tsum` the
honest limit of the partial sums.  The main theorem of this file is `sum_Glin_mul`.
-/

namespace Work.EQ

open Complex Metric Filter

noncomputable section

variable {a : ℝ}

/-- The `n`-th term `b_n = a λ^{4n} ρ (λ^{2n} u)` of the telescoping sequence whose successive
differences are the summands of `sum_Glin_mul`. -/
noncomputable def telFun (a : ℝ) (ρ : ℂ → ℂ) (u : ℂ) (n : ℕ) : ℂ :=
  (a : ℂ) * ((lamC a) ^ (4 * n) * ρ ((lamC a) ^ (2 * n) * u))

/-- `‖lamC a‖ = eqLam a` for `0 < a`: `lamC a` is the (nonnegative) real number `eqLam a`. -/
lemma norm_lamC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : ‖lamC a‖ = eqLam a := by
  rw [lamC]
  simp [abs_of_pos (eqLam_pos ha0 ha1)]

/-- `telFun a ρ u` is summable when `ρ` is bounded on the disc of radius `germR a`: its norms are
dominated by the geometric sequence `|a| C (λ⁴)^n`, and `λ⁴ < 1`. -/
lemma summable_telFun {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ} {C : ℝ}
    (hρ : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ C) (u : ℂ) (hu : ‖u‖ ≤ germR a) :
    Summable (telFun a ρ u) := by
  have hp := eqLam_pos ha0 ha1
  have hlt := eqLam_lt_one ha0 ha1
  have hgeom : Summable (fun n : ℕ => ((eqLam a) ^ 4) ^ n) :=
    summable_geometric_of_lt_one (pow_nonneg (le_of_lt hp) 4)
      (pow_lt_one₀ (le_of_lt hp) hlt (by norm_num))
  have hg : Summable (fun n : ℕ => |a| * C * (eqLam a) ^ (4 * n)) := by
    have h := hgeom.mul_left (|a| * C)
    simpa [pow_mul] using h
  refine Summable.of_norm_bounded hg (fun n => ?_)
  have hz : ‖(lamC a) ^ (2 * n) * u‖ ≤ germR a := by
    rw [norm_mul, norm_pow, norm_lamC ha0 ha1]
    calc (eqLam a) ^ (2 * n) * ‖u‖ ≤ 1 * ‖u‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (le_of_lt hp) (le_of_lt hlt)) (norm_nonneg u)
      _ = ‖u‖ := one_mul _
      _ ≤ germR a := hu
  calc ‖telFun a ρ u n‖
      = |a| * ((eqLam a) ^ (4 * n) * ‖ρ ((lamC a) ^ (2 * n) * u)‖) := by
        simp only [telFun, norm_mul, norm_pow]
        rw [norm_lamC ha0 ha1]
        simp
    _ ≤ |a| * ((eqLam a) ^ (4 * n) * C) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
        exact mul_le_mul_of_nonneg_left (hρ _ hz) (pow_nonneg (le_of_lt hp) (4 * n))
    _ = |a| * C * (eqLam a) ^ (4 * n) := by ring

/-- **Telescoping of the linear part of the germ residual.**
`∑_j λ^{4j+2} GlinOf a ρ (λ^{2j+1} u) = -a ρ u`, for `ρ` bounded on the disc `‖z‖ ≤ germR a`
and `‖u‖ ≤ germR a`.  (`GlinOf` and `lamC` are the linear part of the germ residual and
`λ = eqLam a` from `Submission/Work/EQ/GermSetup.lean`; see the file header for the telescoping
argument.) -/
theorem sum_Glin_mul {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ} {C : ℝ}
    (hρ : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ C) (u : ℂ) (hu : ‖u‖ ≤ germR a) :
    (∑' (j : ℕ), (lamC a) ^ (4 * j + 2) * GlinOf a ρ ((lamC a) ^ (2 * j + 1) * u))
      = -(a : ℂ) * ρ u := by
  have hsum : Summable (telFun a ρ u) := summable_telFun ha0 ha1 hρ u hu
  calc (∑' (j : ℕ), (lamC a) ^ (4 * j + 2) * GlinOf a ρ ((lamC a) ^ (2 * j + 1) * u))
      = ∑' (j : ℕ), (telFun a ρ u (j + 1) - telFun a ρ u j) :=
        tsum_congr (fun j => glin_step ha0 ha1 ρ u j)
    _ = -telFun a ρ u 0 := tsum_shift_sub hsum
    _ = -(a : ℂ) * ρ u := by simp [telFun]

end

end Work.EQ
