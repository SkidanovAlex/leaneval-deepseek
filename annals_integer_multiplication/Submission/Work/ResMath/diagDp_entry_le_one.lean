import Mathlib
import Submission.Work.ResMath.defs

/-!
# The diagonal entries of `D' = D / 2^{2α²−2}` are bounded by 1

Paper §4.1 (Lemma 4.5 / Prop 4.7(i) bookkeeping, step M5 of `resMath1D.lean`): with
`β_ℓ = tℓ/s − [tℓ/s]  ∈ [−1/2, 1/2]` and `D = diag(e^{π α² β_ℓ²})`,

  `|D'_{ℓℓ}| = e^{π α² β_ℓ²} / 2^{2α²−2} ≤ e^{π α²/4} / 2^{2α²−2} < 1`   for `α ≥ 2`.

The numerical core: `π/4 ≤ 1` gives `π α² β² ≤ α²`, and `α² ≤ (2α²−2) log 2` for `α ≥ 2`
(log 2 > 0.693 > 2/3), so `e^{π α² β²} ≤ 2^{2α²−2}`.
-/

namespace Work.ResMath

/-- `β_ℓ = tℓ/s − [tℓ/s]` lies in `[−1/2, 1/2]`: the nearest-integer map `rnd` differs from its
argument by at most `1/2`. -/
private lemma betaR_abs_le_half (s t ℓ : ℕ) : |HvdH.betaR s t ℓ| ≤ 1 / 2 := by
  unfold HvdH.betaR HvdH.rnd
  set x : ℝ := (t : ℝ) * (ℓ : ℝ) / (s : ℝ) with hx
  have h1 : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 - 1 < ((⌊x + 1 / 2⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor _
  rw [abs_le]
  constructor <;> linarith

/-- Numerics of the Gaussian factor: for `α ≥ 2` and `|β| ≤ 1/2`,
`e^{π α² β²} ≤ 2^{2α²−2}`. -/
private lemma exp_pi_sq_le (α : ℕ) (hα : 2 ≤ α) (β : ℝ) (hβ : |β| ≤ 1 / 2) :
    Real.exp (Real.pi * (α : ℝ) ^ 2 * β ^ 2) ≤ (2 : ℝ) ^ (2 * α ^ 2 - 2) := by
  have hβ2 : β ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hβ
    nlinarith [sq_nonneg β]
  have hα2 : (4 : ℝ) ≤ (α : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
    nlinarith
  have hcast : ((2 * α ^ 2 - 2 : ℕ) : ℝ) = 2 * (α : ℝ) ^ 2 - 2 := by
    have h : 2 ≤ 2 * α ^ 2 := by nlinarith
    rw [Nat.cast_sub h]
    push_cast
    ring
  have hpib : Real.pi * β ^ 2 ≤ 1 := by
    have h : Real.pi * β ^ 2 ≤ 4 * β ^ 2 :=
      mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (sq_nonneg β)
    linarith
  have hle : Real.pi * (α : ℝ) ^ 2 * β ^ 2 ≤ ((2 * α ^ 2 - 2 : ℕ) : ℝ) * Real.log 2 := by
    rw [hcast]
    have h1 : Real.pi * (α : ℝ) ^ 2 * β ^ 2 ≤ (α : ℝ) ^ 2 := by
      have h2 : (α : ℝ) ^ 2 * (Real.pi * β ^ 2) ≤ (α : ℝ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hpib (by positivity)
      linarith
    have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith
  calc Real.exp (Real.pi * (α : ℝ) ^ 2 * β ^ 2)
      ≤ Real.exp (((2 * α ^ 2 - 2 : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hle
    _ = (2 : ℝ) ^ (2 * α ^ 2 - 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- Norm of a real number seen as a complex number. -/
private lemma norm_ofReal' (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

/-- `‖D'_{ℓℓ}‖ ≤ 1` for `α ≥ 2` (paper §4.1). -/
theorem diagDp_entry_le_one (s t α : ℕ) (hα : 2 ≤ α) (ℓ : Fin s) :
    ‖HvdH.diagD' s t α ℓ ℓ‖ ≤ 1 := by
  have hβ := betaR_abs_le_half s t (ℓ : ℕ)
  have hexp := exp_pi_sq_le α hα (HvdH.betaR s t (ℓ : ℕ)) hβ
  have hval : HvdH.diagD' s t α ℓ ℓ
      = ((((1 : ℝ) / (2 : ℝ) ^ (2 * α ^ 2 - 2) *
          Real.exp (Real.pi * (α : ℝ) ^ 2 * (HvdH.betaR s t (ℓ : ℕ)) ^ 2)) : ℝ) : ℂ) := by
    simp [HvdH.diagD', HvdH.diagD, Matrix.diagonal_apply_eq]
  rw [hval, norm_ofReal']
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _),
    abs_of_pos (by positivity : (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ (2 * α ^ 2 - 2))]
  have h3 : (0 : ℝ) < (2 : ℝ) ^ (2 * α ^ 2 - 2) := by positivity
  have h4 : (1 : ℝ) / (2 : ℝ) ^ (2 * α ^ 2 - 2) *
        Real.exp (Real.pi * (α : ℝ) ^ 2 * (HvdH.betaR s t (ℓ : ℕ)) ^ 2)
      ≤ (1 : ℝ) / (2 : ℝ) ^ (2 * α ^ 2 - 2) * (2 : ℝ) ^ (2 * α ^ 2 - 2) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  rwa [div_mul_cancel₀ _ (ne_of_gt h3)] at h4

end Work.ResMath
