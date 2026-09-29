import Mathlib
import Submission.Work.Holonomy3.psi_mul_norm_le

namespace Work.Holonomy3

open scoped BigOperators

/-- Base case `d = 0` of `psi_pow_norm_bound`: for the constant power series `1` the weighted
series of coefficient norms is supported at `k = 0`, where it equals `1`. -/
theorem psi_pow_zero_norm_bound {z : ℂ} :
    Summable (fun k : ℕ => ‖PowerSeries.coeff k ((1 : PowerSeries ℂ)) * z ^ k‖) ∧
    (∑' k : ℕ, ‖PowerSeries.coeff k ((1 : PowerSeries ℂ)) * z ^ k‖) ≤ 1 := by
  have hfun : (fun k : ℕ => ‖PowerSeries.coeff k ((1 : PowerSeries ℂ)) * z ^ k‖)
      = fun k => if k = 0 then (1 : ℝ) else 0 := by
    funext k
    rw [PowerSeries.coeff_one]
    by_cases hk : k = 0
    · subst hk; simp
    · simp [hk]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  · rw [hfun, tsum_eq_single (0 : ℕ) (fun b hb => by simp [hb])]
    simp

/-- The weighted `ℓ¹`-norm of the `d`-th power of a power series is at most the `d`-th power of
the weighted `ℓ¹`-norm of the series, whenever the latter is finite. -/
theorem psi_pow_norm_bound {ψ : PowerSeries ℂ} {z : ℂ}
    (hgn : Summable (fun j : ℕ => ‖PowerSeries.coeff j ψ‖ * ‖z‖ ^ j)) :
    ∀ d : ℕ,
      Summable (fun k : ℕ => ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖) ∧
      (∑' k : ℕ, ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖)
        ≤ (∑' j : ℕ, ‖PowerSeries.coeff j ψ‖ * ‖z‖ ^ j) ^ d := by
  have hψ : Summable (fun j : ℕ => ‖PowerSeries.coeff j ψ * z ^ j‖) :=
    hgn.congr fun j => by rw [norm_mul, norm_pow]
  have hAeq : (∑' j : ℕ, ‖PowerSeries.coeff j ψ * z ^ j‖)
      = (∑' j : ℕ, ‖PowerSeries.coeff j ψ‖ * ‖z‖ ^ j) :=
    tsum_congr fun j => by rw [norm_mul, norm_pow]
  have hA0 : 0 ≤ ∑' j : ℕ, ‖PowerSeries.coeff j ψ‖ * ‖z‖ ^ j :=
    tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  intro d
  induction d with
  | zero =>
      refine ⟨psi_pow_zero_norm_bound.1, ?_⟩
      simpa using psi_pow_zero_norm_bound.2
  | succ d ih =>
      rw [pow_succ]
      obtain ⟨hd, hdle⟩ := ih
      have hstep := psi_mul_norm_le hd hψ
      refine ⟨hstep.1, ?_⟩
      calc (∑' k : ℕ, ‖PowerSeries.coeff k (ψ ^ d * ψ) * z ^ k‖)
          ≤ (∑' k : ℕ, ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖) *
            (∑' j : ℕ, ‖PowerSeries.coeff j ψ * z ^ j‖) := hstep.2
        _ = (∑' k : ℕ, ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖) *
            (∑' j : ℕ, ‖PowerSeries.coeff j ψ‖ * ‖z‖ ^ j) := by rw [hAeq]
        _ ≤ (∑' j : ℕ, ‖PowerSeries.coeff j ψ‖ * ‖z‖ ^ j) ^ d *
            (∑' j : ℕ, ‖PowerSeries.coeff j ψ‖ * ‖z‖ ^ j) :=
              mul_le_mul_of_nonneg_right hdle hA0

end Work.Holonomy3
