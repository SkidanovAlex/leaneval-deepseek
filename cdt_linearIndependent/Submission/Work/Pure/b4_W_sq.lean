import Mathlib
import Submission.Commons.Data.Nat.Choose.centralBinom_convolution

namespace Work.Pure

open PowerSeries
open scoped BigOperators

/-- `W = Σₙ C(2n,n) yⁿ/16ⁿ = (1 - y/4)^{-1/2}`, the (formal) square root series
appearing in the product formula for `B₄` of Calegari--Dimitrov--Tang (arXiv:2408.15403).

(NB: this series used to live in `Submission.Work.Pure.b4_defs`; that module has since
been rewritten for a different normalisation and no longer carries it, so we restate it
here so that `Work.Pure.b4_W_sq` is well formed.) -/
noncomputable def W : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.centralBinom n : ℚ) / (16 : ℚ) ^ n

/-- The unit `4` of `ℚ`. -/
private def u4 : ℚˣ := Units.mk0 (4 : ℚ) (by norm_num)

/-- The `n`-th coefficient of the convolution square of the central binomial series. -/
private lemma W_sq_coeff (n : ℕ) :
    (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
        ((Nat.centralBinom x.1 : ℚ) / (16 : ℚ) ^ x.1) *
          ((Nat.centralBinom x.2 : ℚ) / (16 : ℚ) ^ x.2))
      = 4 * (1 /ₚ u4 ^ (n + 1)) := by
  have h1 : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
        ((Nat.centralBinom x.1 : ℚ) / (16 : ℚ) ^ x.1) *
          ((Nat.centralBinom x.2 : ℚ) / (16 : ℚ) ^ x.2))
        = (4 : ℚ) ^ n / (16 : ℚ) ^ n := by
    rw [Finset.sum_congr rfl (fun x hx => ?_)]
    · rw [← Finset.sum_div]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun x y => (Nat.centralBinom x : ℚ) * (Nat.centralBinom y : ℚ)) n]
      rw [Commons.Data.Nat.Choose.centralBinom_convolution n]
    · have hx' : x.1 + x.2 = n := by simpa using hx
      rw [← hx', pow_add]
      field_simp
  rw [h1]
  have h2 : (4 : ℚ) ^ n / (16 : ℚ) ^ n = ((1 : ℚ) / 4) ^ n := by
    rw [← div_pow]; norm_num
  have h3 : 4 * (1 /ₚ u4 ^ (n + 1)) = ((1 : ℚ) / 4) ^ n := by
    simp only [u4, one_divp, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [← div_eq_mul_inv, div_eq_iff (by positivity)]
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num
  rw [h2, ← h3]

/-- `W * W = C 4 · invUnitsSub 4`, i.e. `W² = 4/(4 - X)`. -/
private lemma W_mul_W : W * W = PowerSeries.C (4 : ℚ) * PowerSeries.invUnitsSub u4 := by
  ext n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_invUnitsSub]
  simp only [W, PowerSeries.coeff_mk]
  exact W_sq_coeff n

theorem b4_W_sq : (4 - PowerSeries.X) * Work.Pure.W * Work.Pure.W = (4 : PowerSeries ℚ) := by
  have h4 : (4 : PowerSeries ℚ) = PowerSeries.C (4 : ℚ) := rfl
  rw [h4, mul_assoc, W_mul_W]
  have h : PowerSeries.invUnitsSub u4 * (PowerSeries.C (4 : ℚ) - PowerSeries.X) = 1 := by
    have h0 := PowerSeries.invUnitsSub_mul_sub u4
    rw [show ((u4 : ℚˣ) : ℚ) = (4 : ℚ) from rfl] at h0
    exact h0
  rw [show (PowerSeries.C (4 : ℚ) - PowerSeries.X) *
        (PowerSeries.C (4 : ℚ) * PowerSeries.invUnitsSub u4) = PowerSeries.C (4 : ℚ) from by
      calc (PowerSeries.C (4 : ℚ) - PowerSeries.X) *
            (PowerSeries.C (4 : ℚ) * PowerSeries.invUnitsSub u4)
          = PowerSeries.C (4 : ℚ) *
              ((PowerSeries.C (4 : ℚ) - PowerSeries.X) * PowerSeries.invUnitsSub u4) := by ring
        _ = PowerSeries.C (4 : ℚ) *
              (PowerSeries.invUnitsSub u4 * (PowerSeries.C (4 : ℚ) - PowerSeries.X)) := by ring
        _ = PowerSeries.C (4 : ℚ) * 1 := by rw [h]
        _ = PowerSeries.C (4 : ℚ) := by ring]

end Work.Pure
