import Mathlib

namespace Work.Holonomy3

/-- Norm bound for the Cauchy product of two power series, at a point `z` where both are
absolutely summable: the absolute values of the coefficients of the product, weighted by
`z ^ k`, form a summable family, and the total sum is at most the product of the two
total sums.

This is the (`p = q = r = 1`) Young/convolution inequality for power series; the proof is
the Cauchy product formula `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`
together with the triangle inequality applied coefficientwise. -/
theorem psi_mul_norm_le {ψ φ : PowerSeries ℂ} {z : ℂ}
    (hψ : Summable (fun k : ℕ => ‖PowerSeries.coeff k ψ * z ^ k‖))
    (hφ : Summable (fun k : ℕ => ‖PowerSeries.coeff k φ * z ^ k‖)) :
    Summable (fun k : ℕ => ‖PowerSeries.coeff k (ψ * φ) * z ^ k‖) ∧
    (∑' k : ℕ, ‖PowerSeries.coeff k (ψ * φ) * z ^ k‖) ≤
      (∑' k : ℕ, ‖PowerSeries.coeff k ψ * z ^ k‖) * (∑' k : ℕ, ‖PowerSeries.coeff k φ * z ^ k‖) := by
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  -- the two nonnegative real sequences of absolute values
  have hf' : Summable (fun x : ℕ => ‖‖PowerSeries.coeff x ψ * z ^ x‖‖) :=
    hψ.congr (fun x => (Real.norm_of_nonneg (norm_nonneg _)).symm)
  have hg' : Summable (fun x : ℕ => ‖‖PowerSeries.coeff x φ * z ^ x‖‖) :=
    hφ.congr (fun x => (Real.norm_of_nonneg (norm_nonneg _)).symm)
  -- the convolution of the two absolute-value sequences is summable
  have hS : Summable (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      ‖PowerSeries.coeff kl.1 ψ * z ^ kl.1‖ * ‖PowerSeries.coeff kl.2 φ * z ^ kl.2‖) :=
    summable_sum_mul_antidiagonal_of_summable_norm' (R := ℝ)
      (f := fun x : ℕ => ‖PowerSeries.coeff x ψ * z ^ x‖)
      (g := fun x : ℕ => ‖PowerSeries.coeff x φ * z ^ x‖) hf' hψ hg' hφ
  -- coefficientwise triangle inequality
  have hinner : ∀ n : ℕ, ‖PowerSeries.coeff n (ψ * φ) * z ^ n‖
      ≤ ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          ‖PowerSeries.coeff kl.1 ψ * z ^ kl.1‖ * ‖PowerSeries.coeff kl.2 φ * z ^ kl.2‖ := by
    intro n
    calc ‖PowerSeries.coeff n (ψ * φ) * z ^ n‖
        = ‖PowerSeries.coeff n (ψ * φ)‖ * ‖z‖ ^ n := by rw [norm_mul, norm_pow]
      _ = ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff kl.1 ψ * PowerSeries.coeff kl.2 φ‖ * ‖z‖ ^ n := by
            rw [PowerSeries.coeff_mul]
      _ ≤ (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
            ‖PowerSeries.coeff kl.1 ψ‖ * ‖PowerSeries.coeff kl.2 φ‖) * ‖z‖ ^ n := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hznn n)
            refine le_trans (norm_sum_le _ _) ?_
            exact Finset.sum_le_sum (fun kl _ => norm_mul_le _ _)
      _ = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
            (‖PowerSeries.coeff kl.1 ψ‖ * ‖z‖ ^ kl.1) *
              (‖PowerSeries.coeff kl.2 φ‖ * ‖z‖ ^ kl.2) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun kl hkl => ?_)
            rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]; ring
      _ = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
            ‖PowerSeries.coeff kl.1 ψ * z ^ kl.1‖ * ‖PowerSeries.coeff kl.2 φ * z ^ kl.2‖ := by
            refine Finset.sum_congr rfl (fun kl _ => ?_)
            rw [norm_mul, norm_pow, norm_mul, norm_pow]
  have hsumm : Summable (fun k : ℕ => ‖PowerSeries.coeff k (ψ * φ) * z ^ k‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hinner hS
  refine ⟨hsumm, ?_⟩
  -- Cauchy product formula for the absolute values
  have hcauch := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (R := ℝ)
    (f := fun x : ℕ => ‖PowerSeries.coeff x ψ * z ^ x‖)
    (g := fun x : ℕ => ‖PowerSeries.coeff x φ * z ^ x‖) hf' hg'
  exact le_trans (Summable.tsum_le_tsum hinner hsumm hS) (le_of_eq hcauch.symm)

end Work.Holonomy3
