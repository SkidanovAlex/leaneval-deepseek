import Mathlib
import Submission.Work.FIArea5.S16.fourier_truncation
import Submission.Work.FIArea6.S16fcoef_theta_range
import Submission.Work.FIArea5.S16.fourierCoeff_decay_cMoll

namespace Work.FIArea6

/-- The `ℤ`-indexed weight `ℓ ↦ (1 + (θℓ)²)⁻¹` is even. -/
lemma fcoefWeight_even (θ : ℝ) :
    Function.Even (fun ℓ : ℤ => (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) := by
  intro ℓ
  show (1 + (θ * ((-ℓ : ℤ) : ℝ)) ^ 2)⁻¹ = (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹
  push_cast
  ring_nf

/-- Even-function reduction: the symmetric `ℤ`-sum of the weight is at most twice the
`ℕ`-range sum. -/
lemma fcoefWeight_Icc_le_range (θ : ℝ) (L : ℕ) :
    ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹
      ≤ 2 * ∑ n ∈ Finset.range (L + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹ := by
  have h := Finset.sum_Icc_of_even_eq_range
      (f := fun ℓ : ℤ => (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) (fcoefWeight_even θ) L
  have h' : ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹
      = 2 * (∑ n ∈ Finset.range (L + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹) - 1 := by
    simpa using h
  rw [h']
  linarith

theorem S16FcoefSum {q : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2) (L : ℕ) :
    ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ‖Work.FIArea5.S16.fcoef q ℓ‖ ≤ 100000000 := by
  have hrange := S16fcoef_theta_range hθ hθ1 L
  have hIcc := fcoefWeight_Icc_le_range θ L
  have hkey : θ * ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹ ≤ 10 := by
    calc θ * ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹
        ≤ θ * (2 * ∑ n ∈ Finset.range (L + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hIcc hθ.le
      _ = 2 * (θ * ∑ n ∈ Finset.range (L + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹) := by ring
      _ ≤ 2 * 5 := by linarith
      _ = 10 := by norm_num
  calc ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ‖Work.FIArea5.S16.fcoef q ℓ‖
      ≤ ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
          (1 / (2 * Real.pi)) * (10000000 * θ * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) :=
        Finset.sum_le_sum
          (fun ℓ _ => Work.FIArea5.S16.fcoef_bound q θ hθ hθ1 hqC hq0 hq1 hqsupp hd2 ℓ)
    _ = (1 / (2 * Real.pi)) * 10000000
          * (θ * ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ℓ _
        ring
    _ ≤ (1 / (2 * Real.pi)) * 10000000 * 10 :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ 100000000 := by
        have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
        have hinv : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
          rw [div_le_iff₀ hpos]
          nlinarith [Real.pi_gt_three]
        have h3 := mul_le_mul_of_nonneg_right hinv
          (show (0 : ℝ) ≤ (10000000 : ℝ) * 10 by norm_num)
        linarith

end Work.FIArea6
