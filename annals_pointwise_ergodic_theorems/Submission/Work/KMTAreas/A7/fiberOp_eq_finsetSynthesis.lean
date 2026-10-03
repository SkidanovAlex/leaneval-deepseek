import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

/-- The fibre `fiberOp ρ l φ n₀ f` is the Fourier synthesis in the arithmetic frequencies
`(ℚ/ℤ)_l`: distributing the finite sum over `(ℚ/ℤ)_l` (using `e_{n₀-j} = e_{n₀}·e_{-j}` and the
interchange of the finite sum with the absolutely convergent convolution sum) writes it as
`∑_{α ∈ (ℚ/ℤ)_l} e_{n₀}(α) · ∑_j e_{-j}(α) · cw φ j · f(x-j)`, i.e. as the synthesis of the
frequency projections of the multiplier `cw φ`. -/
theorem fiberOp_eq_finsetSynthesis (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ)
    (hφsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw φ j‖))
    (f : ℤ → ℂ) (B : ℝ) (hB : ∀ x : ℤ, ‖f x‖ ≤ B) (n₀ : ℤ) (x : ℤ) :
    Work.KMTAreas.A7.fiberOp ρ l φ n₀ f x
      = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
          fourier (T := 1) n₀ α *
            (∑' j : ℤ, fourier (T := 1) (-j) α
              * Work.KMTAreas.A7.cw φ j * f (x - j)) := by
  rw [Work.KMTAreas.A7.fiberOp]
  -- `e_{n₀-j} = e_{n₀} · e_{-j}`, then distribute the finite sum over the convolution sum.
  have key : ∀ j : ℤ,
      (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)
          * Work.KMTAreas.A7.cw φ j * f (x - j)
        = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
            fourier (T := 1) n₀ α
              * (fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw φ j * f (x - j)) := by
    intro j
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro α _
    rw [sub_eq_add_neg, fourier_add]
    ring
  rw [tsum_congr key]
  -- interchange the finite sum over `(ℚ/ℤ)_l` with the (absolutely convergent) `j`-sum.
  rw [Summable.tsum_finsetSum
    (s := Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l) ?_]
  · refine Finset.sum_congr rfl ?_
    intro α _
    rw [tsum_mul_left]
  · intro α _
    refine Summable.mul_left _ (Summable.of_norm_bounded (hφsum.mul_right B) (fun j => ?_))
    have h1 : ‖fourier (T := 1) (-j) α‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    calc ‖fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw φ j * f (x - j)‖
        = ‖Work.KMTAreas.A7.cw φ j‖ * ‖f (x - j)‖ := by
          rw [mul_assoc, norm_mul, h1, one_mul, norm_mul]
      _ ≤ ‖Work.KMTAreas.A7.cw φ j‖ * B :=
          mul_le_mul_of_nonneg_left (hB (x - j)) (norm_nonneg _)

end Work.KMTAreas.A7
