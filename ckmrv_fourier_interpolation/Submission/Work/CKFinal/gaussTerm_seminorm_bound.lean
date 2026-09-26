import Mathlib
import Submission.Work.Kernels.Theorem31
import Submission.Work.Asymptotics.gaussian_bound
import Submission.Work.Asymptotics.abs_pow_mul_exp_le
import Submission.Work.CKFinal.gauss_weight_scale_bound
import Submission.Work.CKFinal.gaussTerm_iteratedDeriv_bound

/-!
# The weighted `r`-seminorm bound for the CKMRV Gaussian `gaussTerm`

The generating function `F = gaussTerm + kernelTransform` of CKMRV (Cohn--Kumar--Miller--
Radchenko--Viazovska, Ann. of Math. 196 (2022), (5.2)) has the Gaussian term
`gaussTerm τ s = e^{π i τ s²}`.  Hypothesis (3) of Theorem 3.1 requires, for every pair of
orders `k l`, a bound

  `|r|^k ‖∂_s^l gaussTerm τ s‖_{s = r} ≤ C · (S τ)^N`,

uniform in `r ∈ ℝ` and polynomial in the scale `S τ = 1 + (im τ)⁻¹ + ‖τ‖`.

The estimate splits into two independent factors:

* `Work.CKFinal.gaussTerm_iteratedDeriv_bound` bounds the `l`-th derivative of `gaussTerm τ`
  by `A (S τ)^B (1+|r|)^l e^{-π (im τ) r²}` (the decay of the Gaussian in `r`);
* `Work.CKFinal.gauss_weight_scale_bound` bounds the weighted Gaussian
  `|r|^k (1+|r|)^l e^{-π (im τ) r²}` by a constant times a power of `S τ` (the maximum of a
  polynomial times a Gaussian, whose height as `im τ → 0⁺` is exactly a power of the scale).

Multiplying the two and combining the scale powers with `Real.rpow_add` gives the claim.
-/

namespace Work.CKFinal

theorem gaussTerm_seminorm_bound :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N := by
  intro k l
  obtain ⟨A, B, hA0, hB0, hA⟩ := gaussTerm_iteratedDeriv_bound l
  obtain ⟨C, N, hC0, hN0, hG⟩ := gauss_weight_scale_bound k l
  refine ⟨A * C, B + N, by positivity, by positivity, ?_⟩
  intro τ r
  have hAB : (0 : ℝ) ≤ A * (Work.Kernels.scale τ) ^ B :=
    mul_nonneg hA0 (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le B)
  have h1 : |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r‖
      ≤ A * (Work.Kernels.scale τ) ^ B
        * (|r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * τ.im * r ^ 2))) := by
    calc |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r‖
        ≤ |r| ^ k * (A * (Work.Kernels.scale τ) ^ B * (1 + |r|) ^ l
            * Real.exp (-(Real.pi * τ.im * r ^ 2))) :=
          mul_le_mul_of_nonneg_left (hA τ r) (by positivity)
      _ = A * (Work.Kernels.scale τ) ^ B
        * (|r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * τ.im * r ^ 2))) := by ring
  have h2 : A * (Work.Kernels.scale τ) ^ B
        * (|r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * τ.im * r ^ 2)))
      ≤ A * (Work.Kernels.scale τ) ^ B * (C * (Work.Kernels.scale τ) ^ N) :=
    mul_le_mul_of_nonneg_left (hG τ r) hAB
  have h3 : A * (Work.Kernels.scale τ) ^ B * (C * (Work.Kernels.scale τ) ^ N)
      = (A * C) * (Work.Kernels.scale τ) ^ (B + N) := by
    rw [Real.rpow_add (Work.Kernels.scale_pos τ)]
    ring
  calc |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r‖
      ≤ A * (Work.Kernels.scale τ) ^ B
        * (|r| ^ k * (1 + |r|) ^ l * Real.exp (-(Real.pi * τ.im * r ^ 2))) := h1
    _ ≤ A * (Work.Kernels.scale τ) ^ B * (C * (Work.Kernels.scale τ) ^ N) := h2
    _ = (A * C) * (Work.Kernels.scale τ) ^ (B + N) := h3

end Work.CKFinal
