/-
# The weighted `r`-seminorm bound for the CKMRV Gaussian `gaussTerm`

Hypothesis (3) of CKMRV Theorem 3.1 (Cohn--Kumar--Miller--Radchenko--Viazovska,
Ann. of Math. 196 (2022)) asks, for the Gaussian term `gaussTerm τ s = e^{π i τ s²}` of the
generating function (5.2), that for every pair of orders `k l` there are constants `C, N ≥ 0`
with

  `|r|^k ‖∂_s^l gaussTerm τ s‖_{s = r} ≤ C · (S τ)^N`   for all `τ ∈ ℍ`, `r ∈ ℝ`,

where `S τ = 1 + (im τ)⁻¹ + ‖τ‖` is the moderate-growth scale.

The estimate is the product of two independent estimates:

* `Work.CKFinal.gaussTerm_iteratedDeriv_bound` bounds the `l`-th derivative of `gaussTerm τ`
  by `A (S τ)^B (1+|r|)^l e^{-π (im τ) r²}` (decay of the Gaussian in `r`);
* `Work.CKFinal.gauss_weight_scale_bound` bounds `|r|^k (1+|r|)^l e^{-π (im τ) r²}` by a
  constant times a power of `S τ`.

Multiplying and combining the scale powers with `Real.rpow_add` gives the claim.
-/
import Mathlib
import Submission.Work.Kernels.Theorem31
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.CKFinal.gauss_weight_scale_bound
import Submission.Work.CKFinal.gaussTerm_iteratedDeriv_bound

namespace Work.CKFinal

theorem iteratedDeriv_gaussTerm_scale_bound :
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
