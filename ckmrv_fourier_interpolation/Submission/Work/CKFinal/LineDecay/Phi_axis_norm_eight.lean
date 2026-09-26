import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

/-- `‖(t i) ^ 2‖ = t ^ 2` for `t > 0` (the exponent `8/2 - 2` arising in dimension 8). -/
private lemma norm_I_mul_zpow_two (t : ℝ) (ht : 0 < t) :
    ‖((t : ℂ) * Complex.I) ^ (2 : ℤ)‖ = t ^ 2 := by
  rw [norm_zpow,
    show ‖(t : ℂ) * Complex.I‖ = t from by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le],
    zpow_ofNat]

/-- **The pointwise norm bound for `Φ` on the imaginary axis, in dimension 8.**

On `z = i t` (`t > 0`) the second difference of the kernel `K^{(8)}` and of the hatted kernel
`K̂^{(8)}` are both bounded by `t ^ 2 * (‖K₊(τ, i/t)‖ + ‖K₋(τ, i/t)‖)`, where `i/t = S • (i t)`.
This is the dimension-8 analogue of `Work.CKFinal.LineDecay.Phi_axis_norm_twentyfour` (where the
exponent is `10`); the proof is the pair of identities `Work.CKFinal.Phi_axis_eq` and
`Work.CKFinal.PhiHat_axis_eq` evaluated on the imaginary axis together with `‖(i t) ^ m‖ = t ^ m`.
It is the missing public dimension-8 counterpart of the private lemma `Phi_axis_norm_le` in
`Phi_tail_bound_eight.lean`. -/
theorem Phi_axis_norm_eight (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    (‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 8) τ t‖
        ≤ t ^ 2 * (‖Work.Kernels.KPlus 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
              + ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖)) ∧
    (‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 8) τ t‖
        ≤ t ^ 2 * (‖Work.Kernels.KPlus 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
              + ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖)) := by
  have ht2 : (0 : ℝ) ≤ t ^ 2 := by positivity
  constructor
  · -- the second difference of the kernel `K^{(8)}`
    have h := Work.CKFinal.Phi_axis_eq ℓ 8 (Or.inl rfl) τ ht
    rw [show (((8 : ℕ) : ℤ) / 2 - 2) = (2 : ℤ) by norm_num] at h
    rw [h, norm_mul, norm_neg, norm_I_mul_zpow_two t ht,
      Work.CKFinal.Kax_zero_inv (Work.Kernels.KPlus 8) τ ht,
      Work.CKFinal.Kax_zero_inv (Work.Kernels.KMinus ℓ 8) τ ht]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) ht2
  · -- the second difference of the hatted kernel `K̂^{(8)}`
    have hh := Work.CKFinal.PhiHat_axis_eq ℓ 8 (Or.inl rfl) τ ht
    rw [show (((8 : ℕ) : ℤ) / 2 - 2) = (2 : ℤ) by norm_num] at hh
    have hPhi : Work.CKFinal.Phi (Work.Kernels.Khat ℓ 8) τ t
        = 2 * Work.CKFinal.Kax (Work.Kernels.Khat ℓ 8) τ 0 t
          - Work.CKFinal.Kax (Work.Kernels.Khat ℓ 8) τ 1 t
          - Work.CKFinal.Kax (Work.Kernels.Khat ℓ 8) τ (-1) t := by
      rw [Work.CKFinal.Phi]; ring
    rw [hPhi, hh, norm_mul, norm_neg, norm_I_mul_zpow_two t ht,
      Work.CKFinal.Kax_zero_inv (Work.Kernels.KPlus 8) τ ht,
      Work.CKFinal.Kax_zero_inv (Work.Kernels.KMinus ℓ 8) τ ht]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) ht2

end

end Work.CKFinal.LineDecay
