import Mathlib
import Submission.Work.CKFinal.LineDecay.PhiAxis

/-!
# The pointwise norm bound for `Φ` on the imaginary axis, in dimension 24

This file proves `Work.CKFinal.LineDecay.Phi_axis_norm_twentyfour`: on the imaginary axis
`z = i t`, the second difference `Φ` of the kernel `K^{(24)}` and the second difference `Φ` of the
hatted kernel `K̂` are both bounded by

`t ^ 10 * (‖K₊(τ, i/t)‖ + ‖K₋(τ, i/t)‖),`

where `i/t = S • (i t)`.

The input is the pair of identities `Work.CKFinal.Phi_axis_eq` and
`Work.CKFinal.PhiHat_axis_eq` (CKMRV Proposition 4.10 in the second variable, evaluated on the
imaginary axis):

* `Φ(K^{(d)}, τ, t) = -(i t)^{d/2-2} (K₊(τ,i/t) - K₋(τ,i/t))`,
* `2K̂(τ,i t) - K̂(τ,i t+1) - K̂(τ,i t-1) = -(i t)^{d/2-2} (K₊(τ,i/t) + K₋(τ,i/t))`,

together with `‖(i t)^m‖ = t^m` for `t > 0`.  For `d = 24` the exponent is `10`
(whereas for `d = 8` it is `2`, cf. the private lemma `Phi_axis_norm_le` of
`Phi_tail_bound_eight`).
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

/-- `‖(i t) ^ m‖ = t ^ m` for `t > 0`, `m` a natural number. -/
private lemma norm_I_mul_pow (t : ℝ) (ht : 0 < t) (m : ℕ) :
    ‖((t : ℂ) * Complex.I) ^ m‖ = t ^ m := by
  rw [norm_pow,
    show ‖(t : ℂ) * Complex.I‖ = t from by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le]]

/-- `‖(i t) ^ (24/2 - 2)‖ = t ^ 10` for `t > 0`. -/
private lemma norm_I_mul_zpow_twentyfour (t : ℝ) (ht : 0 < t) :
    ‖((t : ℂ) * Complex.I) ^ (((24 : ℕ) : ℤ) / 2 - 2)‖ = t ^ 10 := by
  rw [show (((24 : ℕ) : ℤ) / 2 - 2) = (10 : ℤ) by norm_num, norm_zpow,
    show ‖(t : ℂ) * Complex.I‖ = t from by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le],
    zpow_ofNat]

theorem Phi_axis_norm_twentyfour (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    (‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 24) τ t‖
        ≤ t ^ 10 * (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
              + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖)) ∧
    (‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 24) τ t‖
        ≤ t ^ 10 * (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
              + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖)) := by
  have ht2 : (0 : ℝ) ≤ t ^ 10 := by positivity
  constructor
  · -- the `K`-second difference
    have h := Work.CKFinal.Phi_axis_eq ℓ 24 (Or.inr rfl) τ ht
    rw [h, norm_mul, norm_neg, norm_I_mul_zpow_twentyfour t ht,
      Work.CKFinal.Kax_zero_inv (Work.Kernels.KPlus 24) τ ht,
      Work.CKFinal.Kax_zero_inv (Work.Kernels.KMinus ℓ 24) τ ht]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) ht2
  · -- the `K̂`-second difference
    have hh := Work.CKFinal.PhiHat_axis_eq ℓ 24 (Or.inr rfl) τ ht
    have hPhi : Work.CKFinal.Phi (Work.Kernels.Khat ℓ 24) τ t
        = 2 * Work.CKFinal.Kax (Work.Kernels.Khat ℓ 24) τ 0 t
          - Work.CKFinal.Kax (Work.Kernels.Khat ℓ 24) τ 1 t
          - Work.CKFinal.Kax (Work.Kernels.Khat ℓ 24) τ (-1) t := by
      rw [Work.CKFinal.Phi]; ring
    rw [hPhi, hh, norm_mul, norm_neg, norm_I_mul_zpow_twentyfour t ht,
      Work.CKFinal.Kax_zero_inv (Work.Kernels.KPlus 24) τ ht,
      Work.CKFinal.Kax_zero_inv (Work.Kernels.KMinus ℓ 24) τ ht]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) ht2

end

end Work.CKFinal.LineDecay
