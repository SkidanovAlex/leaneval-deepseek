/-
# The middle-range dominance for the contour integrand (seam (ii))

`Work.Asymptotics.contour_bound_Kfun` and `Work.Asymptotics.divisor_lower_compact` combine into a
uniform bound for `contourIntegrand` on the middle range `[δ, 1/δ]`: dividing the former by the
latter's lower bound and using `scale (i t) = 1 + 1/t + t ≤ 1 + 2/δ` gives a constant.
-/
import Mathlib
import Submission.Work.Asymptotics.Basic
import Submission.Work.Asymptotics.Instances
import Submission.Work.Asymptotics.divisor_lower_compact
import Submission.Work.Kernels.Theorem31

set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.InteriorDD

open Work.Asymptotics Work.Kernels

/-- `scale (i t) = 1 + 1/t + t`. -/
lemma scale_imagAxis (t : ℝ) (ht : 0 < t) :
    Work.Kernels.scale (Work.Kernels.imagAxis t ht) = 1 + t⁻¹ + t := by
  have him : (Work.Kernels.imagAxis t ht).im = t := by
    rw [← UpperHalfPlane.coe_im]
    simp [Work.Kernels.imagAxis]
  have hcoe : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [Work.Kernels.scale, him, hcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht]

/-- **The middle-range dominance.** -/
theorem norm_contourIntegrand_le_of_divisor (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    {δ : ℝ} (hδ : 0 < δ) {S : ℝ} (hS : ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R →
      Work.Kernels.scale τ ≤ S)
    (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      dist τ τ₀ ≤ R → δ ≤ t → t ≤ 1 / δ →
      ‖contourIntegrand (Work.Kernels.Kfun ℓ d) r (τ : ℂ) t‖ ≤ C := by
  obtain ⟨α, N, M, hα, hN, hM, hbound⟩ := contour_bound_Kfun ℓ d hd
  obtain ⟨c, hcpos, hclower⟩ := divisor_lower_compact hd hR hclean hδ
  have hSpos : 0 < S :=
    lt_of_lt_of_le (by linarith [Work.Kernels.one_le_scale τ₀])
      (hS τ₀ (by rw [dist_self]; exact hR.le))
  have hC0 : 0 ≤ α * S ^ N * (1 + 2 / δ) ^ M :=
    mul_nonneg (mul_nonneg hα (Real.rpow_nonneg hSpos.le N))
      (Real.rpow_nonneg (by linarith [div_pos (by norm_num : (0:ℝ) < 2) hδ]) M)
  have hC : 0 ≤ α * S ^ N * (1 + 2 / δ) ^ M / c := div_nonneg hC0 hcpos.le
  refine ⟨α * S ^ N * (1 + 2 / δ) ^ M / c, hC, fun τ t ht hτ hδt htδ => ?_⟩
  have hdiv : c ≤ ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ :=
    hclower τ t ht hτ hδt htδ
  have hK := hbound τ t ht
  have hst : Work.Kernels.scale τ ≤ S := hS τ hτ
  have hsc : Work.Kernels.scale (Work.Kernels.imagAxis t ht) ≤ 1 + 2 / δ := by
    rw [scale_imagAxis t ht]
    have htinv : t⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ ht hδ).mpr hδt
    have htle : t ≤ δ⁻¹ := by rw [one_div δ] at htδ; exact htδ
    have h2 : (2 : ℝ) / δ = 2 * δ⁻¹ := by rw [div_eq_mul_inv]
    rw [h2]; linarith
  have hSpow : Work.Kernels.scale τ ^ N ≤ S ^ N :=
    Real.rpow_le_rpow (by linarith [Work.Kernels.one_le_scale τ]) hst hN
  have hcM : Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M ≤ (1 + 2 / δ) ^ M :=
    Real.rpow_le_rpow
      (by linarith [Work.Kernels.one_le_scale (Work.Kernels.imagAxis t ht)]) hsc hM
  have hratio : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
      ≤ α * S ^ N * (1 + 2 / δ) ^ M / c := by
    rw [le_div_iff₀ hcpos]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * c
        ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
            * ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ :=
          mul_le_mul_of_nonneg_left hdiv (norm_nonneg _)
      _ ≤ α * Work.Kernels.scale τ ^ N
            * Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M := hK
      _ ≤ α * S ^ N * (1 + 2 / δ) ^ M := by
          have h2 : α * Work.Kernels.scale τ ^ N ≤ α * S ^ N :=
            mul_le_mul_of_nonneg_left hSpow hα
          have h3 := mul_le_mul h2 hcM
            (Real.rpow_nonneg (by linarith [Work.Kernels.one_le_scale (Work.Kernels.imagAxis t ht)]) M)
            (mul_nonneg hα (Real.rpow_nonneg hSpos.le N))
          simpa only [mul_assoc] using h3
  have hexp : ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.mpr ?_
    have hre : (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))).re = -(Real.pi * r ^ 2 * t) := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        ← Complex.ofReal_pow, mul_zero, sub_zero]
    rw [hre]
    have h0 : (0 : ℝ) ≤ Real.pi * r ^ 2 * t := by positivity
    linarith
  rw [contourIntegrand, norm_mul, contourKernel,
    UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos]
  calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
        * ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
      ≤ α * S ^ N * (1 + 2 / δ) ^ M / c * 1 :=
        mul_le_mul hratio hexp (norm_nonneg _) (by simpa using hC)
    _ = α * S ^ N * (1 + 2 / δ) ^ M / c := by ring

end Work.LayerCont.InteriorDD
