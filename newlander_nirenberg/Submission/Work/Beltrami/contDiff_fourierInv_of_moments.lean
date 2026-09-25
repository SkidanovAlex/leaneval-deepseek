import Mathlib

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff FourierTransform

/-- The Japanese-bracket weight `(1 + ‖x‖²)^{-2}` in (real) dimension two is the square of the
reciprocal weight `(1 + ‖x‖²)⁻¹`, written with an `rpow` exponent so that
`integrable_rpow_neg_one_add_norm_sq` applies. -/
private lemma rpow_neg_half4 (x : ℝ) : x ^ (-(4:ℝ)/2) = (x⁻¹)^2 := by
  rw [show (-(4:ℝ)/2) = -(2:ℝ) by norm_num, Real.rpow_neg_eq_inv_rpow]
  norm_num

/-- The reciprocal Japanese-bracket weight `(1 + ‖ξ‖²)⁻¹` on `ℂ ≅ ℝ²` is square integrable: its
square is `(1 + ‖ξ‖²)^(-4/2)` and the exponent `4` exceeds the real dimension `2`. -/
private lemma memLp_inv_one_add_norm_sq :
    MemLp (fun ξ : ℂ => ((1 + ‖ξ‖ ^ 2 : ℝ))⁻¹) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun ξ : ℂ => ((1 + ‖ξ‖ ^ 2 : ℝ))⁻¹) volume := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have h1 : Integrable (fun ξ : ℂ => ((1 + ‖ξ‖ ^ 2 : ℝ)) ^ (-(4:ℝ)/2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)
  refine h1.congr ?_
  filter_upwards with ξ
  exact rpow_neg_half4 _

/-- **Moment integrability.** If every polynomial moment of `V ∈ L²(ℂ)` lies again in `L²`, then
every polynomial moment of `V` lies in `L¹`: `‖ξ‖ ^ n * ‖V ξ‖` is integrable.

Factor `‖ξ‖ ^ n * ‖V ξ‖ = (1+‖ξ‖²)⁻¹ · ‖(1+‖ξ‖²)^{n+1} · V ξ‖`: the first factor is in `L²`
(`memLp_inv_one_add_norm_sq`), the second is the norm of an `L²` function (`hmom (n+1)`), so the
product is in `L¹` (`MemLp.mul`, Hölder `2,2,1`), and it dominates `‖ξ‖ ^ n * ‖V ξ‖` pointwise
since `‖ξ‖ ≤ 1 + ‖ξ‖²`. -/
private lemma integrable_moment_of_memLp_weights {V : Lp ℂ 2 volume}
    (hmom : ∀ N : ℕ, MemLp (fun ξ : ℂ => (1 + ‖ξ‖ ^ 2) ^ N * V ξ) 2 volume) (n : ℕ) :
    Integrable (fun ξ : ℂ => ‖ξ‖ ^ n * ‖V ξ‖) := by
  have h2 : MemLp (fun ξ : ℂ => ‖(1 + ‖ξ‖ ^ 2) ^ (n+1) * V ξ‖) 2 volume :=
    (hmom (n+1)).norm
  have hprod : MemLp (fun ξ : ℂ =>
      ((1 + ‖ξ‖ ^ 2 : ℝ))⁻¹ * ‖(1 + ‖ξ‖ ^ 2) ^ (n+1) * V ξ‖) 1 volume :=
    memLp_inv_one_add_norm_sq.mul h2
  have hint : Integrable (fun ξ : ℂ =>
      ((1 + ‖ξ‖ ^ 2 : ℝ))⁻¹ * ‖(1 + ‖ξ‖ ^ 2) ^ (n+1) * V ξ‖) :=
    memLp_one_iff_integrable.mp hprod
  refine hint.mono' ?_ ?_
  · exact ((continuous_norm.pow n).aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable V).norm)
  · filter_upwards with ξ
    have hb : (0:ℝ) < 1 + ‖ξ‖^2 := by positivity
    have hbase : ((1:ℂ) + ↑‖ξ‖^2) = ((1 + ‖ξ‖^2 : ℝ) : ℂ) := by push_cast; ring
    have hnorm : ‖(1 + ‖ξ‖ ^ 2) ^ (n+1) * V ξ‖ = (1 + ‖ξ‖ ^ 2)^(n+1) * ‖V ξ‖ := by
      rw [hbase, ← Complex.ofReal_pow, ← Complex.real_smul, norm_smul,
        Real.norm_of_nonneg (by positivity)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hnorm, ← mul_assoc]
    have h1 : ((1 + ‖ξ‖ ^ 2 : ℝ))⁻¹ * (1 + ‖ξ‖ ^ 2)^(n+1) = (1 + ‖ξ‖ ^ 2)^n := by
      rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt hb)]
      ring
    rw [h1]
    have hle : ‖ξ‖ ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [norm_nonneg ξ, sq_nonneg (‖ξ‖ - 1)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg ξ) hle n) (norm_nonneg _)

/-- If all polynomial moments of `V : L²(ℂ)` are in `L²`, then the inverse Fourier transform of `V`,
written as the absolutely convergent integral `x ↦ ∫ ξ, e^{2πi⟪ξ,x⟫} V ξ`, is smooth.

Suggested route: `Real.fourierInv_eq` identifies the integrand; `Real.fourierInv_eq_fourier_comp_neg`
turns the goal into `ContDiff ℝ ∞ (𝓕 (fun ξ => V (-ξ)))`. From the moments derive, for every `n`,
`Integrable (fun ξ => ‖ξ‖^n * ‖V ξ‖)` by Cauchy–Schwarz against the weight `(1+‖ξ‖²)^{-k}` for `k`
large (`MemLp.mul`, Hölder triple `2,2,1`), transport to `ξ ↦ V (-ξ)` by `Integrable.comp_neg`, and
apply `Real.contDiff_fourier` (`Analysis/Fourier/FourierTransformDeriv.lean`) with `N = ∞`. -/
theorem contDiff_fourierInv_of_moments {V : Lp ℂ 2 volume}
    (hmom : ∀ N : ℕ, MemLp (fun ξ : ℂ => (1 + ‖ξ‖ ^ 2) ^ N * V ξ) 2 volume) :
    ContDiff ℝ ∞ (fun x : ℂ => ∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ) := by
  have hfun : (fun x : ℂ => ∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ) = 𝓕⁻ (fun ξ : ℂ => V ξ) := by
    funext x
    rw [Real.fourierInv_eq]
  rw [hfun, Real.fourierInv_eq_fourier_comp_neg]
  refine Real.contDiff_fourier (N := (⊤ : ℕ∞)) (fun n _ => ?_)
  have hm : Integrable (fun ξ : ℂ => ‖ξ‖ ^ n * ‖V ξ‖) := integrable_moment_of_memLp_weights hmom n
  simpa [norm_neg] using hm.comp_neg

end Work.Beltrami
