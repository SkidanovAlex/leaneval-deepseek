import Mathlib
import Submission.Work.GM.Affine.fine_setup

/-!
# Domination of the dilated smoothing kernel (GM §9)

The smoothing kernel `ψ = psiSmooth` of GM Lemma 9.2 is the `L¹`-normalised bump
`ψ = psiBump.normed volume`; all that is used below are its general `ContDiffBump` properties:

* `ψ ≥ 0`;
* `ψ x ≤ 1 / ∫ ψ` for every `x`, with equality on `|x| ≤ 1/8`;
* `ψ x = 0` for `|x| ≥ 1/4`.

The lemma proved here, `rho_kernel_domination`, bounds the dilated kernel
`u ↦ (m/λ) ψ((m/λ) u)` (with `λ = M₂/(2 K T)` and `m ∈ R2 M₂`, so that
`2 K T < m/λ ≤ 4 K T`) by `4 K T · T ψ(T u)`.

The point is that the two arguments differ by the factor `(m/λ)/T = 2 K m/M₂ > 16`:
since `16 |Tu| ≤ |(m/λ) u|`, either `|Tu| ≤ 1/8` and `ψ(Tu)` is the maximal value
`1/∫ψ ≥ ψ((m/λ)u)`, or `|(m/λ)u| > 2 > 1/4` and `ψ((m/λ)u) = 0`.
-/

open MeasureTheory

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The integral of the smoothing bump is positive. -/
lemma rho_psiBump_integral_pos : 0 < ∫ y, psiBump y :=
  ContDiffBump.integral_pos (f := psiBump) (μ := volume)

/-- The normalised bump is bounded by `1/∫ ψ`. -/
lemma rho_psiSmooth_le_inv_integral (x : ℝ) :
    psiSmooth x ≤ 1 / ∫ y, psiBump y := by
  have h1 : psiBump x ≤ 1 := ContDiffBump.le_one (f := psiBump) (x := x)
  rw [psiSmooth, ContDiffBump.normed_def]
  exact div_le_div_of_nonneg_right h1 rho_psiBump_integral_pos.le

/-- On `|y| ≤ 1/8` the normalised bump attains its maximal value `1/∫ ψ`. -/
lemma rho_psiSmooth_eq_inv_integral {y : ℝ} (hy : |y| ≤ 1 / 8) :
    psiSmooth y = 1 / ∫ z, psiBump z := by
  have h1 : psiBump y = 1 :=
    ContDiffBump.one_of_mem_closedBall (f := psiBump) (by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact hy)
  rw [psiSmooth, ContDiffBump.normed_def, h1]

/-- The normalised bump vanishes on `|x| ≥ 1/4`. -/
lemma rho_psiSmooth_zero_of_quarter_le_abs {x : ℝ} (hx : 1 / 4 ≤ |x|) :
    psiSmooth x = 0 := by
  by_contra h
  have hmem : x ∈ Function.support (psiBump.normed volume) := by
    rw [Function.mem_support]
    exact h
  rw [ContDiffBump.support_normed_eq] at hmem
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
  have hr : psiBump.rOut = (1 : ℝ) / 4 := rfl
  linarith [hmem]

/-- Comparison of two dilates of the kernel: if `16 |y| ≤ |x|` then `ψ x ≤ ψ y`. -/
lemma rho_psiSmooth_le_of_sixteen_mul_le {x y : ℝ} (h : 16 * |y| ≤ |x|) :
    psiSmooth x ≤ psiSmooth y := by
  by_cases hy : |y| ≤ 1 / 8
  · rw [rho_psiSmooth_eq_inv_integral hy]
    exact rho_psiSmooth_le_inv_integral x
  · have hx : 1 / 4 ≤ |x| := by
      rw [not_le] at hy
      nlinarith [abs_nonneg y]
    rw [rho_psiSmooth_zero_of_quarter_le_abs hx]
    exact psiSmooth_nonneg y

theorem rho_kernel_domination {K T M₂ : ℝ} (hT : 1 ≤ T) (hK : 8 ≤ K) (hM₂ : 1 ≤ M₂)
    {m : ℤ} (hm : m ∈ R2 M₂) (u : ℝ) :
    ((m : ℝ) / (M₂ / (2 * K * T))) * psiSmooth ((m : ℝ) * u / (M₂ / (2 * K * T)))
      ≤ 4 * K * (T * psiSmooth (T * u)) := by
  obtain ⟨hmem, hmlt⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hmem
  have hTpos : 0 < T := by linarith
  have hKpos : 0 < K := by linarith
  have hM₂pos : 0 < M₂ := by linarith
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmpos : 0 < (m : ℝ) := by linarith
  have hmltR : M₂ < (m : ℝ) := hmlt
  have hm2R : (m : ℝ) ≤ 2 * M₂ := by
    have hcast : (m : ℝ) ≤ ((⌊2 * M₂⌋ : ℤ) : ℝ) := by exact_mod_cast hm2
    have hfloor : ((⌊2 * M₂⌋ : ℤ) : ℝ) ≤ 2 * M₂ := Int.floor_le (2 * M₂)
    linarith
  set c : ℝ := M₂ / (2 * K * T) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hApos : 0 < (m : ℝ) / c := by positivity
  have h2KT : 0 < 2 * K * T := by positivity
  -- `m / c ≤ 4 K T`
  have hAle : (m : ℝ) / c ≤ 4 * K * T := by
    rw [hc, div_div_eq_mul_div, div_le_iff₀ hM₂pos]
    have h := mul_le_mul_of_nonneg_right hm2R h2KT.le
    nlinarith [h]
  -- `16 T ≤ m / c`
  have hAge : 16 * T ≤ (m : ℝ) / c := by
    rw [hc, div_div_eq_mul_div, le_div_iff₀ hM₂pos]
    have h1 : 16 * T * M₂ ≤ 2 * K * T * M₂ := by
      have hK16 : (16 : ℝ) ≤ 2 * K := by linarith
      have hTM : 0 ≤ T * M₂ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hK16 hTM]
    have h2 : 2 * K * T * M₂ < 2 * K * T * (m : ℝ) := by
      have h := mul_lt_mul_of_pos_left hmltR h2KT
      linarith
    linarith
  -- the two kernels are compared at arguments differing by a factor `> 16`
  have hxform : (m : ℝ) * u / c = ((m : ℝ) / c) * u := by ring
  have hψ : psiSmooth ((m : ℝ) * u / c) ≤ psiSmooth (T * u) := by
    apply rho_psiSmooth_le_of_sixteen_mul_le
    have key : 16 * |T * u| ≤ |((m : ℝ) / c) * u| := by
      rw [abs_mul, abs_mul, abs_of_pos hTpos, abs_of_nonneg hApos.le]
      nlinarith [hAge, abs_nonneg u]
    rw [hxform]
    exact key
  calc ((m : ℝ) / c) * psiSmooth ((m : ℝ) * u / c)
      ≤ ((m : ℝ) / c) * psiSmooth (T * u) := mul_le_mul_of_nonneg_left hψ hApos.le
    _ ≤ (4 * K * T) * psiSmooth (T * u) :=
        mul_le_mul_of_nonneg_right hAle (psiSmooth_nonneg _)
    _ = 4 * K * (T * psiSmooth (T * u)) := by ring

end

end Work.GM.Affine
