/-
# `θ₁₀ ∈ 𝒫`

Jacobi's theta function
`θ₁₀ τ = ∑_{n ∈ ℤ} q^{(n+1/2)²/2}` (with `q = e^{2πiτ}`), realized here as
`θ₁₀ τ = e^{πiτ/4} · jacobiTheta₂ (τ/2) τ`, belongs to the class `𝒫 = Work.Kernels.InP`
of CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)): it is
holomorphic on `ℍ` and has moderate growth there.

Holomorphy.  The exponential prefactor `τ ↦ e^{πiτ/4}` is entire, and
`τ ↦ jacobiTheta₂ (τ/2) τ` is the composite of the complex-linear (in fact holomorphic)
map `τ ↦ (τ/2, τ)` with the two-variable theta function, which is complex differentiable
at every point `(z, τ)` with `im τ > 0` (Mathlib's `hasFDerivAt_jacobiTheta₂`); this
composite is complex differentiable on `ℍ`, hence `MDiff`.

Growth.  Since `‖e^{πiτ/4}‖ = e^{-π im τ/4} ≤ 1`, it suffices to bound
`‖jacobiTheta₂ (τ/2) τ‖`.  Mathlib's `norm_jacobiTheta₂_term` computes
`‖jacobiTheta₂_term n z τ‖ = e^{-π n² im τ - 2π n im z}`, so with `z = τ/2` and `y = im τ`

  `‖jacobiTheta₂ (τ/2) τ‖ ≤ ∑_{n ∈ ℤ} e^{-y (n²+n)} ≤ 2 / (1 - e^{-y})`,

the last step being `Work.Kernels.ClassicalFacts.tsum_int_exp_quad_le` (the involution
`n ↦ -n-1` halves the double-sided sum, and `n² + n ≥ n` for `n ≥ 0` gives a geometric
comparison).  Finally `1 - e^{-y} ≥ y/(1+y)` and `y = π im τ ≥ im τ > 0` give
`2/(1 - e^{-y}) ≤ 2 ((im τ)⁻¹ + 1)`, a moderate growth bound with `β = 1`, `γ = 0`.
-/
import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Kernels.ClassicalFacts.tsum_int_exp_quad_le

noncomputable section

open UpperHalfPlane
open scoped Manifold

namespace Work.Kernels.ClassicalFacts

/-- The two-variable Jacobi theta function is dominated in absolute value by the sum of the
norms of its defining terms: for `0 < im τ`,

`‖jacobiTheta₂ z τ‖ ≤ ∑' n, exp (-(π (im τ) n²) - 2π n (im z))`.

Indeed `‖∑' aₙ‖ ≤ ∑' ‖aₙ‖` (`norm_tsum_le_tsum_norm`) and Mathlib's
`norm_jacobiTheta₂_term` computes `‖jacobiTheta₂_term n z τ‖`. -/
lemma norm_jacobiTheta2_le (z τ : ℂ) (hτ : 0 < τ.im) :
    ‖jacobiTheta₂ z τ‖ ≤
      ∑' n : ℤ, Real.exp (-(Real.pi * τ.im * (n : ℝ) ^ 2) - 2 * Real.pi * (n : ℝ) * z.im) := by
  have hsum : Summable (fun n : ℤ => ‖jacobiTheta₂_term n z τ‖) :=
    ((summable_jacobiTheta₂_term_iff z τ).mpr hτ).norm
  calc ‖jacobiTheta₂ z τ‖ = ‖∑' n : ℤ, jacobiTheta₂_term n z τ‖ := rfl
    _ ≤ ∑' n : ℤ, ‖jacobiTheta₂_term n z τ‖ := norm_tsum_le_tsum_norm hsum
    _ = ∑' n : ℤ, Real.exp (-(Real.pi * τ.im * (n : ℝ) ^ 2) - 2 * Real.pi * (n : ℝ) * z.im) := by
        refine tsum_congr (fun n => ?_)
        rw [norm_jacobiTheta₂_term]
        congr 1
        ring

/-- Specialization of `norm_jacobiTheta2_le` to `z = τ/2`: the two half-integral summands
combine into `exp (-(π (im τ) (n² + n)))`. -/
lemma norm_jacobiTheta2_halve_le (τ : ℍ) :
    ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ ≤
      ∑' n : ℤ, Real.exp (-(Real.pi * τ.im * ((n : ℝ) ^ 2 + (n : ℝ)))) := by
  refine (norm_jacobiTheta2_le ((τ : ℂ) / 2) (τ : ℂ) τ.im_pos).trans (le_of_eq ?_)
  refine tsum_congr (fun n => ?_)
  congr 1
  have him : ((τ : ℂ) / 2).im = τ.im / 2 := by simp
  rw [him]
  simp only [UpperHalfPlane.coe_im]
  ring

/-- The prefactor `exp (π i τ / 4)` of `θ₁₀` has norm at most `1` on `ℍ`. -/
lemma norm_exp_pi_I_div_four_le (τ : ℍ) :
    ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have h : (Real.pi * Complex.I * (τ : ℂ) / 4).re = -(Real.pi * τ.im / 4) := by
    simp; ring
  rw [h]
  have := τ.im_pos
  nlinarith [Real.pi_pos]

/-- The function `θ₁₀ = e^{πiτ/4} · jacobiTheta₂ (τ/2) τ` is holomorphic on `ℍ`. -/
lemma mdifferentiable_theta10Fun : MDiff Work.Kernels.theta10Fun := by
  intro τ
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have heq : (Work.Kernels.theta10Fun ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)]
      (fun z : ℂ => Complex.exp (Real.pi * Complex.I * z / 4) * jacobiTheta₂ (z / 2) z) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  refine (DifferentiableAt.congr_of_eventuallyEq ?_ heq)
  apply DifferentiableAt.mul
  · fun_prop
  · have h1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (((τ : ℂ) / 2), (τ : ℂ)) :=
      (hasFDerivAt_jacobiTheta₂ ((τ : ℂ) / 2) τ.im_pos).differentiableAt
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (z / 2, z)) (τ : ℂ) :=
      ((differentiableAt_id (x := (τ : ℂ))).div_const 2).prodMk differentiableAt_id
    exact DifferentiableAt.comp (f := fun z : ℂ => (z / 2, z)) (τ : ℂ) h1 h2

/-- `θ₁₀ ∈ 𝒫`: `θ₁₀ = e^{πiτ/4} θ(τ/2; τ)` is holomorphic on `ℍ` and of moderate growth
there, with exponents `β = 1`, `γ = 0` and constant `2`. -/
lemma theta10Fun_mem_InP : Work.Kernels.InP Work.Kernels.theta10Fun := by
  refine ⟨mdifferentiable_theta10Fun, ?_⟩
  refine ⟨2, 1, 0, by norm_num, by norm_num, le_rfl, fun τ _ => ?_⟩
  rw [Real.rpow_one, Real.rpow_zero]
  have h1 : ‖Work.Kernels.theta10Fun τ‖ ≤ ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ := by
    calc ‖Work.Kernels.theta10Fun τ‖
        = ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)
            * jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ := rfl
      _ = ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)‖
            * ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ := norm_mul _ _
      _ ≤ 1 * ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ :=
            mul_le_mul_of_nonneg_right (norm_exp_pi_I_div_four_le τ) (norm_nonneg _)
      _ = ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ := one_mul _
  have h2 := norm_jacobiTheta2_halve_le τ
  have h3 := tsum_int_exp_quad_le (Real.pi * τ.im) (by positivity)
  have h4 : 2 / (1 - Real.exp (-(Real.pi * τ.im))) ≤ 2 * ((τ.im)⁻¹ + 1) := by
    have hy : 0 < Real.pi * τ.im := by positivity
    have hden : 0 < 1 - Real.exp (-(Real.pi * τ.im)) := by
      have : Real.exp (-(Real.pi * τ.im)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    -- `y/(1+y) ≤ 1 - e^{-y}` for `y = π im τ > 0`
    have hkey : (Real.pi * τ.im) / (1 + Real.pi * τ.im) ≤ 1 - Real.exp (-(Real.pi * τ.im)) := by
      have h1 : Real.exp (-(Real.pi * τ.im)) * (1 + Real.pi * τ.im) ≤ 1 := by
        have h2 : Real.exp (-(Real.pi * τ.im)) * Real.exp (Real.pi * τ.im) = 1 := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        calc Real.exp (-(Real.pi * τ.im)) * (1 + Real.pi * τ.im)
            ≤ Real.exp (-(Real.pi * τ.im)) * Real.exp (Real.pi * τ.im) := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
              linarith [Real.add_one_le_exp (Real.pi * τ.im)]
          _ = 1 := h2
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + Real.pi * τ.im)]
      linarith
    have hkey2 : (1 - Real.exp (-(Real.pi * τ.im)))⁻¹ ≤ (τ.im)⁻¹ + 1 := by
      have hpos1 : 0 < Real.pi * τ.im / (1 + Real.pi * τ.im) := div_pos hy (by positivity)
      have h5 : (1 - Real.exp (-(Real.pi * τ.im)))⁻¹
          ≤ (Real.pi * τ.im / (1 + Real.pi * τ.im))⁻¹ :=
        (inv_le_inv₀ hden hpos1).mpr hkey
      calc (1 - Real.exp (-(Real.pi * τ.im)))⁻¹
            ≤ (Real.pi * τ.im / (1 + Real.pi * τ.im))⁻¹ := h5
        _ = (Real.pi * τ.im)⁻¹ + 1 := by
              rw [inv_div, add_div, div_self (ne_of_gt hy), one_div]
        _ ≤ (τ.im)⁻¹ + 1 := by
              have hle : (Real.pi * τ.im)⁻¹ ≤ (τ.im)⁻¹ := by
                rw [inv_le_inv₀ (by positivity) τ.im_pos]
                nlinarith [Real.pi_gt_three, τ.im_pos]
              linarith
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hkey2 (by norm_num)
  linarith

end Work.Kernels.ClassicalFacts
