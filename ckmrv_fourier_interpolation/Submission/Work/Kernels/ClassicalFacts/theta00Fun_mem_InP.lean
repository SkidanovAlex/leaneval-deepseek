/-
# `θ₀₀ ∈ 𝒫`

Jacobi's one-variable theta function
`θ₀₀ τ = ∑_{n ∈ ℤ} e^{π i n² τ}` belongs to the class `𝒫 = Work.Kernels.InP` of CKMRV
(Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)): it is holomorphic on
the upper half plane `ℍ` and has moderate growth there.

Holomorphy is Mathlib's `mdifferentiable_jacobiTheta`.

For the growth, Mathlib's estimate `norm_jacobiTheta_sub_one_le` gives, for `y = im τ > 0`,

  `‖θ₀₀ τ - 1‖ ≤ 2 e^{-π y} / (1 - e^{-π y})`.

Since `e^{-u} (e^u - 1) = 1 - e^{-u}` and `e^u - 1 ≥ u` (`Real.add_one_le_exp`), we get

  `2 e^{-u} / (1 - e^{-u}) = 2 / (e^u - 1) * ... ≤ 2 / u`   for `u > 0`,

so with `u = π y`:

  `‖θ₀₀ τ - 1‖ ≤ (2/π) (im τ)⁻¹`   and hence   `‖θ₀₀ τ‖ ≤ (1 + 2/π) ((im τ)⁻¹ + 1)`,

which is a moderate growth bound with exponents `β = 1`, `γ = 0`.  (The presence of the `y⁻¹`
term is essential: `θ₀₀` is *not* bounded on `ℍ`, it behaves like `(-iτ)^{-1/2}` as `im τ → 0⁺`.)
-/
import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.ModerateGrowth

noncomputable section

open UpperHalfPlane

namespace Work.Kernels.ClassicalFacts

/-- The elementary estimate `2 e^{-u} / (1 - e^{-u}) ≤ 2 / u` for `u > 0`.

Indeed `e^{-u} (e^u - 1) = 1 - e^{-u}` and `e^u - 1 ≥ u`, so `e^{-u} u ≤ 1 - e^{-u}`; dividing
by the positive quantities `1 - e^{-u}` and `u` gives the claim. -/
lemma two_mul_exp_neg_div_one_sub_le (u : ℝ) (hu : 0 < u) :
    2 * Real.exp (-u) / (1 - Real.exp (-u)) ≤ 2 / u := by
  have hlt : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-u) := by linarith
  have h1 : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have h2 : Real.exp (-u) * u ≤ 1 - Real.exp (-u) := by
    calc Real.exp (-u) * u ≤ Real.exp (-u) * (Real.exp u - 1) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-u)).le
      _ = 1 - Real.exp (-u) := by
          rw [mul_sub, mul_one, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [div_le_div_iff₀ hden hu]
  linarith

/-- The same estimate in the shape of Mathlib's `norm_jacobiTheta_sub_one_le`, with the
exponential decay expressed in terms of `im τ`: for `y > 0`,

`2 / (1 - e^{-π y}) * e^{-π y} ≤ (2/π) y⁻¹`. -/
lemma two_div_one_sub_mul_exp_neg_pi_le (y : ℝ) (hy : 0 < y) :
    2 / (1 - Real.exp (-Real.pi * y)) * Real.exp (-Real.pi * y) ≤ (2 / Real.pi) * y⁻¹ := by
  have hπ : 0 < Real.pi * y := mul_pos Real.pi_pos hy
  have hmain := two_mul_exp_neg_div_one_sub_le (Real.pi * y) hπ
  have he : -(Real.pi * y) = -Real.pi * y := by ring
  have h2 : 2 / (Real.pi * y) = (2 / Real.pi) * y⁻¹ := by field_simp
  have hgoal : 2 / (1 - Real.exp (-Real.pi * y)) * Real.exp (-Real.pi * y)
      = 2 * Real.exp (-Real.pi * y) / (1 - Real.exp (-Real.pi * y)) := by ring
  rw [hgoal, ← he]
  rw [h2] at hmain
  exact hmain

/-- Jacobi's theta function `θ₀₀ = ∑_{n ∈ ℤ} q^{n²/2}` lies in the class `𝒫 = Work.Kernels.InP`:
it is holomorphic on `ℍ` and of moderate growth there.

Holomorphy is `mdifferentiable_jacobiTheta`.  For the growth, `norm_jacobiTheta_sub_one_le`
bounds `‖θ₀₀ τ - 1‖` by `2 e^{-π y} / (1 - e^{-π y})` with `y = im τ`, and
`two_div_one_sub_mul_exp_neg_pi_le` bounds the latter by `(2/π) y⁻¹`; hence
`‖θ₀₀ τ‖ ≤ (1 + 2/π) (y⁻¹ + 1)`, a moderate growth bound with `β = 1`, `γ = 0`. -/
lemma theta00Fun_mem_InP : Work.Kernels.InP Work.Kernels.theta00Fun := by
  refine ⟨?_, ?_⟩
  · exact mdifferentiable_jacobiTheta
  · refine ⟨1 + 2 / Real.pi, 1, 0, by positivity, by norm_num, le_rfl, fun τ _ => ?_⟩
    have hy : 0 < τ.im := τ.im_pos
    have h := norm_jacobiTheta_sub_one_le (τ := (τ : ℂ)) (by simpa using hy)
    simp only [UpperHalfPlane.coe_im] at h
    have hb := two_div_one_sub_mul_exp_neg_pi_le τ.im hy
    rw [Real.rpow_one, Real.rpow_zero]
    calc ‖Work.Kernels.theta00Fun τ‖
        = ‖jacobiTheta (τ : ℂ)‖ := rfl
      _ ≤ ‖jacobiTheta (τ : ℂ) - 1‖ + 1 := by
            have := norm_add_le (jacobiTheta (τ : ℂ) - 1) (1 : ℂ)
            simpa using this
      _ ≤ 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) + 1 := by
            linarith [h]
      _ ≤ (2 / Real.pi) * (τ.im)⁻¹ + 1 := by linarith [hb]
      _ ≤ (1 + 2 / Real.pi) * ((τ.im)⁻¹ + 1) := by
            have h1 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr hy.le
            have h2 : 0 < (2 / Real.pi) := by positivity
            nlinarith

end Work.Kernels.ClassicalFacts
