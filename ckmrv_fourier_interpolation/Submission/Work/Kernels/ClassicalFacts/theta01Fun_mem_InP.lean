/-
# `θ₀₁ ∈ 𝒫`

Jacobi's theta function
`θ₀₁ τ = ∑_{n ∈ ℤ} (-1)^n e^{π i n² τ}`
belongs to the class `𝒫 = Work.Kernels.InP` of CKMRV
(Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)): it is holomorphic on
the upper half plane `ℍ` and has moderate growth there.

The whole content is the elementary identity

  `θ₀₁ τ = θ₀₀ (τ + 1)`   (`jacobiTheta (τ + 1)`, in Mathlib's normalisation),

valid because the sign `(-1)^n` in the summand is exactly the factor `e^{π i n²}` picked up by
shifting `τ` to `τ + 1`, and `n² ≡ n (mod 2)`.  Since `τ + 1` has the same imaginary part as `τ`,
Mathlib's estimate `norm_jacobiTheta_sub_one_le` for `θ₀₀ - 1` applies verbatim and yields the
growth bound `‖θ₀₁ τ‖ ≤ (1 + 2 / π) ((im τ)⁻¹ + 1)`.

Holomorphy is `differentiableAt_jacobiTheta₂_snd` (differentiability of the two-variable theta
function in its second variable).
-/
import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.ModerateGrowth

noncomputable section

open UpperHalfPlane
open scoped Manifold

namespace Work.Kernels.ClassicalFacts

/-! ## The identity `θ₀₁ τ = θ₀₀ (τ + 1)` -/

/-- The elementary parity identity `e^{π i n} = e^{π i n²}` for integers `n`: both sides are
`(-1)^n`, since `n² - n` is even. -/
private lemma exp_pi_I_int_eq_exp_pi_I_int_sq (n : ℤ) :
    Complex.exp (Real.pi * Complex.I * (n : ℂ))
      = Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2) := by
  obtain ⟨m, hm⟩ : Even (n ^ 2 - n) := by
    have hh : n ^ 2 - n = n * (n - 1) := by ring
    rw [hh]; exact Int.even_mul_pred_self n
  have hcast : ((n ^ 2 - n : ℤ) : ℂ) = (m : ℂ) + (m : ℂ) := by
    rw [hm]; push_cast; ring
  have hdiff : (n : ℂ) ^ 2 - (n : ℂ) = ((n ^ 2 - n : ℤ) : ℂ) := by push_cast; ring
  have key : Real.pi * Complex.I * (n : ℂ) ^ 2
      = Real.pi * Complex.I * (n : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [show (Real.pi * Complex.I * (n : ℂ) ^ 2 : ℂ)
          = Real.pi * Complex.I * ((n : ℂ) + ((n : ℂ) ^ 2 - (n : ℂ))) by ring,
      mul_add, hdiff, hcast]
    ring
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I m, mul_one]

/-- The summands of `θ₀₁` at `z = 1/2` agree, term by term, with those of `θ₀₀` at `τ + 1`. -/
private lemma jacobiTheta₂_term_half (n : ℤ) (τ : ℂ) :
    jacobiTheta₂_term n (1/2) τ = jacobiTheta₂_term n 0 (τ + 1) := by
  have h := exp_pi_I_int_eq_exp_pi_I_int_sq n
  rw [jacobiTheta₂_term, jacobiTheta₂_term]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (1/2)
        + Real.pi * Complex.I * (n : ℂ) ^ 2 * τ)
      = (Real.pi * Complex.I * (n : ℂ) + Real.pi * Complex.I * (n : ℂ) ^ 2 * τ) by ring]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * 0
        + Real.pi * Complex.I * (n : ℂ) ^ 2 * (τ + 1))
      = (Real.pi * Complex.I * (n : ℂ) ^ 2 * τ + Real.pi * Complex.I * (n : ℂ) ^ 2) by ring]
  rw [Complex.exp_add, Complex.exp_add, h, mul_comm]

/-- `θ₀₁ τ = θ₀₀ (τ + 1)`: the two-variable Jacobi theta function at `z = 1/2` is the
one-variable theta function at `τ + 1`. -/
lemma jacobiTheta₂_half_eq_jacobiTheta_add_one (τ : ℂ) :
    jacobiTheta₂ (1/2) τ = jacobiTheta (τ + 1) := by
  rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂, jacobiTheta₂]
  exact tsum_congr (fun n => jacobiTheta₂_term_half n τ)

/-! ## The growth estimate -/

/-- The elementary estimate `2 e^{-u} / (1 - e^{-u}) ≤ 2 / u` for `u > 0`. -/
private lemma two_mul_exp_neg_div_one_sub_le (u : ℝ) (hu : 0 < u) :
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

/-- The estimate of `norm_jacobiTheta_sub_one_le` in terms of `y = im τ`:
`2 / (1 - e^{-π y}) * e^{-π y} ≤ (2/π) y⁻¹` for `y > 0`. -/
private lemma two_div_one_sub_mul_exp_neg_pi_le (y : ℝ) (hy : 0 < y) :
    2 / (1 - Real.exp (-Real.pi * y)) * Real.exp (-Real.pi * y)
      ≤ (2 / Real.pi) * y⁻¹ := by
  have hπ : 0 < Real.pi * y := mul_pos Real.pi_pos hy
  have hmain := two_mul_exp_neg_div_one_sub_le (Real.pi * y) hπ
  have he : -(Real.pi * y) = -Real.pi * y := by ring
  have h2 : 2 / (Real.pi * y) = (2 / Real.pi) * y⁻¹ := by field_simp
  have hgoal : 2 / (1 - Real.exp (-Real.pi * y)) * Real.exp (-Real.pi * y)
      = 2 * Real.exp (-Real.pi * y) / (1 - Real.exp (-Real.pi * y)) := by ring
  rw [hgoal, ← he]
  rw [h2] at hmain
  exact hmain

/-- Jacobi's theta function `θ₀₁ = ∑_{n ∈ ℤ} (-1)^n q^{n²/2}` lies in the class
`𝒫 = Work.Kernels.InP`: it is holomorphic on `ℍ` and of moderate growth there.

Holomorphy is `differentiableAt_jacobiTheta₂_snd` for the two-variable theta function.
For the growth, `θ₀₁ τ = θ₀₀ (τ + 1)` and `norm_jacobiTheta_sub_one_le` give
`‖θ₀₁ τ - 1‖ ≤ 2 e^{-π y}/(1 - e^{-π y}) ≤ (2/π) y⁻¹` with `y = im τ`, whence
`‖θ₀₁ τ‖ ≤ (1 + 2/π) (y⁻¹ + 1)`, a moderate growth bound with `β = 1` and `γ = 0`. -/
lemma theta01Fun_mem_InP : Work.Kernels.InP Work.Kernels.theta01Fun := by
  refine ⟨?_, ?_⟩
  · -- holomorphy: `θ₀₁ = jacobiTheta₂ (1/2) ∘ (↑)` is holomorphic
    intro τ
    exact ((differentiableAt_jacobiTheta₂_snd (1/2) (by simpa using τ.im_pos)).mdifferentiableAt).comp
      τ τ.mdifferentiable_coe
  · -- moderate growth
    refine ⟨1 + 2 / Real.pi, 1, 0, by positivity, by norm_num, le_rfl, fun τ _ => ?_⟩
    rw [Real.rpow_one, Real.rpow_zero]
    have hy : 0 < τ.im := τ.im_pos
    have h := norm_jacobiTheta_sub_one_le (τ := (τ : ℂ) + 1) (by simpa using hy)
    have h' : ‖jacobiTheta ((τ : ℂ) + 1) - 1‖
        ≤ 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) := by
      simpa using h
    have hb := two_div_one_sub_mul_exp_neg_pi_le τ.im hy
    calc ‖Work.Kernels.theta01Fun τ‖
        = ‖jacobiTheta ((τ : ℂ) + 1)‖ := by
          rw [Work.Kernels.theta01Fun, jacobiTheta₂_half_eq_jacobiTheta_add_one]
      _ ≤ ‖jacobiTheta ((τ : ℂ) + 1) - 1‖ + 1 := by
          have := norm_add_le (jacobiTheta ((τ : ℂ) + 1) - 1) (1 : ℂ)
          simpa using this
      _ ≤ 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) + 1 := by linarith
      _ ≤ (2 / Real.pi) * (τ.im)⁻¹ + 1 := by linarith
      _ ≤ (1 + 2 / Real.pi) * ((τ.im)⁻¹ + 1) := by
          have h1 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr hy.le
          have h2 : 0 < (2 / Real.pi) := by positivity
          nlinarith

end Work.Kernels.ClassicalFacts
