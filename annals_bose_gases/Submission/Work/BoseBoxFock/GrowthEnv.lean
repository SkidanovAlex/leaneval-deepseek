import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.GrowthEnv` — the growth envelope `1 + ρ^{3/2}`

Helper vocabulary for the uniform-in-`ρ` lower bound on FS's substituted
Hamiltonian `KzOpFS ρ`: every row of `KzOpFS ρ` has a lower bound of the shape
`-C · env(ρ) · ‖g‖²`, `env ρ = 1 + √ρ·ρ = 1 + ρ^{3/2}` (written with `√ρ` to
avoid `Real.rpow`).  `env` is the envelope in which the polynomial part
`c(ρ) = ½ℓ³(ĝ(0)+Ŵ₁ω(0))ρ² − μℓ³ĝ(0)ρ` of the `c`-number row of `KzOpFS ρ`
dominates all the remaining rows, so that the resulting polynomial is bounded
below on `[0,∞)`.
-/

noncomputable section

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- The growth envelope `1 + ρ^{3/2} = 1 + √ρ·ρ`. -/
def genv (ρ : ℝ) : ℝ := 1 + Real.sqrt ρ * ρ

private lemma sqrt_mul_self_nonneg (ρ : ℝ) : 0 ≤ Real.sqrt ρ * ρ := by
  rcases lt_or_ge 0 ρ with h | h
  · exact mul_nonneg (Real.sqrt_nonneg ρ) (le_of_lt h)
  · rw [Real.sqrt_eq_zero_of_nonpos h, zero_mul]

lemma genv_nonneg (ρ : ℝ) : 0 ≤ genv ρ := by
  have h := sqrt_mul_self_nonneg ρ
  rw [genv]
  linarith

lemma one_le_genv (ρ : ℝ) : 1 ≤ genv ρ := by
  have h := sqrt_mul_self_nonneg ρ
  rw [genv]
  linarith

lemma genv_pos (ρ : ℝ) : 0 < genv ρ := lt_of_lt_of_le zero_lt_one (one_le_genv ρ)

private lemma sq_le_one_add_cube {t : ℝ} (ht : 0 ≤ t) : t * t ≤ 1 + t * (t * t) := by
  rcases lt_or_ge t 1 with h | h
  · have h0 : 0 ≤ t * t := mul_nonneg ht ht
    have h1 : t * t ≤ 1 := by nlinarith
    have h2 : 0 ≤ t * (t * t) := mul_nonneg ht h0
    linarith
  · have h1 : t * t ≤ t * (t * t) := by
      have : 0 ≤ t * t * (t - 1) := mul_nonneg (mul_nonneg ht ht) (by linarith)
      nlinarith
    linarith

private lemma self_le_one_add_cube {t : ℝ} (ht : 0 ≤ t) : t ≤ 1 + t * (t * t) := by
  rcases lt_or_ge t 1 with h | h
  · have h0 : 0 ≤ t * (t * t) := mul_nonneg ht (mul_nonneg ht ht)
    linarith
  · have h1 : t ≤ t * (t * t) := by
      have : 0 ≤ t * (t * t - 1) := mul_nonneg ht (by nlinarith)
      nlinarith
    linarith

/-- For `ρ ≥ 0`: `ρ ≤ 1 + ρ^{3/2}`. -/
lemma self_le_genv {ρ : ℝ} (hρ : 0 ≤ ρ) : ρ ≤ genv ρ := by
  calc ρ = Real.sqrt ρ * Real.sqrt ρ := (Real.mul_self_sqrt hρ).symm
    _ ≤ 1 + Real.sqrt ρ * (Real.sqrt ρ * Real.sqrt ρ) :=
        sq_le_one_add_cube (Real.sqrt_nonneg ρ)
    _ = 1 + Real.sqrt ρ * ρ := by rw [Real.mul_self_sqrt hρ]
    _ = genv ρ := by rw [genv]

/-- For `ρ ≥ 0`: `√ρ ≤ 1 + ρ^{3/2}`. -/
lemma sqrt_le_genv {ρ : ℝ} (hρ : 0 ≤ ρ) : Real.sqrt ρ ≤ genv ρ := by
  calc Real.sqrt ρ ≤ 1 + Real.sqrt ρ * (Real.sqrt ρ * Real.sqrt ρ) :=
        self_le_one_add_cube (Real.sqrt_nonneg ρ)
    _ = 1 + Real.sqrt ρ * ρ := by rw [Real.mul_self_sqrt hρ]
    _ = genv ρ := by rw [genv]

lemma sqrt_mul_self_le_genv (ρ : ℝ) : Real.sqrt ρ * ρ ≤ genv ρ := by
  rw [genv]; linarith

end Work.BoseBoxFock
