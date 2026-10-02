/-
# ZeroFreeTables/OffAxis/RectRepDiag

The **diagonal §9 assembly at rectangle height `H`**: the height-parametric form of
`Work.ZeroFreeTables.Rep9.ineq913_diag_of_pointwise` (`Rep9/combination_diag.lean`).

From the pointwise diagonal inequality `OffAxis.RectRepComb` (HB (9.1) at `γ₀ = γ₁ = Im ρ₁`)
and the four per-point *upper* bounds at `σ = 1 + a/log q`, `σ+iγ`, `σ+2iγ`, `σ+3iγ`
(`γ = Im ρ₁`, `|γ| ≤ H`), HB's `ineq913` at the diagonal `λ₀ = λ₁` follows.

The hypothesis `IsZ χ₁ ρ₁` of the on-axis version is replaced by its three consequences
`χ₁ ≠ 1`, `|ρ₁.im| ≤ H`, `0 ≤ lamOf q ρ₁`; nothing else changes.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepComb
import Submission.Work.ZeroFreeTables.Rep9.Algebra

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables Work.LinnikContract

/-- **The diagonal assembly at height `H`.**  `ρ₁` is a zero of the non-principal `χ₁` with
`|Im ρ₁| ≤ H` and `λ = lamOf q ρ₁ ≥ 0`; the side condition `cond913 λ λ a K` holds; the four
per-point bounds `hS0 … hS3` hold with errors `e₀ … e₃` whose weighted sum is at most
`c (K²+3K+3/2)`; then `ineq913 λ λ a K ε`. -/
theorem RectRepDiag {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    {a K ε c e₀ e₁ e₂ e₃ H : ℝ}
    (hq : 2 ≤ q) (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε)
    (hχ₁ : χ₁ ≠ 1) (hγ : |ρ₁.im| ≤ H) (hlam : 0 ≤ Work.LinnikContract.lamOf q ρ₁)
    (hcond : cond913 (lamOf q ρ₁) (lamOf q ρ₁) a K)
    (hc : c ≤ 1/6 + (K^2 + K + 1 - K * Kond K) / (12*K))
    (hS0 : SigmaP3L q (Real.log q) 1 (((1 + a / Real.log q : ℝ)) : ℂ) a (lamOf q ρ₁)
             ≤ P3R ((a + lamOf q ρ₁)/a) + (a + lamOf q ρ₁) * e₀)
    (hS1 : SigmaP3L q (Real.log q) χ₁
             ((((1 + a / Real.log q : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
             ≤ -(2 * P3R 1) + (a + lamOf q ρ₁) * e₁)
    (hS2 : SigmaP3L q (Real.log q) (χ₁^2)
             ((((1 + a / Real.log q : ℝ)) : ℂ) + (((2*ρ₁.im : ℝ)) : ℂ) * Complex.I)
             a (lamOf q ρ₁)
             ≤ (a + lamOf q ρ₁) * e₂)
    (hS3 : SigmaP3L q (Real.log q) (χ₁^3)
             ((((1 + a / Real.log q : ℝ)) : ℂ) + (((3*ρ₁.im : ℝ)) : ℂ) * Complex.I)
             a (lamOf q ρ₁)
             ≤ (a + lamOf q ρ₁) * e₃)
    (he : (K^2 + K + 1/2) * e₀ + (K^2 + 2*K + 3/4) * e₁ + (K + 1/2) * e₂ + (1/4) * e₃
            ≤ c * (K^2 + 3*K + 3/2)) :
    ineq913 (lamOf q ρ₁) (lamOf q ρ₁) a K ε := by
  set lam := lamOf q ρ₁ with hlamdef
  set S0 := SigmaP3L q (Real.log q) 1 (((1 + a / Real.log q : ℝ)) : ℂ) a lam with hS0def
  set S1 := SigmaP3L q (Real.log q) χ₁
      ((((1 + a / Real.log q : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a lam with hS1def
  set S2 := SigmaP3L q (Real.log q) (χ₁^2)
      ((((1 + a / Real.log q : ℝ)) : ℂ) + (((2*ρ₁.im : ℝ)) : ℂ) * Complex.I) a lam with hS2def
  set S3 := SigmaP3L q (Real.log q) (χ₁^3)
      ((((1 + a / Real.log q : ℝ)) : ℂ) + (((3*ρ₁.im : ℝ)) : ℂ) * Complex.I) a lam with hS3def
  have hα : 0 < a + lam := by linarith only [ha, hlam]
  have hcomb : 0 ≤ (K^2 + K + 1/2) * S0 + (K^2 + 2*K + 3/4) * S1
      + (K + 1/2) * S2 + (1/4) * S3 := by
    rw [hS0def, hS1def, hS2def, hS3def]
    exact RectRepComb χ₁ hq ha hK hγ hlam hχ₁
  have h1 : (K^2 + K + 1/2) * S0
      ≤ (K^2 + K + 1/2) * (P3R ((a + lam)/a) + (a + lam) * e₀) :=
    mul_le_mul_of_nonneg_left hS0 (by positivity)
  have h2 : (K^2 + 2*K + 3/4) * S1
      ≤ (K^2 + 2*K + 3/4) * (-(2 * P3R 1) + (a + lam) * e₁) :=
    mul_le_mul_of_nonneg_left hS1 (by positivity)
  have h3 : (K + 1/2) * S2 ≤ (K + 1/2) * ((a + lam) * e₂) :=
    mul_le_mul_of_nonneg_left hS2 (by linarith only [hK])
  have h4 : (1/4 : ℝ) * S3 ≤ (1/4 : ℝ) * ((a + lam) * e₃) :=
    mul_le_mul_of_nonneg_left hS3 (by norm_num)
  have hkey : 0 ≤ (K^2 + K + 1/2) * (P3R ((a + lam)/a) + (a + lam) * e₀)
      + (K^2 + 2*K + 3/4) * (-(2 * P3R 1) + (a + lam) * e₁)
      + (K + 1/2) * ((a + lam) * e₂) + (1/4 : ℝ) * ((a + lam) * e₃) := by
    linarith only [hcomb, h1, h2, h3, h4, hS3]
  have heα : (a + lam) * ((K^2 + K + 1/2) * e₀ + (K^2 + 2*K + 3/4) * e₁
        + (K + 1/2) * e₂ + (1/4) * e₃)
      ≤ (a + lam) * (c * (K^2 + 3*K + 3/2)) :=
    mul_le_mul_of_nonneg_left he hα.le
  have hD : 0 ≤ (K^2 + K + 1/2) * P3R ((a + lam)/a) - (2*K^2 + 4*K + 3/2) * P3R 1
      + (a + lam) * c * (K^2 + 3*K + 3/2) := by
    linarith only [hkey, heα, hS3, hcomb, h1, h2, h3]
  have hx3 : ((a + lam)/a)^3 ≤ Kond K + 1 := by
    rw [hlamdef]; exact Work.ZeroFreeTables.Rep9.cond913_cube_le ha hlam hcond
  exact Work.ZeroFreeTables.Rep9.ineq913_diag_of_derived ha hK hε hlam hx3 hc hD

end Work.ZeroFreeTables.OffAxis
