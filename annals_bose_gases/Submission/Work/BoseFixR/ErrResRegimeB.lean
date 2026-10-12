import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixR.arithRegimeB
import Submission.Work.BoseFixR.sqrt_LM_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/ErrResRegimeB.lean` — the far-regime arithmetic (`2μ ≤ ρ`)

This is the second half of the far-leg scalar arithmetic consumed by
`Submission/Work/BoseFixR/RB5FSArith2.lean` (FS §9, `Work.BoseFixR.RB5FSHonest`): on the
region `2μ ≤ ρ` the whole residual budget

`10³⁰⁰·((ρ+μ)AM + (ρ+μ)^{3/2}·A·√(L³M)) + |ρ−μ|·256πAM + πAμ²L³X⁶`

fits inside the full quadratic margin `4πA(ρ−μ)²L³` of FS `eq:SimplifyKz`, under the two
structural inputs

* `M = X^{337/4}·(μL³)` (the `𝓜`-ratio of `Work.BoseFixR.bigMV`), and
* the single numeric slack `10³⁰⁰·X^{289/8} ≤ 1/6`.

**The mathematics.**  Put `s := (ρ−μ)/μ`; then `2μ ≤ ρ` gives `s ≥ 1`, and
`ρ−μ = sμ`, `ρ+μ = (s+2)μ`, while the far condition `μX³ ≤ |ρ−μ|` becomes `X³ ≤ s`.
The `𝓜`-identity turns `√(L³M)` into `X^{337/8}·√μ·L³` (`sqrt_LM_eq`), so every term of
the left-hand side is `Aμ²L³` times a monomial in `s` and `X`:

`LHS = Aμ²L³·[10³⁰⁰((s+2)X^{337/4} + (s+2)^{3/2}X^{337/8}) + 256πsX^{337/4} + πX⁶]`,

while `RHS = Aμ²L³·4πs²`.  The bracket is exactly `arithRegimeB`.  This file is the
assembly: rewriting the four terms into that normal form (the only non-algebraic input
being `μ^{3/2}·√μ = μ²`), applying the two children, and comparing the resulting
`Aμ²L³`-multiples, `4πs²μ² ≤ 4π(ρ−μ)²` after the substitution `ρ−μ = sμ`.
-/

namespace Work.BoseFixR

theorem ErrResRegimeB {A μ ρ L M X : ℝ}
    (hA : 0 < A) (hμ : 0 < μ) (hρ2 : 2 * μ ≤ ρ)
    (hL : 0 < L) (hM : 0 < M) (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hfar : μ * X ^ 3 ≤ |ρ - μ|)
    (hML : M = X ^ (337 / 4 : ℝ) * (μ * L ^ 3))
    (hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ 1 / 6) :
    (10 : ℝ) ^ 300 * ((ρ + μ) * A * M
        + (ρ + μ) ^ (3 / 2 : ℝ) * A * Real.sqrt (L ^ 3 * M))
      + |ρ - μ| * (256 * Real.pi * A * M)
      + Real.pi * A * μ ^ 2 * L ^ 3 * X ^ 6
      ≤ 4 * Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by
  have hM0 : (0 : ℝ) < M := hM
  -- the reduced variable `s = (ρ−μ)/μ`, which satisfies `s ≥ 1`
  set s : ℝ := (ρ - μ) / μ with hs
  have hs1 : 1 ≤ s := by
    rw [hs, le_div_iff₀ hμ]; linarith
  have hρeq : ρ = (s + 1) * μ := by
    have h : s * μ = ρ - μ := by rw [hs]; field_simp
    linarith
  have hρμ : ρ + μ = (s + 2) * μ := by rw [hρeq]; ring
  have hsub : ρ - μ = s * μ := by rw [hρeq]; ring
  have habs : |ρ - μ| = s * μ := by rw [hsub]; exact abs_of_nonneg (by positivity)
  -- the `𝓜`-ratio rewrites the square root
  have hsqrt := sqrt_LM_eq hL hμ hX0 hML
  -- the far condition becomes `X³ ≤ s`
  have hsX : X ^ 3 ≤ s := by
    have hfar' : μ * X ^ 3 ≤ s * μ := by rw [habs] at hfar; exact hfar
    have h2 : X ^ 3 * μ ≤ s * μ := by linarith
    exact le_of_mul_le_mul_right h2 hμ
  have hmu2 : μ ^ (3 / 2 : ℝ) * Real.sqrt μ = μ ^ 2 := by
    rw [Real.sqrt_eq_rpow μ, ← Real.rpow_add hμ]
    norm_num
  have hbracket := arithRegimeB hs1 hX0 hX1 hsX hslack
  -- each of the four terms, written as `A·μ²·L³` times its monomial
  have hT1 : (ρ + μ) * A * M = A * μ ^ 2 * L ^ 3 * ((s + 2) * X ^ (337 / 4 : ℝ)) := by
    rw [hρμ, hML]; ring
  have hT2 : (ρ + μ) ^ (3 / 2 : ℝ) * A * Real.sqrt (L ^ 3 * M)
      = A * μ ^ 2 * L ^ 3 * ((s + 2) ^ (3 / 2 : ℝ) * X ^ (337 / 8 : ℝ)) := by
    rw [hρμ, hsqrt, Real.mul_rpow (show (0:ℝ) ≤ s + 2 by positivity) (le_of_lt hμ)]
    calc ((s + 2) ^ (3 / 2 : ℝ) * μ ^ (3 / 2 : ℝ)) * A
            * (X ^ (337 / 8 : ℝ) * Real.sqrt μ * L ^ 3)
        = ((s + 2) ^ (3 / 2 : ℝ) * A * X ^ (337 / 8 : ℝ) * L ^ 3)
            * (μ ^ (3 / 2 : ℝ) * Real.sqrt μ) := by ring
      _ = ((s + 2) ^ (3 / 2 : ℝ) * A * X ^ (337 / 8 : ℝ) * L ^ 3) * μ ^ 2 := by
            rw [hmu2]
      _ = A * μ ^ 2 * L ^ 3 * ((s + 2) ^ (3 / 2 : ℝ) * X ^ (337 / 8 : ℝ)) := by ring
  have hT3 : |ρ - μ| * (256 * Real.pi * A * M)
      = A * μ ^ 2 * L ^ 3 * (256 * Real.pi * s * X ^ (337 / 4 : ℝ)) := by
    rw [habs, hML]; ring
  have hT4 : Real.pi * A * μ ^ 2 * L ^ 3 * X ^ 6
      = A * μ ^ 2 * L ^ 3 * (Real.pi * X ^ 6) := by ring
  have key : (10 : ℝ) ^ 300 * ((ρ + μ) * A * M
        + (ρ + μ) ^ (3 / 2 : ℝ) * A * Real.sqrt (L ^ 3 * M))
      + |ρ - μ| * (256 * Real.pi * A * M)
      + Real.pi * A * μ ^ 2 * L ^ 3 * X ^ 6
      = A * μ ^ 2 * L ^ 3 * ((10 : ℝ) ^ 300 * ((s + 2) * X ^ (337 / 4 : ℝ)
          + (s + 2) ^ (3 / 2 : ℝ) * X ^ (337 / 8 : ℝ))
        + 256 * Real.pi * s * X ^ (337 / 4 : ℝ) + Real.pi * X ^ 6) := by
    rw [hT1, hT2, hT3, hT4]; ring
  calc (10 : ℝ) ^ 300 * ((ρ + μ) * A * M
        + (ρ + μ) ^ (3 / 2 : ℝ) * A * Real.sqrt (L ^ 3 * M))
      + |ρ - μ| * (256 * Real.pi * A * M)
      + Real.pi * A * μ ^ 2 * L ^ 3 * X ^ 6
      = A * μ ^ 2 * L ^ 3 * ((10 : ℝ) ^ 300 * ((s + 2) * X ^ (337 / 4 : ℝ)
          + (s + 2) ^ (3 / 2 : ℝ) * X ^ (337 / 8 : ℝ))
        + 256 * Real.pi * s * X ^ (337 / 4 : ℝ) + Real.pi * X ^ 6) := key
    _ ≤ A * μ ^ 2 * L ^ 3 * (4 * Real.pi * s ^ 2) :=
        mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = 4 * Real.pi * A * (ρ - μ) ^ 2 * L ^ 3 := by rw [hsub]; ring

end Work.BoseFixR
