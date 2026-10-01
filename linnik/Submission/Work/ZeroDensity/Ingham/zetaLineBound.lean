import Mathlib
import Submission.Work.ZeroDensity.Ingham.perronIntDeps

namespace Work.ZeroDensity.Ingham

/-- **Polynomial growth of `ζ` on the vertical line through `ρ` shifted by `c`**, for
`σ := ρ.re + c ∈ [-1,3]`, once `|Im| ≥ 1` (ensured here by `|t| ≥ |Im ρ| + 1`).

Ingredient (re-exported by `Work.ZeroDensity.Ingham.perronIntDeps`):
`Commons.NumberTheory.Zeta.zeta_strip_polyGrowth : ∃ C > 0, ∀ σ t, -1 ≤ σ → σ ≤ 3 → 1 ≤ |t| →
‖ζ (σ + it)‖ ≤ C (|t| + 3)^4`, applied at `σ = ρ.re + c` and `t = ρ.im + t₀`.  Since
`|ρ.im + t₀| ≥ |t₀| - |ρ.im| ≥ 1` for `|t₀| ≥ |ρ.im| + 1`, and
`|ρ.im + t₀| + 3 ≤ (|ρ.im| + 1 + 3) + |t₀| ≤ 5 (1 + |t₀|)` because `|ρ.im| + 1 ≤ |t₀|`, this gives
`‖ζ (ρ + c + i t₀)‖ ≤ C · 5^4 · (1 + |t₀|)^4`. -/
theorem zetaLineBound (ρ : ℂ) (c : ℝ) (hc1 : -1 ≤ ρ.re + c) (hc2 : ρ.re + c ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |ρ.im| + 1 ≤ |t| →
      ‖riemannZeta (ρ + ((c : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C * (1 + |t|) ^ 4 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
  refine ⟨C₀ * 5 ^ 4, by positivity, ?_⟩
  intro t ht
  -- identify the argument with `σ + i τ` for `σ = ρ.re + c`, `τ = ρ.im + t`
  have harg : ρ + ((c : ℂ) + (t : ℂ) * Complex.I)
      = (((ρ.re + c : ℝ)) : ℂ) + Complex.I * ((ρ.im + t : ℝ) : ℂ) := by
    conv_lhs => rw [show ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I from (Complex.re_add_im ρ).symm]
    push_cast
    ring
  -- `τ` is at least `1` in absolute value
  have htabs : 1 ≤ |ρ.im + t| := by
    have h1 : |ρ.im| ≤ |t| := by linarith
    have h2 : |t| ≤ |ρ.im + t| + |ρ.im| := by
      have h := abs_add_le (ρ.im + t) (-ρ.im)
      have heq : (ρ.im + t) + (-ρ.im) = t := by ring
      rw [heq, abs_neg] at h
      exact h
    linarith
  have hb := hC₀ (ρ.re + c) (ρ.im + t) hc1 hc2 htabs
  rw [harg]
  -- the polynomial factor comparison
  have hle : |ρ.im + t| + 3 ≤ 5 * (1 + |t|) := by
    have h1 : |ρ.im| ≤ |t| := by linarith
    have h2 : |ρ.im + t| ≤ |ρ.im| + |t| := abs_add_le _ _
    have h3 : (0 : ℝ) ≤ |t| := abs_nonneg t
    nlinarith
  have hpow : (|ρ.im + t| + 3) ^ 4 ≤ 5 ^ 4 * (1 + |t|) ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ |ρ.im + t| + 3) hle 4
    rwa [mul_pow] at h
  calc ‖riemannZeta (↑(ρ.re + c) + Complex.I * ↑(ρ.im + t))‖
      ≤ C₀ * (|ρ.im + t| + 3) ^ 4 := hb
    _ ≤ C₀ * (5 ^ 4 * (1 + |t|) ^ 4) :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hC₀pos)
    _ = C₀ * 5 ^ 4 * (1 + |t|) ^ 4 := by ring

end Work.ZeroDensity.Ingham
