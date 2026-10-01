import Mathlib
import Submission.Work.LinnikAreas.RepelDefs
import Submission.Work.LinnikAreas.repelPsiBasic
import Submission.Work.LinnikAreas.repelPsiEval
import Submission.Work.LinnikAreas.repelPsiSubLe

namespace Work.LinnikAreas

/-!
# The `x`-instance arithmetic of the triangular test function (Linnik §6 input)

This is the arithmetic engine extracted from the Deuring--Heilbronn triangle inequality at a
*general* length `x`.  With `repelPsi u = ∫₀¹ e^{ut}(1-t)dt` the two integrals of the hypothesis
are `∫₀ˣ e^{λ₂t}(x-t)dt = x² Ψ(λ₂x)` and `∫₀ˣ e^{(λ₂-λ₀)t}(x-t)dt = x² Ψ((λ₂-λ₀)x)`
(`repelPsiEval`), so the hypothesis `h6` reads

`0 ≤ 2x²(Ψ(λ₂x) - Ψ((λ₂-λ₀)x)) - x²/2 + Cx`.

Dividing by `2x² > 0` gives `(x-2C)/(4x) ≤ Ψ(λ₂x) - Ψ((λ₂-λ₀)x)`, while the finite-difference
bound `repelPsiSubLe` (with `u = λ₂x`, `w = λ₀x ≥ 0`) gives the reverse estimate
`Ψ(λ₂x) - Ψ((λ₂-λ₀)x) ≤ λ₀ x e^{λ₂x}/6`.  Combining,

`(x-2C)/(4x) ≤ λ₀ · (x e^{λ₂x}/6)`,

which upon solving for `λ₀` is exactly the claimed bound `3(x-2C)/(2x²)·e^{-xλ₂} ≤ λ₀`.
-/

/-- **The `x`-instance arithmetic of the triangular test function.**  If the §6 triangle inequality
holds at length `x` (`h6`), then `λ₀` is bounded below by `3(x-2C)/(2x²)·e^{-xλ₂}`. -/
theorem sixArith {lam₀ lam₂ x C : ℝ} (hx : 0 < x) (hC : 0 ≤ C) (hlam₀ : 0 < lam₀)
    (hle : lam₀ ≤ lam₂) (hxC : 2 * C < x)
    (h6 : 0 ≤ 2 * (∫ t in (0:ℝ)..x, Real.exp (lam₂ * t) * (x - t))
        - 2 * (∫ t in (0:ℝ)..x, Real.exp ((lam₂ - lam₀) * t) * (x - t))
        - x ^ 2 / 2 + C * x) :
    3 * (x - 2 * C) / (2 * x ^ 2) * Real.exp (-(x * lam₂)) ≤ lam₀ := by
  have hx0 : (0:ℝ) ≤ x := le_of_lt hx
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₀ hle
  have hx2C : (0:ℝ) < x - 2 * C := by linarith
  have hCnn : (0:ℝ) ≤ C := hC
  -- Rewrite the two integrals with `repelPsiEval`.
  have h6psi : 0 ≤ 2 * (x^2 * repelPsi (lam₂ * x)) - 2 * (x^2 * repelPsi ((lam₂ - lam₀) * x))
      - x^2/2 + C*x := by
    rw [repelPsiEval x lam₂ hx0, repelPsiEval x (lam₂ - lam₀) hx0] at h6
    exact h6
  -- Lower bound on the `Ψ`-difference.
  have hr : (x - 2*C)/(4*x) ≤ repelPsi (lam₂*x) - repelPsi ((lam₂-lam₀)*x) := by
    have hmain : (x^2/2 - C*x)/(2*x^2) ≤ repelPsi (lam₂*x) - repelPsi ((lam₂-lam₀)*x) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*x^2)]
      linarith [h6psi]
    have heq : (x^2/2 - C*x)/(2*x^2) = (x-2*C)/(4*x) := by
      field_simp
      ring
    linarith [hmain, heq]
  -- Upper bound on the same `Ψ`-difference.
  have hAu : repelPsi (lam₂*x) - repelPsi ((lam₂-lam₀)*x) ≤ lam₀ * (x*Real.exp (lam₂*x))/6 := by
    have := repelPsiSubLe (u := lam₂*x) (w := lam₀*x)
      (mul_nonneg (le_of_lt hlam₂) (le_of_lt hx)) (mul_nonneg (le_of_lt hlam₀) (le_of_lt hx))
    have harg : lam₂*x - lam₀*x = (lam₂-lam₀)*x := by ring
    rw [harg] at this
    linarith [this]
  have hcomb : (x - 2*C)/(4*x) ≤ lam₀ * (x*Real.exp (lam₂*x))/6 := le_trans hr hAu
  -- Solve for `λ₀`.
  have hkey : 3 * (x - 2 * C) / (2 * x ^ 2) * Real.exp (-(x * lam₂))
      = ((x - 2*C)/(4*x)) / (x * Real.exp (lam₂ * x) / 6) := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [hkey, div_le_iff₀ (by positivity : (0:ℝ) < x * Real.exp (lam₂ * x) / 6)]
  linarith [hcomb]

end Work.LinnikAreas
