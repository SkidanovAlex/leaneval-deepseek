import Mathlib

/-!
# The triangular-test-function kernel `Ψ` for the Deuring--Heilbronn arithmetic engine

This file fixes the single notion used by the proof of `Work.LinnikAreas.repelArith`:

`repelPsi u = ∫₀¹ e^{ut} (1 - t) dt`  (for `u ≠ 0` this is `(e^u - 1 - u)/u²`, and `repelPsi 0 = 1/2`),

the Laplace transform of the triangle of length `1`.  With it, the §6 inequality for the triangle
of length `x` reads `0 ≤ 2x²(Ψ(νx) - Ψ((ν-μ)x)) - x²/2 + Cx`, and `repelD0 = 1/2 - 2(Ψ 1 - Ψ 0)`
is the positive constant produced by the `x = 1/ν` instance.
-/

namespace Work.LinnikAreas

/-- The kernel of the triangular test function: the Laplace transform of `t ↦ (1 - t)⁺` on `[0,1]`,
`repelPsi u = ∫₀¹ e^{ut} (1 - t) dt`.  For `u ≠ 0` this is `(e^u - 1 - u)/u²`; `repelPsi 0 = 1/2`. -/
noncomputable def repelPsi (u : ℝ) : ℝ := ∫ t in (0:ℝ)..1, Real.exp (u * t) * (1 - t)

/-- The positive constant forced by the `x = 1/ν` instance: `repelD0 = 1/2 - 2(Ψ 1 - Ψ 0)
= 11/2 - 2e > 0`. -/
noncomputable def repelD0 : ℝ := 1 / 2 - 2 * (repelPsi 1 - repelPsi 0)

end Work.LinnikAreas
