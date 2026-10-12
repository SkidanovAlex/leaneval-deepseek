import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7.Coef
import Submission.Work.BoseK15.AlphaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.alphaCoef_eq_h` — the Bogoliubov squeezing parameter is a
function of the ratio `ℬ/𝒜`

FS's squeezing parameter `α(𝒜,ℬ) = ℬ/(𝒜+√(𝒜²-ℬ²))` (`Work.BoseB7.alphaCoef`) is
homogeneous of degree `0` in the pair `(𝒜,ℬ)`: pulling the positive factor `𝒜`
out of the square root,

`α(𝒜,ℬ) = ℬ/(𝒜(1+√(1-(ℬ/𝒜)²))) = h(ℬ/𝒜)`,

with `h(r) = r/(1+√(1-r²))` (`Work.BoseK15.h`), the `tan(½·arcsin r)`
parametrisation of the angle used in `lem:EstimatesOnQ3-js` and in the
`eq:Comparealpha-A` / `eq:alphaInPH` estimate `|α| ≤ 𝓁 ≤ ½`.

The hypothesis `|ℬ| ≤ 𝒜/2` (FS `eq:BoverA`) is more than what the algebra needs
(`|ℬ| ≤ 𝒜` and `𝒜 > 0` suffice, since then `1-(ℬ/𝒜)² ≥ 0`); it is exactly the
regime in which the corpus states the estimate, so we keep it.

Main identity: `√(𝒜²-ℬ²) = 𝒜√(1-(ℬ/𝒜)²)` for `𝒜 ≥ 0`, hence
`𝒜+√(𝒜²-ℬ²) = 𝒜(1+√(1-(ℬ/𝒜)²))`, and the result follows by cancellation.
-/

noncomputable section

namespace Work.BoseK15

/-- The Bogoliubov squeezing parameter depends on `(𝒜,ℬ)` only through the
ratio `ℬ/𝒜`: `ℬ/(𝒜+√(𝒜²-ℬ²)) = h(ℬ/𝒜)` for `𝒜 > 0`, `|ℬ| ≤ 𝒜/2`. -/
theorem alphaCoef_eq_h {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A / 2) :
    Work.BoseB7.alphaCoef A B = Work.BoseK15.h (B / A) := by
  have hAle : |B| ≤ A := by linarith [abs_nonneg B]
  have hA0 : (0 : ℝ) ≤ A := le_of_lt hA
  -- the factorisation `A² - B² = A²(1 - (B/A)²)`
  have hsq : A ^ 2 - B ^ 2 = A ^ 2 * (1 - (B / A) ^ 2) := by field_simp
  -- hence `√(A²-B²) = A√(1-(B/A)²)` (using `A ≥ 0`)
  have hs : Real.sqrt (A ^ 2 - B ^ 2) = A * Real.sqrt (1 - (B / A) ^ 2) := by
    rw [hsq, Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA0]
  unfold Work.BoseB7.alphaCoef Submission.BoseGases.bogAlpha Submission.BoseGases.bogS
    Work.BoseK15.h
  rw [hs, div_div, show A + A * Real.sqrt (1 - (B / A) ^ 2)
      = A * (1 + Real.sqrt (1 - (B / A) ^ 2)) by ring]

end Work.BoseK15
