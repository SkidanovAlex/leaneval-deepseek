/-
# The symbol toolbox of the §6 model approximation: kernel mass from the symbol

The §6 model approximation of Krause--Mirek--Tao (`mod-approx`) compares two bilinear convolution
operators on `ℓ²(ℤ)`: the concrete halved average and the §6 model operator.  Both are of the form
`bilinOp K u v x = ∑'_a ∑'_b K a b * u (x-a) * v (x-b)` (`Work.KMTAreas.A7.ModelOps`), so by
`Work.KMTAreas.A7.BilinOpLp` the whole estimate is an estimate of the `ℓ¹(ℤ²)` **mass** `∑'|K|` of
the *difference* of the two kernels.  The mass of the difference is small (`N⁻¹`) although each mass
is `O(1)`: the cancellation is visible only on the *frequency* side, where the symbol of the
difference is the paper's `M₀` (times the bumps).

This module fixes the elementary dictionary between a kernel `K : ℤ → ℤ → ℂ` and its symbol
`σ : ℝ → ℝ → ℂ`, i.e.

  `K (p₁,p₂) = ∫₀¹ ∫₀¹ σ(x,y) e(-p₁ x - p₂ y) dx dy`,   `e(z) = exp(2πiz)`,

and proves the precise form of the paper's **crude multiplier bound** (Lemma `crude-mult`(ii) of
the paper) which converts sup-bounds on the *partial derivatives* of `σ` up to order `2` into an
`ℓ¹` bound on the kernel:

  `∑'_{(p₁,p₂)} |K(p₁,p₂)| ≤ 40 * A`

provided `∫₀¹∫₀¹ ‖∂₁^{j₁}∂₂^{j₂}σ‖ ≤ A * r₁^{1-j₁} * r₂^{1-j₂}` for all `0 ≤ j₁,j₂ ≤ 2` and some
`0 < r₁,r₂ ≤ 1`.  The proof is the integration-by-parts argument of loc. cit.: each `K(p₁,p₂)` is
`((2πip₁)^{j₁}(2πip₂)^{j₂})⁻¹` times the coefficient of `∂₁^{j₁}∂₂^{j₂}σ`, and one takes for each
`(p₁,p₂)` the better of the cases `(0,0)`, `(2,0)`, `(0,2)`, `(2,2)` according to the sizes of
`r₁|p₁|` and `r₂|p₂|`.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral
open scoped BigOperators ENNReal

noncomputable section

/-- `e(x) = exp (2 π i x)`, the standard character of `ℝ`. -/
def eeC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- The `j`-th Fourier coefficient of a function of one real variable on `[0,1]`:
`∫₀¹ f(x) e(-j x) dx`. -/
def coeff1 (f : ℝ → ℂ) (j : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, f x * eeC (-(j : ℝ) * x)

/-- The `(p₁,p₂)`-th Fourier coefficient of a function of two real variables on `[0,1]²`:
`∫₀¹∫₀¹ σ(x,y) e(-p₁x - p₂y) dx dy`. -/
def coeff2 (σ : ℝ → ℝ → ℂ) (p₁ p₂ : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)

/-- The `j`-fold partial derivative in the first variable, the second variable being a parameter. -/
def dp1 (j : ℕ) (σ : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y => iteratedDeriv j (fun t => σ t y) x

/-- The `j`-fold partial derivative in the second variable. -/
def dp2 (j : ℕ) (σ : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y => iteratedDeriv j (fun t => σ x t) y

/-- The mixed partial derivative `∂₁^{j₁} ∂₂^{j₂} σ`. -/
def dp (j₁ j₂ : ℕ) (σ : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ := dp1 j₁ (dp2 j₂ σ)

end

end Work.KMTPlan.A6
