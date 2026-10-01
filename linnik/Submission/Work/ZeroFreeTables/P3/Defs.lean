/-
# ZeroFreeTables/P3/Defs — the definitions of the `P₃` engine of HB §8–§9

* `SigmaP3` — HB's `Σ(s,χ)` of (8.4) for the polynomial `P₃(X) = X + X² + (2/3)X³`
  (the third polynomial of HB's list (4.12)).
* `P3NearSum` — the sum of `Re P₃(α/((s-u)𝓛))` over the zeros of the completed
  L-function within `δ` of the point `1 + i·Im s` (HB's "near zeros", (9.2)–(9.7)).
* `P3Combination` — the left-hand side of HB (9.1) (the `Σ`-combination coming from the
  pointwise inequality `0 ≤ χ₀(n)(1+Re z₀)(K+Re z₁)²`), at the eight points of §9.
* `A913` — HB's `A` of (9.8).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

namespace Work.ZeroFreeTables

/-- **Caution (wrong coefficient, kept for history).**  With HB's (8.4)
`Σ_k a_k α^k/(k-1)! (𝓛⁻¹log n)^{k-1}` and `a₃ = 2/3` the smoothing weight is
`α + α²y + (1/3)α³y²`, whose Laplace transform is `P₃(α/z)`.  The definition below carries
`(2/3)α³y²` instead (the functional of `X + X² + (4/3)X³`), so it is *not* the `Σ` for which
HB's (9.2)–(9.8) hold; it is kept only because the proved `P3/Pointwise91.lean` is stated for
the `HbCombination` built from it.  The corrected definitions (`SigmaP3L`, `HbCombinationL`)
are in `P3/DefsL.lean` and are the ones the §9 derivation uses. -/
def SigmaP3 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (a lam₁ : ℝ) : ℝ :=
  (Real.log q)⁻¹ * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
    (χ (n : ZMod q) / (n : ℂ) ^ s).re *
    ((a + lam₁) + (a + lam₁) ^ 2 * (Real.log n / Real.log q)
      + (2/3) * (a + lam₁) ^ 3 * (Real.log n / Real.log q) ^ 2)

/-- The "near zero" sum of HB (9.2)–(9.7): the zeros of the completed `L`-function within
`δ` of the point `1 + i·Im s`, weighted by their multiplicity and by `Re P₃(α/((s-u)𝓛))`.
The test point is `1 + i·Im s`, which is the convention of HB's Lemma 3.1 and of
`Commons.NumberTheory.Linnik.lemma3_1`. -/
def P3NearSum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (a lam₁ δ : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2)) u : ℤ) : ℝ) *
    (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
      (P3 ((a + lam₁) / ((s - u) * (Real.log q)))).re else 0)

/-- HB's `A` of (9.8): `Re{(K²+3/4)P₃(α/(a+λ₁+iΔ)) + 2K P₃(α/(a+λ₀+iΔ)) − K P₃(α/(a+iΔ))}`.
(It is the part of the derivation that has to be shown non-negative; HB (9.9)–(9.12).) -/
def A913 (a lam₁ lam₀ K Δ : ℝ) : ℝ :=
  ((K ^ 2 + 3/4) * P3 ((a + lam₁) / ((a + lam₁) + Δ * Complex.I))
    + 2 * K * P3 ((a + lam₁) / ((a + lam₀) + Δ * Complex.I))
    - K * P3 ((a + lam₁) / (a + Δ * Complex.I))).re

end Work.ZeroFreeTables

namespace Work.ZeroFreeTables

/-- The left-hand side of HB (9.1): the `Σ`-combination coming from the pointwise
inequality `0 ≤ χ₀(n)(1 + Re z₀)(K + Re z₁)²`, `z_j = χ(n)n^{-iγ_j}`, evaluated at the eight
points `σ`, `σ+iγ₀`, `σ+i(γ₁−γ₀)`, `σ+iγ₁`, `σ+i(γ₁+γ₀)`, `σ+i(2γ₁−γ₀)`, `σ+2iγ₁`,
`σ+i(2γ₁+γ₀)` and the characters `χ₀, χ, χ², χ³`. -/
def HbCombination (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ₀ γ₁ a lam₁ : ℝ) : ℝ :=
  (K ^ 2 + 1/2) * (SigmaP3 q 1 (σ : ℂ) a lam₁
      + SigmaP3 q χ ((σ : ℂ) + (γ₀ : ℂ) * Complex.I) a lam₁)
  + K * (SigmaP3 q 1 ((σ : ℂ) + ((γ₁ - γ₀) : ℂ) * Complex.I) a lam₁
      + 2 * SigmaP3 q χ ((σ : ℂ) + (γ₁ : ℂ) * Complex.I) a lam₁
      + SigmaP3 q (χ ^ 2) ((σ : ℂ) + ((γ₁ + γ₀) : ℂ) * Complex.I) a lam₁)
  + (1/4) * (SigmaP3 q χ ((σ : ℂ) + ((2 * γ₁ - γ₀) : ℂ) * Complex.I) a lam₁
      + 2 * SigmaP3 q (χ ^ 2) ((σ : ℂ) + ((2 * γ₁) : ℂ) * Complex.I) a lam₁
      + SigmaP3 q (χ ^ 3) ((σ : ℂ) + ((2 * γ₁ + γ₀) : ℂ) * Complex.I) a lam₁)

end Work.ZeroFreeTables
