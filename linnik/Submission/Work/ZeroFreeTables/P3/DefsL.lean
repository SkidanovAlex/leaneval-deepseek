/-
# ZeroFreeTables/P3/DefsL — the free-scale, coefficient-correct form of HB's `Σ(s,χ)` (8.4)

## The coefficient

HB (8.4) defines

  `Σ(s,χ) = 𝓛⁻¹ Σ_k a_k α^k/(k-1)! Σ_n Λ(n) Re(χ(n)n^{-s}) (𝓛⁻¹ log n)^{k-1}`,  `α = a + λ₁`,

and for `P₃(X) = X + X² + (2/3)X³` (the third polynomial of (4.12)) one has `a₁ = a₂ = 1`,
`a₃ = 2/3`, so the smoothing weight is

  `u(y) = α + α² y + (a₃/2!) α³ y² = α + α² y + (1/3) α³ y²`

(equivalently `u(y) = α(1 + αy + α²y²/3)`), whose Laplace transform is exactly
`∫₀^∞ e^{-zt} u(t) dt = α/z + α²/z² + (2/3)α³/z³ = P₃(α/z)` (using `∫₀^∞ t^n e^{-zt} = n!/z^{n+1}`).
This is what makes HB's §8 computation `Σ(s,χ) = −Σ_ρ Re P₃(α/((s−ρ)𝓛)) + O(1)` — and hence
(9.8), with its `P₃(α/(a+λ₀))`, `P₃(1)`, `A913` — literally true, and it is the source of the
numerical agreement of Table 8.

**Caution.**  The earlier definitions `Work.ZeroFreeTables.SigmaP3` and
`Work.ZeroFreeTables.HbCombination` in `P3/Defs.lean` carry the coefficient `2/3` instead of
`1/3` in the `y²` term (i.e. they are the functional of `X + X² + (4/3)X³`, not of `P₃`).
They are *not* used by this development (the proved `P3/Pointwise91.lean` is a statement about
`HbCombination`, valid for any non-negative weight, but it is not the inequality this
derivation needs).  The corrected definitions live below and are the ones the engine and the
assembly use.

## The scale `L`

`SigmaP3` of `Defs.lean` hard-codes the logarithmic scale `Real.log q` of the modulus; the
engine of HB §8 is applied to a *primitive* character whose conductor may be smaller than the
modulus of the ambient `Σ` (the imprimitive case), so the scale has to be a free parameter
`L ≥ log N`.
-/
import Submission.Work.ZeroFreeTables.P3.Defs
import Submission.Work.ZeroFreeTables.P3.Imports

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- HB's `Σ(s,χ)` of (8.4) with a free logarithmic scale `L` and the coefficient-correct
weight `u(y) = α + α²y + (1/3)α³y²` (whose Laplace transform is `P₃(α/z)`):

`Σ(s,χ) = L⁻¹ Σ_n Λ(n) Re(χ(n) n^{-s}) u(log n / L)`, `α = a + λ₁`.
Absolutely convergent for `Re s > 1`; `L` will be `log q` with `log N ≤ L`. -/
def SigmaP3L (N : ℕ) [NeZero N] (L : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ)
    (a lam₁ : ℝ) : ℝ :=
  L⁻¹ * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
    (χ (n : ZMod N) / (n : ℂ) ^ s).re *
    ((a + lam₁) + (a + lam₁) ^ 2 * (Real.log n / L)
      + (1/3) * (a + lam₁) ^ 3 * (Real.log n / L) ^ 2)

/-- HB's smoothing weight `u(y) = α + α²y + (1/3)α³y²` at `y = log n / L`. -/
def hbWL (L : ℝ) (a lam₁ : ℝ) (n : ℕ) : ℝ :=
  (a + lam₁) + (a + lam₁) ^ 2 * (Real.log n / L)
    + (1/3) * (a + lam₁) ^ 3 * (Real.log n / L) ^ 2

/-- `SigmaP3L` as a sum of its summands. -/
theorem SigmaP3L_eq_tsum (N : ℕ) [NeZero N] (L : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ)
    (a lam₁ : ℝ) :
    SigmaP3L N L χ s a lam₁ = L⁻¹ * ∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) * (χ (n : ZMod N) / (n : ℂ) ^ s).re
        * hbWL L a lam₁ n := rfl

/-- HB (9.1) at the scale `L = log q`, with the coefficient-correct weight: the eight-term
combination coming from the pointwise inequality
`0 ≤ χ₀(n)(1 + Re z₀)(K + Re z₁)²`, `z_j = χ(n)n^{-iγ_j}`, at the points `σ`, `σ+iγ₀`,
`σ+i(γ₁−γ₀)`, `σ+iγ₁`, `σ+i(γ₁+γ₀)`, `σ+i(2γ₁−γ₀)`, `σ+2iγ₁`, `σ+i(2γ₁+γ₀)` and the
characters `χ₀, χ, χ₀, χ, χ², χ, χ², χ³`.

This is the corrected analogue of `Work.ZeroFreeTables.HbCombination` of `P3/Defs.lean`
(whose `y²`-coefficient is wrong by a factor 2). -/
def HbCombinationL (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ₀ γ₁ a lam₁ : ℝ) : ℝ :=
  (K ^ 2 + 1/2) * (SigmaP3L q (Real.log q) 1 (σ : ℂ) a lam₁
      + SigmaP3L q (Real.log q) χ ((σ : ℂ) + (γ₀ : ℂ) * Complex.I) a lam₁)
  + K * (SigmaP3L q (Real.log q) 1 ((σ : ℂ) + ((γ₁ - γ₀) : ℂ) * Complex.I) a lam₁
      + 2 * SigmaP3L q (Real.log q) χ ((σ : ℂ) + (γ₁ : ℂ) * Complex.I) a lam₁
      + SigmaP3L q (Real.log q) (χ ^ 2) ((σ : ℂ) + ((γ₁ + γ₀) : ℂ) * Complex.I) a lam₁)
  + (1/4) * (SigmaP3L q (Real.log q) χ ((σ : ℂ) + ((2 * γ₁ - γ₀) : ℂ) * Complex.I) a lam₁
      + 2 * SigmaP3L q (Real.log q) (χ ^ 2) ((σ : ℂ) + ((2 * γ₁) : ℂ) * Complex.I) a lam₁
      + SigmaP3L q (Real.log q) (χ ^ 3) ((σ : ℂ) + ((2 * γ₁ + γ₀) : ℂ) * Complex.I) a lam₁)

/-- The divisor of the completed `L`-function, restricted to the ball that the
near-zero sums of HB §§5, 8, 9 use (`|s.im| ≤ 1` makes this `closedBall 0 3`). -/
def pdiv (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ → ℤ :=
  fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
    (Metric.closedBall 0 (|s.im| + 2)) u

/-- The near-zero sum of HB (9.2)–(9.7): the zeros of the completed `L`-function within
`δ` of the test point `1 + i·Im s`, weighted by multiplicity and by `Re P₃(α/((s-u)L))`. -/
def P3NearSumL (N : ℕ) [NeZero N] (L : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ)
    (a lam₁ δ : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, ((pdiv N χ s u : ℤ) : ℝ) *
    (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      then (P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re else 0)

/-- The near-zero sum of HB Lemma 3.1: the zeros of the completed `L`-function within `δ`
of `1 + i·Im s`, weighted by multiplicity and by `Re (1/(s-u))`. -/
def InvNearSum (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (δ : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, ((pdiv N χ s u : ℤ) : ℝ) *
    (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0)

/-- The hypothesis of HB Lemma 3.1 at radius `δ`, scale `L` and error coefficient `c`:
`-Re (L'/L)(s) + Σ_{near} Re(1/(s-u)) ≤ c·L` on the region of the lemma.  This is the
conclusion of the proved `Commons.NumberTheory.Linnik.lemma3_1` with `φ = 1/3` and error `ε`
(i.e. `c = 1/6 + ε`). -/
def LogDerivHyp {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (δ L c : ℝ) : Prop :=
  ∀ s : ℂ, 1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L → |s.im| ≤ L →
    (-logDeriv (DirichletCharacter.LFunction χ) s).re + InvNearSum N χ s δ ≤ c * L

end Work.ZeroFreeTables
