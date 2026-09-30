import Mathlib
import ChallengeDeps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared definitions for `annals_bounded_multiplicative_functions` (DEFINITIONS ONLY)

To be created as `Submission/Work/BMF/Defs.lean`, namespace `Work.BMF`.

It reuses the challenge's own `𝔻`, `M`, `weakGowersUniformityNorm` and `IsOneBounded`
(from `ChallengeDeps`, namespace `BoundedMultiplicativeFunctions`) and adds only the vocabulary
of the MRT/MRTTZ argument:

* `eC t = e(t) = exp(2πit)`, `natIcc a b = ℕ ∩ [a, b]`, `primesIn a b`;
* `corr f P x L = Σ_{n ∈ [x, x+L]} f(n) e(-P(n))`, the local correlation;
* `dil a P = P(a ·)`: the pushforward `(1/a)_*(I, P) = (I/a, P(a ·))`;
* `IntegralOn δ γ`: `γ(δℤ) ⊆ ℤ` (the group `Poly(δℤ → ℤ)` of the paper);
* `PolyRel k C δ`: the comparability relation `φ₁ ~_δ φ₂` with explicit constant `C`;
* `IsFam X L S`: an `(X, L)`-family of left endpoints (intervals `[x, x+L]`);
* `PhaseFamily`, `QuadData`, `ADIData`: the data passed between the pipeline nodes;
* `TwistCorr`, `IsPeriodicBdd`, `PretendsTo`: the interface to the Matomäki–Radziwiłł node.
-/

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

namespace Work.BMF

/-- The additive character `e(t) = exp(2π i t)`. -/
noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- The natural numbers in the real interval `[a, b]`. -/
noncomputable def natIcc (a b : ℝ) : Finset ℕ := Finset.Icc ⌈a⌉₊ ⌊b⌋₊

/-- The primes in the real interval `[a, b]`. -/
noncomputable def primesIn (a b : ℝ) : Finset ℕ := (natIcc a b).filter Nat.Prime

/-- A prime in the real interval `[a, b]`. -/
def IsPrimeIn (a b : ℝ) (p : ℕ) : Prop := p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b

/-- `π₀(P) = P / log P`. -/
noncomputable def pi0 (P : ℝ) : ℝ := P / Real.log P

/-- The local correlation `Σ_{n ∈ ℕ ∩ [x, x+L]} f(n) e(-P(n))`. -/
noncomputable def corr (f : ℕ → ℂ) (P : ℝ[X]) (x L : ℝ) : ℂ :=
  ∑ n ∈ natIcc x (x + L), f n * eC (-(P.eval (n : ℝ)))

/-- Dilation `P ↦ P(a ·)`. -/
noncomputable def dil (a : ℝ) (P : ℝ[X]) : ℝ[X] := P.comp (Polynomial.C a * Polynomial.X)

/-- `γ` maps the lattice `δℤ` into `ℤ`. -/
def IntegralOn (δ : ℝ) (γ : ℝ[X]) : Prop := ∀ n : ℤ, ∃ m : ℤ, γ.eval (δ * n) = m

/-- The relation `(I₁, P₁) ~_δ (I₂, P₂)` with constant `C`, for `I_i = [x_i, x_i + L_i]`:
the intervals are comparable, and `P₁ = ε + P₂ + γ` with `deg ε, deg γ ≤ k`,
`|ε| ≤ C` on `I₁`, and `γ(δℤ) ⊆ ℤ`. -/
def PolyRel (k : ℕ) (C δ : ℝ) (x₁ L₁ : ℝ) (P₁ : ℝ[X]) (x₂ L₂ : ℝ) (P₂ : ℝ[X]) : Prop :=
  L₁ ≤ C * L₂ ∧ L₂ ≤ C * L₁ ∧ |x₁ - x₂| ≤ C * L₁ ∧
    ∃ ε γ : ℝ[X], ε ∈ degreeLE ℝ (k : WithBot ℕ) ∧ γ ∈ degreeLE ℝ (k : WithBot ℕ) ∧
      P₁ = ε + P₂ + γ ∧ (∀ t ∈ Set.Icc x₁ (x₁ + L₁), |ε.eval t| ≤ C) ∧ IntegralOn δ γ

/-- An `(X, L)`-family: left endpoints `x` of intervals `[x, x+L] ⊆ [X/10, 10X]`,
pairwise at distance at least `500 L`. -/
def IsFam (X L : ℝ) (S : Finset ℝ) : Prop :=
  (∀ x ∈ S, X / 10 ≤ x ∧ x + L ≤ 10 * X) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 500 * L ≤ |x - y|

/-- An edge `(I₁, I₂, p₁, p₂)` of the MRT graph, recorded by the left endpoints of `I₁, I₂`. -/
structure Edge where
  x₁ : ℝ
  x₂ : ℝ
  p₁ : ℕ
  p₂ : ℕ

/-- Geometry of an edge: both endpoints in `S`, distinct, `p₁ ≠ p₂` primes in `[P, 2P]`,
and `I₁` within `100 L` of `(p₂/p₁) I₂` (left endpoints). -/
def EdgeGeom (S : Finset ℝ) (P L : ℝ) (e : Edge) : Prop :=
  e.x₁ ∈ S ∧ e.x₂ ∈ S ∧ e.x₁ ≠ e.x₂ ∧ e.p₁ ≠ e.p₂ ∧ IsPrimeIn P (2 * P) e.p₁ ∧
    IsPrimeIn P (2 * P) e.p₂ ∧ |e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂| ≤ 100 * L

/-- The edge relation `(1/p₂)_* φ_{I₁} ~_δ (1/p₁)_* φ_{I₂}` for the phases `pol`. -/
def EdgeRel (k : ℕ) (C δ L : ℝ) (pol : ℝ → ℝ[X]) (e : Edge) : Prop :=
  PolyRel k C δ (e.x₁ / e.p₂) (L / e.p₂) (dil e.p₂ (pol e.x₁))
    (e.x₂ / e.p₁) (L / e.p₁) (dil e.p₁ (pol e.x₂))

/-- A large `(X, L)`-family of intervals `[x, x+L]`, each carrying a degree-`≤ k` phase `pol x`
with which `f` correlates: `|Σ_{n ∈ [x, x+L]} f(n) e(-pol x (n))| ≥ c L`. -/
structure PhaseFamily (k : ℕ) (f : ℕ → ℂ) (c X L : ℝ) where
  fam : Finset ℝ
  pol : ℝ → ℝ[X]
  isFam : IsFam X L fam
  card_ge : c * (X / L) ≤ (fam.card : ℝ)
  deg : ∀ x ∈ fam, pol x ∈ degreeLE ℝ (k : WithBot ℕ)
  corr_ge : ∀ x ∈ fam, c * L ≤ ‖corr f (pol x) x L‖

/-- Output of the Turán–Kubilius / scaling-down stage (MRTTZ Prop. 3.6, MRT Prop. 3.2):
a phase family at scale `(X, L)` together with `≥ c π₀(P₁)² (X/L)` edges, each satisfying the
edge relation modulo `1/p` for `≥ c π₀(P₂)` primes `p ∈ [P₂/2, P₂]`. -/
structure QuadData (k : ℕ) (f : ℕ → ℂ) (c C X L P₁ P₂ : ℝ) extends PhaseFamily k f c X L where
  edges : Finset Edge
  edges_card : c * pi0 P₁ ^ 2 * (X / L) ≤ (edges.card : ℝ)
  geom : ∀ e ∈ edges, EdgeGeom fam P₁ L e
  rel : ∀ e ∈ edges, ∃ S : Finset ℕ, (∀ p ∈ S, IsPrimeIn (P₂ / 2) P₂ p) ∧
    c * pi0 P₂ ≤ (S.card : ℝ) ∧ ∀ p ∈ S, EdgeRel k C (1 / (p : ℝ)) L pol e

/-- Approximate dilation invariance along the edge `e` (MRTTZ Prop. 3.7 (i)–(iii)): natural
numbers `b_i < a_i` in `[P₁^ℓ, (2P₁)^ℓ]` with `a_i - b_i ≍ a_i / N`, and a set `S` of
`≥ c π₀(P₂)` primes in `[P₂/2, P₂]` such that, with modulus `Q = ∏ S`, the edge relation holds
modulo `1/Q` and `(1/a_i)_* φ_{I_i} ~_{1/Q} (1/b_i)_* φ_{I_i}` for `i = 1, 2`. -/
def ADIEdge (k : ℕ) (c C N L P₁ P₂ : ℝ) (ℓ : ℕ) (pol : ℝ → ℝ[X]) (e : Edge) : Prop :=
  ∃ a₁ b₁ a₂ b₂ : ℕ, ∃ S : Finset ℕ, (∀ p ∈ S, IsPrimeIn (P₂ / 2) P₂ p) ∧
    c * pi0 P₂ ≤ (S.card : ℝ) ∧
    P₁ ^ ℓ ≤ (b₁ : ℝ) ∧ b₁ < a₁ ∧ (a₁ : ℝ) ≤ (2 * P₁) ^ ℓ ∧
    P₁ ^ ℓ ≤ (b₂ : ℝ) ∧ b₂ < a₂ ∧ (a₂ : ℝ) ≤ (2 * P₁) ^ ℓ ∧
    (a₁ : ℝ) ≤ C * N * ((a₁ : ℝ) - b₁) ∧ N * ((a₁ : ℝ) - b₁) ≤ C * a₁ ∧
    (a₂ : ℝ) ≤ C * N * ((a₂ : ℝ) - b₂) ∧ N * ((a₂ : ℝ) - b₂) ≤ C * a₂ ∧
    EdgeRel k C (1 / ((∏ p ∈ S, p : ℕ) : ℝ)) L pol e ∧
    PolyRel k C (1 / ((∏ p ∈ S, p : ℕ) : ℝ)) (e.x₁ / a₁) (L / a₁) (dil a₁ (pol e.x₁))
      (e.x₁ / b₁) (L / b₁) (dil b₁ (pol e.x₁)) ∧
    PolyRel k C (1 / ((∏ p ∈ S, p : ℕ) : ℝ)) (e.x₂ / a₂) (L / a₂) (dil a₂ (pol e.x₂))
      (e.x₂ / b₂) (L / b₂) (dil b₂ (pol e.x₂))

/-- Output of the graph-theoretic stage (MRTTZ Prop. 3.7): a phase family with
`≥ c π₀(P₁)² (X/L)` edges, each carrying approximate dilation invariance data. -/
structure ADIData (k : ℕ) (f : ℕ → ℂ) (c C X L P₁ P₂ : ℝ) (ℓ : ℕ)
    extends PhaseFamily k f c X L where
  edges : Finset Edge
  edges_card : c * pi0 P₁ ^ 2 * (X / L) ≤ (edges.card : ℝ)
  geom : ∀ e ∈ edges, EdgeGeom fam P₁ L e
  adi : ∀ e ∈ edges, ADIEdge k c C (X / L) L P₁ P₂ ℓ pol e

/-- `ψ` is `r`-periodic on `ℕ` and `1`-bounded, with `r ≥ 1`. -/
def IsPeriodicBdd (r : ℕ) (ψ : ℕ → ℂ) : Prop :=
  0 < r ∧ (∀ n, ψ (n + r) = ψ n) ∧ ∀ n, ‖ψ n‖ ≤ 1

/-- The twisted short-interval hypothesis of the Matomäki–Radziwiłł node:
`∫_Y^{2Y} |Σ_{y ≤ n ≤ y+H'} f(n) ψ(n) n^{-iT₀}| dy ≥ η H' Y`. -/
def TwistCorr (f ψ : ℕ → ℂ) (T₀ Y H' η : ℝ) : Prop :=
  η * H' * Y ≤ ∫ y in Y..(2 * Y),
    ‖∑ n ∈ natIcc y (y + H'), f n * ψ n * (n : ℂ) ^ (-(Complex.I * T₀))‖

/-- `f` pretends to be `n ↦ χ(n) n^{it}` at scale `Y` within `B`, for a character of modulus
`1 ≤ q ≤ Q`. -/
def PretendsTo (f : ℕ → ℂ) (Q : ℕ) (B Y t : ℝ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ∃ χ : DirichletCharacter ℂ q,
    𝔻 f (fun n ↦ χ n * (n : ℂ) ^ (Complex.I * t)) Y ≤ B

end Work.BMF
