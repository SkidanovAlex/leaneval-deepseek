import Mathlib

/-!
# The Ionescu–Wainger multiplier vocabulary (Mirek–Stein–Trojan, arXiv:1512.07518)

Trusted sources for this chapter are `REFS/MirekSteinTrojan_1512.07518_maximal.tex` (MST) and
`REFS/Tao_2008.05066_IonescuWainger.tex` (Tao's clean proof of the Ionescu–Wainger theorem).

MST §2 "Estimates for Ionescu–Wainger type multipliers" introduce, for a parameter `ρ > 0`:

* `N₀ = ⌊N^{ρ/2}⌋ + 1` and `Q₀ = (N₀!)^{D}`, `D = ⌊2/ρ⌋ + 1`;
* `ℙ_N = ℙ ∩ (N₀, N]` (primes strictly between `N₀` and `N`);
* `Π_k(V)` = products `p_1^{γ_1}···p_k^{γ_k}` with `p_1, …, p_k ∈ V` **distinct** and
  `γ_l ∈ {1, …, D}`; `Π(V) = ⋃_{k ≤ D} Π_k(V)`;
* `P_N = { q = Q·w : Q | Q₀, w ∈ Π(ℙ_N) ∪ {1} }`, so that `ℕ_N ⊆ P_N ⊆ ℕ_{e^{N^ρ}}` and `|P_N| ≤ e^{N^ρ}`;
* `A_q = { a ∈ ℕ_q^d : gcd(q, (a_γ : γ ∈ Γ)) = 1 }` and
  `𝒰_N = ℛ(P_N) = { a/q : a ∈ A_q, q ∈ P_N } ⊂ 𝕋^d`.

The Ionescu–Wainger type multiplier is then, for a symbol `Θ` on `ℝ^d`, a bump `η` and a diagonal
scaling matrix `ℰ_N = diag(ε_γ)` with `ε_γ ≤ e^{-N^{2ρ}}`,

`Δ_N(ξ) = Σ_{a/q ∈ 𝒰_N} Θ(ξ − a/q) · η((ξ − a/q)/ε)`  (coordinatewise in the last factor).

This file only records that vocabulary; the theorem (`iw_multiplier_lp`, MST Theorem 3 / eq. (5))
and its proof live in `Submission/Work/BourgainPlan/IonescuWainger/multiplier.lean`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- MST's `N₀ = ⌊N^{ρ/2}⌋ + 1`. -/
noncomputable def iwN0 (ρ : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1

/-- MST's `D = D_ρ = ⌊2/ρ⌋ + 1`. -/
noncomputable def iwDeg (ρ : ℝ) : ℕ := ⌊2 / ρ⌋₊ + 1

/-- MST's `Q₀ = (N₀!)^D`. -/
noncomputable def iwQ0 (ρ : ℝ) (N : ℕ) : ℕ := (iwN0 ρ N).factorial ^ iwDeg ρ

/-- MST's `ℙ_N = ℙ ∩ (N₀, N]`: the primes strictly between `N₀` and `N`. -/
def iwPrimeSet (N₀ N : ℕ) : Finset ℕ := (Finset.Icc (N₀ + 1) N).filter Nat.Prime

/-- MST's `Π_k(V)`: products of `k` **distinct** primes of `V` with exponents in `{1, …, D}`. -/
noncomputable def iwPiK (D : ℕ) (V : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (V.powerset.filter (fun t => t.card = k)).biUnion fun t =>
    ((t.pi fun _ => Finset.Icc 1 D)).image fun f => t.attach.prod fun p => p.1 ^ f p.1 p.2

/-- MST's `Π(V) = ⋃_{k ≤ D} Π_k(V)`. -/
noncomputable def iwPi (D : ℕ) (V : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 D).biUnion fun k => iwPiK D V k

/-- MST's `P_N = {Q·w : Q | Q₀, w ∈ Π(ℙ_N) ∪ {1}}`. -/
noncomputable def iwPN (ρ : ℝ) (N : ℕ) : Finset ℕ :=
  (iwQ0 ρ N).divisors.biUnion fun Q =>
    (iwPi (iwDeg ρ) (iwPrimeSet (iwN0 ρ N) N) ∪ {1}).image fun w => Q * w

/-- MST's `A_q = {a ∈ ℕ_q^d : gcd(q, (a_γ)) = 1}` (a finite set of `d`-tuples). -/
noncomputable def iwAq (d q : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.range q)).filter
    fun a => Nat.Coprime q (Finset.univ.gcd fun γ => a γ)

/-- MST's `𝒰_N = ℛ(P_N)`, indexed by the pair `(a, q)` (so `a/q` is the corresponding torus
point). -/
noncomputable def iwUN (ρ : ℝ) (d N : ℕ) : Finset ((Fin d → ℕ) × ℕ) :=
  (iwPN ρ N).biUnion fun q => (iwAq d q).image fun a => (a, q)

/-- The Ionescu–Wainger type multiplier `Δ_N` of MST, for a symbol `Θ` on `ℝ^d`, a bump `η` and a
diagonal scaling `ε` (MST's `ℰ_N = diag(ε_γ)`):

`Δ_N(ξ) = Σ_{a/q ∈ 𝒰_N} Θ(ξ − a/q) · η((ξ − a/q)/ε)`,

where the last factor is evaluated coordinatewise: `(η(ξ/ε))_γ = η(ξ_γ/ε_γ)`. -/
noncomputable def iwDelta (ρ : ℝ) (d N : ℕ) (Θ : (Fin d → ℝ) → ℂ) (η : (Fin d → ℝ) → ℂ)
    (ε : Fin d → ℝ) (ξ : Fin d → ℝ) : ℂ :=
  ∑ p ∈ iwUN ρ d N, Θ (ξ - fun γ => (p.1 γ : ℝ) / (p.2 : ℝ)) *
    η (fun γ => (ξ γ - (p.1 γ : ℝ) / (p.2 : ℝ)) / ε γ)

/-- The Fourier transform of a finite measure on `ℝ^d`, in Mathlib's convention
(`𝓕 f ξ = ∫ x, e(-⟪x,ξ⟫) f x`).  This is the class of symbols used in MST §4: their `Θ = Φ_N` is
the Fourier transform of the pushforward of Lebesgue measure on `[0,1]^k` under `y ↦ 𝒬(Ny)`, a
probability measure, so the associated multiplier is an `L^p` contraction. -/
noncomputable def measureFourier {d : ℕ} (μ : Measure (Fin d → ℝ)) (ξ : Fin d → ℝ) : ℂ :=
  ∫ x, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ γ, x γ * ξ γ : ℝ) : ℂ))) ∂μ

/-- The Fourier multiplier operator on `ℓ^p(ℤ^d)` associated with a symbol `m` on the torus: the
finitely supported `f` is identified with its trigonometric polynomial and `m` is applied on the
Fourier side. -/
noncomputable def mulOp (d : ℕ) (m : (Fin d → ℝ) → ℂ) (s : Finset (Fin d → ℤ))
    (f : (Fin d → ℤ) → ℂ) (x : Fin d → ℤ) : ℂ :=
  ∫ ξ in Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1),
    m ξ * (∑ n ∈ s, f n *
      Complex.exp (2 * Real.pi * Complex.I * ((∑ γ, (n γ : ℝ) * ξ γ : ℝ) : ℂ))) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((∑ γ, (x γ : ℝ) * ξ γ : ℝ) : ℂ)))

end Work.BourgainPlan.IonescuWainger
