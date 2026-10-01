import Mathlib
import Submission.Work.LinnikContract.Defs

/-!
# The Selberg sieve of Graham's proof of the Deuring–Heilbronn phenomenon

* [BGTZ] Benli–Goel–Twiss–Zaman, *Explicit Deuring–Heilbronn phenomenon for Dirichlet
  `L`-functions*, arXiv:2410.06082, §3;
* [Graham] S. Graham, *Applications of the sieve to Dirichlet `L`-functions*, PhD thesis 1977,
  §9 (Lemma 9.6).

Fixes the vocabulary of the chapter: for a real quadratic character `χ₁` mod `q` with an
exceptional real zero `β₁`,

* `aFun χ₁ n = Σ_{d | n} χ₁(d)` (non-negative and multiplicative);
* `gPrime χ₁ p = (Σ_{k ≥ 1} a(p^k)p^{-k})^{-1}`, `hPrime χ₁ p = gPrime χ₁ p + 1`;
* `hFun`, `gFun` their multiplicative extensions (`h` totally multiplicative, `g = h ∏_{p|n}(1-1/h)`);
* `VFun χ₁ R = Σ_{ℓ ≤ R} μ²(ℓ)/g(ℓ)`;
* `thetaFun χ₁ R d` — Graham's optimal Selberg weights (BGTZ (2.6));
* `FF χ₁ χ s = Σ_n a(n)χ(n)n^{-s}` and `GF χ₁ χ R s` the Selberg-sieve function `G`,
  with `F(s,χ)G(s,χ) = Σ_n a(n)χ(n)(Σ_{d|n}θ_d)² n^{-s}`.
-/

open scoped BigOperators
open DirichletCharacter

namespace Work.LinnikAreas.Sieve

variable {q : ℕ}

/-- Graham's multiplicative function `a(n) = Σ_{d | n} χ₁(d)`; non-negative when `χ₁` is real. -/
noncomputable def aFun (χ₁ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (χ₁ (d : ZMod q)).re

/-- The local sieve factor `g(p) = (Σ_{k ≥ 1} a(p^k) p^{-k})^{-1}`. -/
noncomputable def gPrime (χ₁ : DirichletCharacter ℂ q) (p : ℕ) : ℝ :=
  (∑' k : ℕ, aFun χ₁ (p ^ (k + 1)) / (p : ℝ) ^ (k + 1))⁻¹

/-- `h(p) = g(p) + 1`. -/
noncomputable def hPrime (χ₁ : DirichletCharacter ℂ q) (p : ℕ) : ℝ := gPrime χ₁ p + 1

/-- `h(n) = ∏_{p^k ∥ n} h(p)^k`, the totally multiplicative extension of `h`. -/
noncomputable def hFun (χ₁ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, (hPrime χ₁ p) ^ (n.factorization p)

/-- `g(n) = h(n) ∏_{p | n} (1 - 1/h(p))`. -/
noncomputable def gFun (χ₁ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  hFun χ₁ n * ∏ p ∈ n.primeFactors, (1 - (hPrime χ₁ p)⁻¹)

/-- `V(R) = Σ_{ℓ ≤ R} μ²(ℓ)/g(ℓ)`. -/
noncomputable def VFun (χ₁ : DirichletCharacter ℂ q) (R : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 R, (if Squarefree ℓ then (1 : ℝ) else 0) / gFun χ₁ ℓ

/-- **Graham's optimal Selberg weights** `θ_d` (BGTZ (2.6)), zero off squarefree `d ≤ R`. -/
noncomputable def thetaFun (χ₁ : DirichletCharacter ℂ q) (R d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) * hFun χ₁ d / (VFun χ₁ R * gFun χ₁ d) *
    (∑ r ∈ (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d),
      (if Squarefree r then (1 : ℝ) else 0) / gFun χ₁ r)

/-- `F(s,χ) = Σ_n a(n)χ(n)n^{-s}` (absolutely convergent for `Re s > 1`). -/
noncomputable def FF (χ₁ χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (aFun χ₁ n : ℂ) * χ (n : ZMod q) / (n : ℂ) ^ s

/-- The local factor of the Selberg-sieve function `G` at the prime `p`. -/
noncomputable def Gloc (χ₁ χ : DirichletCharacter ℂ q) (s : ℂ) (p : ℕ) : ℂ :=
  (∑' k : ℕ, (aFun χ₁ (p ^ (k + 1)) : ℂ) * χ ((p : ℕ) ^ (k + 1) : ZMod q) /
      (p : ℂ) ^ ((k + 1 : ℕ) * s)) /
    (1 + ∑' k : ℕ, (aFun χ₁ (p ^ (k + 1)) : ℂ) * χ ((p : ℕ) ^ (k + 1) : ZMod q) /
      (p : ℂ) ^ ((k + 1 : ℕ) * s))

/-- The Selberg-sieve function `G(s,χ)` (BGTZ (2.3)); then
`F(s,χ)G(s,χ) = Σ_n a(n)χ(n)(Σ_{d|n}θ_d)² n^{-s}` for `Re s > 1`. -/
noncomputable def GF (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
    ((thetaFun χ₁ R d : ℂ) * (thetaFun χ₁ R e : ℂ)) *
      ∏ p ∈ (d.lcm e).primeFactors, Gloc χ₁ χ s p

end Work.LinnikAreas.Sieve
