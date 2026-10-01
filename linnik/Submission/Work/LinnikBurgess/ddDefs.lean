import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_levelSum_nondegenerate
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_cube_local
import Submission.Commons.NumberTheory.GaussSum.quadratic_phase_prime_pow
import Submission.Commons.NumberTheory.ExponentialSums.additive_weil_bound_poly

/-!
# Vocabulary for the doubly degenerate critical level-sum bound

This module holds the definitions shared by `Work.LinnikBurgess.dd_criticalSumBound` and the
lemmas it is assembled from.

## The mathematical problem

Let `p` be an odd prime, `χ` a primitive character modulo `p ^ e` (`e ≥ 4`), and let
`A, C : Fin 3 → ZMod (p^e)` be two triples.  The *level sum* of interest (an instance of
`Commons.NumberTheory.DirichletCharacter.levelSum3`) is

`∑_{w : ZMod (p^(e-2))} χ (∏_l (1 + p A_l w)) * conj (χ (∏_l (1 + p C_l w)))`.

In the application `A_l = gammaU p e r (a l) = (r + a_l)⁻¹` and `C_l = gammaU p e r (b l)`,
and `r` is a *doubly degenerate* critical class (`IsDD p e a b r`), which gives

(D1) `p^2 ∣ (∑ A - ∑ C).val`,
(D2) `p ∣ (∑ A^2 - ∑ C^2).val`.

If in addition a *cubic* doubly degenerate class exists somewhere, then the third defect is a unit,

(D3) `¬ p ∣ (∑ A^3 - ∑ C^3).val`,

and one proves `‖levelSum3 p e 1 (e-2) χ A C‖ ≤ 8 p^(2e/3 - 1)`.

## The strategy (for the analytic core)

Write `Φ(w) = ∏_l (1+pA_lw)/∏_l (1+pC_lw)` (this is `prodCoord3 p e 1 A C w`).  Then
`Φ(w) = 1 + p·u(w)`, and `χ(Φ(w)) = χ(1+p·u(w))`.  The map `u ↦ χ (1 + p * u)` is a character of
`ZMod (p^(e-1))` (the group `1+pZ` is cyclic), so there are a unit `λ` and, for each `w`, an
element `v(w) ∈ ZMod (p^(e-1))` with `χ(Φ(w)) = ζ^(λ v(w))`; concretely one may use
`χ (1 + p*y) = (χ (1 + p))^y`-type manipulations.  Hence the level sum is an exponential sum of a
*p-adic phase* `v`, and

* (D1),(D2) say `v(w) ≡ 0 mod p^2` (the linear and quadratic coefficients of `v` are `p^2`-small),
  so the summand is periodic with period `p^(e-3)` and the level sum is `p` times the sum over
  `ZMod (p^(e-3))`;
* the expansion `u(w) = ∑ c_k w^k` satisfies `c_3 = p^2 δ/3 + …` with `δ` the cubic defect, which
  is a *unit* by (D3).  Therefore the normalized phase `v/p^2` is a genuine cubic modulo `p`, with
  unit cubic coefficient: the sum is a complete *cubic* `p`-adic Weyl sum
  `∑_{w : ZMod (p^K)} e_p^K (β w + γ w^2 + δ w^3 + p R(w))`, `K = e-3`, `p ∤ δ`.

The extremal family `a_l^3 = p^3+1`, `b_l^3 = p^3-1` (for `p ≡ 1 mod 3`) attains
`‖levelSum3‖ = p^(2e/3-1)`, so the exponent `2/3` and the shape of the bound are sharp.

## Detailed plan for `dd_levelSum_eq_cubicSum` (piece 2)

Write `Φ(w) = prodCoord3 p e 1 A C w = ∏_l (1+pA_lw)·(∏_l (1+pC_lw))⁻¹` and
`Δ_k = ddDsum p e k A C`.  The expansion of `Φ` as a power series in `w` (truncated at `p^e`)

`Φ(w) = 1 + p·Δ_1·w + p²E_2·w² + p³E_3·w³ + …`

has, with `e_i` the elementary symmetric functions of the triples,
`E_2 = e₂(A) - e₁(A)e₁(C) + e₁(C)² - e₂(C)` and
`E_3 = e₃(A) - e₂(A)e₁(C) + e₁(A)(e₁(C)²-e₂(C)) - (e₁(C)³-2e₁(C)e₂(C)+e₃(C))`.
Two algebraic facts (pure `ring` computations; verified numerically for p = 5,7,11,13, e = 4,5,6):

* from `Δ_1 ≡ 0 (mod p²)` and `Δ_2 ≡ 0 (mod p)`: `E_2 ≡ 0 (mod p)`, hence
  `Φ(w) ≡ 1 (mod p³)` and `χ(Φ(w)) = χ(1+p³·u(w))` with `u(w) = (Φ(w)-1)/p³` read in
  `ZMod (p^(e-3))`; the summand is therefore `p^(e-3)`-periodic and
  `levelSum3 p e 1 (e-2) = p · ∑_{w : ZMod (p^(e-3))} χ (Φ w)`.
* `3·E_3 ≡ Δ_3 (mod p)`; since `p ∤ Δ_3` and `p ≥ 5` (so `3` is invertible), the cubic
  coefficient of `u` is a unit.

Finally `u ↦ χ (1+p³u)` is a character of `ZMod (p^(e-3))` (the group `1+p³Z/p^e` is cyclic) and
`hχ` makes it non-trivial, hence `χ (1+p³u) = ζ^(λ''u)` with `λ''` a unit; multiplying `u` by the
integer `λ''` and lifting the coefficients of `u` to integers produces the `H` of the statement
with `IsCubic p H`.

## Detailed plan for `cubic_phase_prime_pow` (piece 3)

Induction on `K`; the quadratic analogue is `Commons.NumberTheory.GaussSum.quadratic_phase_prime_pow`.

* Peel: for `K ≥ 2`, split the index `j < p^K` as `j = j' + p^(K-1)t`; all terms of the Taylor
  expansion of `H(j'+p^(K-1)t) - H(j')` beyond the first vanish modulo `p^K` (the `t²` term is
  `p^(2K-2)`, and `2K-2 ≥ K`), so
  `Tsum (p^K) H = p · ∑_{j' < p^(K-1), p ∣ H'(j')} E (p^K) (H j')`.
* The congruence `p ∣ H'(j')` is, modulo `p`, the quadratic equation `β + 2γX + 3δX² = 0`
  (`H' = β + 2γX + 3δX² + pR'`), which has at most two roots (`p ∤ 3δ` since `p ≥ 5`, `p ∤ δ`);
  a double root occurs iff also `H''` vanishes at the (unique) root modulo `p`.
* Simple root `a₀` (that is `H''(a₀) ≢ 0 mod p`): summing over `u` with `j' = a₀ + p u`,
  `Tsum(p^K,H) = p·E(p^K, H a₀)·∑_{u<p^(K-2)} E(p^(K-2), (H(a₀+pu)-H(a₀))/p²)`, and the inner
  phase `μu + (H''(a₀)/2)u² + (p/6)H'''(a₀)u³ + …` is a quadratic phase with unit quadratic
  coefficient and `p`-multiple remainder, so `quadratic_phase_prime_pow` gives `≤ 2 p^((K-2)/2)`,
  whence `|Tsum(p^K,H)| ≤ 2p·2p^((K-2)/2) = 4p^(K/2) ≤ 8p^(2K/3)`.
* Double root (`H''(a₀) ≡ 0 mod p`, hence a unique root `a₀`, and `H'(a₀) = pμ`):
  - If `p ∤ μ`: the inner sum over `u` has full linear frequency `μ p`, and orthogonality over a
    complete period gives `0`.
  - If `p ∣ μ`: the inner phase is divisible by `p²` and the inner sum is `p` times a cubic sum
    over `p^(K-3)` with the same `IsCubic` shape, so the induction gives
    `|Tsum(p^K,H)| ≤ p·p·8p^(2(K-3)/3) = 8p^(2K/3)`.
* Base cases: `K = 0`: `Tsum 1 H = 1`.  `K = 1`: `|Tsum(p,H)| ≤ 2·3·√p ≤ 8p^(2/3)` by
  `additive_weil_bound_poly` (`H mod p` has degree `3 < p`).  `K = 2`: the peel gives
  `≤ 2p ≤ 8p^(4/3)`.  `K = 3`: the trivial bound `p² ≤ 8p²` suffices.

-/

namespace Work.LinnikBurgess

/-- The `k`-th power-sum defect of the pair `(A, C)`: `∑ A^k - ∑ C^k` in `ZMod (p^e)`. -/
noncomputable def ddDsum (p e k : ℕ) (A C : Fin 3 → ZMod (p ^ e)) : ZMod (p ^ e) :=
  (∑ l : Fin 3, (A l) ^ k) - (∑ l : Fin 3, (C l) ^ k)

/-- A polynomial over `ℤ` whose reduction modulo `p` is a *genuine cubic*, up to a multiple of
`p`: `H = β X + γ X^2 + δ X^3 + p R` with `p ∤ δ`. -/
def IsCubic (p : ℕ) (H : Polynomial ℤ) : Prop :=
  ∃ β γ δ : ℤ, ∃ R : Polynomial ℤ, ¬ (p : ℤ) ∣ δ ∧
    H = Polynomial.C β * Polynomial.X + Polynomial.C γ * Polynomial.X ^ 2
      + Polynomial.C δ * Polynomial.X ^ 3 + Polynomial.C (p : ℤ) * R

end Work.LinnikBurgess
