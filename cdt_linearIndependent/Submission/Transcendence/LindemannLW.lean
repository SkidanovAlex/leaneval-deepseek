import Mathlib
import Submission.Transcendence.Hermite
import Submission.Transcendence.Lindemann
import Submission.Commons.FieldTheory.Minpoly.ConjRoots.trace_rat_poly
import Submission.Commons.FieldTheory.Minpoly.ConjRoots.norm_rat_poly
import Submission.Commons.FieldTheory.Minpoly.ConjRoots.aroots_minpoly_eq_of_common_root
import Submission.Commons.FieldTheory.Minpoly.ConjRoots.zero_not_mem_aroots_of_ne_zero
import Submission.Commons.Algebra.Polynomial.X_pow_sub_C_pow_eq_mul_sum
import Submission.Commons.Algebra.Polynomial.exists_mul_X_sub_C_of_eval
import Submission.Commons.RingTheory.IsIntegral.eval_of_coeffs
import Submission.Commons.FieldTheory.Norm.norm_isInt
import Submission.Commons.FieldTheory.Norm.norm_pow_not_mem_smul
import Submission.Commons.Polynomial.Prod.MonicProdConjClosed
import Submission.Commons.Polynomial.Prod.WeightedPowerSumsConjClosed
import Submission.Commons.Polynomial.Prod.ProdEvalConjClosed
import Submission.Commons.RingTheory.IsIntegral.finset_sum
import Submission.Commons.RingTheory.IsIntegral.isInt_of_rat

/-!
# Lindemann–Weierstrass: Lemma A (orbit relations) — polynomial core

The classical proof of the Lindemann–Weierstrass theorem is built on two
lemmas (Wikipedia, "Lindemann–Weierstrass theorem", §Proof):

* **Lemma A (orbit relations):** if `c(1),…,c(r)` are integers and, for each
  `k`, the exponents `{γ(k)_1,…,γ(k)_{m(k)}}` form the full root set of an
  integer polynomial `T_k(x)` (all roots pairwise distinct across classes),
  then `Σ_k c(k)·(e^{γ(k)_1} + ⋯ + e^{γ(k)_{m(k)}}) = 0` forces every
  `c(k) = 0`.
* **Lemma B:** distinct algebraic exponents `γ_1,…,γ_n` give
  `Σ_k b_k·e^{γ_k} ≠ 0` for any integers `b_k` not all zero (via the
  `S_N`-symmetrization / conjugate-product trick).

This module develops Lemma A.  The roadmap (see `Lindemann.lean` §11, which
supersedes the earlier §8/§8b plan): for exponents `α : Fin n → ℂ` that are
pairwise distinct and partitioned into full `conjRoots`-classes, with class
coefficients `β : Fin n → ℤ` constant on classes, a relation
`Σ_k β_k·cexp (α_k) = 0` leads to a contradiction via the auxiliary
polynomials (Wikipedia notation)

`fᵢ(x) = ℓ^{n·p}·(x−α₁)ᵖ⋯(x−αₙ)ᵖ/(x−αᵢ)`

for primes `p` (`ℓ` a fixed integer making every `ℓαₖ` an algebraic
integer), the functionals `Jᵢ = Σ_k β_k·Iᵢ(α_k)` (`Iᵢ(s) = eˢ·Σⱼfᵢ⁽ʲ⁾(0) −
Σⱼfᵢ⁽ʲ⁾(s)`, the sum over all iterated derivatives), and the two-sided
estimate of `|J₁⋯Jₙ|`.

**Status of this file.**  Contains the polynomial core and the complete
*clearing-layer arithmetic* of Lemma A (the "arithmetic side" of the
§11 roadmap), all proved over `ℂ`:

* §1 — `lemmaA_H`, `lemmaA_f`: the full product `H = ∏ₖ(X−αₖ)` and the
  auxiliary polynomial `fᵢ = ℓ^{np}·Hᵖ/(X−αᵢ)` (factored form);
  the exact factor identity `(X−C αᵢ)·fᵢ = ℓ^{np}·Hᵖ`;
* §2 — vanishing/factorial shapes of `sumIDeriv (fᵢ)` at the exponents
  (`(p!·)`-divisibility at `αₖ`, `k ≠ i`; the diagonal
  `(p−1)!·ℓ^{np}·∏_{k≠i}(αᵢ−αₖ)ᵖ + p!·(·)` at `αᵢ`), via Mathlib's
  `Polynomial.aeval_sumIDeriv(_of_pos)`;
* §3 — the divided difference: `polyDivDiff P a` with
  `(X−a)·polyDivDiff P a = P − P(a)` and, for `P = ℓ^{np}·Hᵖ` (which
  vanishes at every `αᵢ`), `fᵢ = polyDivDiff P (αᵢ)` — the foundation of the
  "symmetric step" (coefficients of `fᵢ` polynomial in `αᵢ`, independent of
  `i`).

**Already built.**  §4–§5 add the clearing-layer engine:

* §4 (`PolyInt`, namespace `Submission.Transcendence.PolyInt`) — the
  "algebraic-integer coefficients" API: sums/products/powers/subtractions and
  iterated derivatives of polynomials with integral coefficients over `ℤ`
  again have integral coefficients (`finset_sum`/`eval_of_coeffs` Commons
  lemmas supply the closure under finite sums and evaluation at integral
  points);
* §5 (scaled polynomials) — with the exponents cleared to algebraic integers
  `bₖ = ℓ·αₖ`, the auxiliary polynomial becomes `f̃ᵢ(y) = ℓ·(y−bᵢ)^{p−1}·
  ∏_{t≠i}(y−bₜ)ᵖ` (`scaledF`, with the factors `scaledQ`, `scaledR`); the
  exact root-value formulas (`deriv_X_sub_C_pow_root`,
  `deriv_mul_pow_eval_root`) give: at `bₖ` (`k ≠ i`) derivatives of order
  `< p` vanish and higher derivatives are `p!`-divisible *in the ring of
  algebraic integers* (`scaledF_deriv_offdiag_lt/_ge`), while at `bᵢ` the
  `(p−1)`-st derivative is the nonzero diagonal
  `(p−1)!·ℓ·δᵢᵖ`, `δᵢ = ∏_{k≠i}(bᵢ−bₖ)` (`scaledF_deriv_diag`), and lower
  derivatives vanish (`scaledF_deriv_diag_lt`).

**Completed §7 (clearing-layer arithmetic — new this session).**  The change
of variable `fᵢ(x) = f̃ᵢ(ℓx)` is now an *exact polynomial identity*
(`lemmaA_f_eq_scaledF_comp`), with the derivative chain rule
`(f̃ᵢ∘(ℓX))⁽ʲ⁾ = C(ℓʲ)·f̃ᵢ⁽ʲ⁾∘(ℓX)` (`iterate_derivative_comp_C_mul_X`,
`deriv_lemmaA_f_eval`), so `fᵢ⁽ʲ⁾(αₖ) = ℓʲ·f̃ᵢ⁽ʲ⁾(bₖ)`.  The *diagonal*
orders `j ≥ p` at `bᵢ` are `p!`-divisible in the ring of algebraic integers:
`derivative (∏_{t≠i}(X−bₜ)ᵖ) = C(p)·Qᵢ'` with `Qᵢ'` an integral-coefficient
sum (`scaledQderiv`, `scaledQ_deriv`, `PolyInt_scaledQderiv`), hence all
higher derivatives of `Qᵢ` at `bᵢ` carry a factor `p`
(`scaledQ_deriv_iter`, `scaledQ_deriv_eval_diag_p`) and of `f̃ᵢ` at `bᵢ` a
factor `p!` (`scaledF_deriv_diag_ge`).  The resulting **sumIDeriv arithmetic
of Lemma A with algebraic-integer remainders** (the exact statements the
class step feeds into `Jᵢ = −Σₖ βₖ·F(αₖ)`):

* `lemmaA_f_sumIDeriv_offdiag_int`: for `k ≠ i`, `F(αₖ) = p!·u` with `u` an
  algebraic integer (`F = sumIDeriv (fᵢ)`);
* `lemmaA_f_sumIDeriv_diag_int`: `F(αᵢ) =
  (p−1)!·ℓᵖ·∏_{t≠i}(ℓαᵢ−ℓαₜ)ᵖ + p!·u` with `u` an algebraic integer;
* `prod_sub_pow_ne_zero`, `mul_left_injective_of_ne_zero` (§7b): for
  pairwise-distinct cleared exponents the diagonal product is nonzero.

**Planned future sections** (roadmap `Lindemann.lean` §11, superseding
§8/§8b):

* §8 (completed) — **Lemma A assembly**: under the exponential relation
  `Σₖβₖ·cexp(αₖ)=0`, `Jᵢ := Σₖβₖ·P(fᵢ,αₖ)` collapses to `−Σₖβₖ·F(αₖ)`
  (`lemmaA_J_eq`), and that object factors as `(p−1)!·Wᵢ` with
  `Wᵢ = −βᵢ·ℓᵖ·∏_{t≠i}(ℓαᵢ−ℓαₜ)ᵖ − p·Sᵢ`, `Sᵢ ∈ ℤ̄`
  (`lemmaA_J_shape`); so each `Jᵢ` is an algebraic integer divisible by
  `(p−1)!` and `Wᵢ ≡ −βᵢ·ℓᵖ·δᵢᵖ (mod p)`.  `lemmaA_J_ne_zero` turns the
  non-divisibility input `hnot` into `Jᵢ ≠ 0`.
* §9 (completed) — the **ambient field** `L = ⨆ₖ ℚ⟮bₖ⟯` of a finite family
  (`clearedField`, `clearedField_finiteDimensional`, `clearedField_mem`,
  `clearedElem`, `clearedElem_isIntegral`), the diagonal `δᵢᵖ ∈ L`
  (`clearedDelta`, coe, integrality) and its nonzero (`clearedDelta_ne_zero`).
* §10 (completed) — **`Wᵢ ≠ 0` for suitable primes**:
  `lemmaA_J_ne_zero_cleared` — for a cleared injective family and `βᵢ ≠ 0`
  there is `c ≠ 0` (`βᵢ·ℓ₀·N(δᵢ)`) with `Jᵢ ≠ 0` for every prime `p ∤ c`
  (field transfer + Commons `norm_isInt` / `norm_pow_not_mem_smul`).
* Remaining steps of Lemma A — **all completed in §§11–16** of this file:
  (i) the **class structure** §11 (`conjRoots`-closed pairwise-distinct
  cleared families, `conjClosedFamily`, `H̃ ∈ ℤ[y]` via
  `clearedH_mem_Z`/Commons `MonicProdConjClosed`, rational class power
  sums); (ii) the **symmetric step** §§12–13 (`Jᵢ = G(bᵢ)`, one
  `G ∈ ℚ[t]`, via `polyDivDiff` expansion + `betaPowerSum_rat`;
  `∏ᵢ Jᵢ ∈ ℚ` via `evalProd_rat`/`lemmaA_J_prod_rat`); (iii) the
  **`(p−1)!ⁿ | ∏Jᵢ` lower bound** §14/§14b (`lemmaA_J_translation`,
  `lemmaA_J_divisible_rep`, `lemmaA_J_prod_divisible`,
  `lemmaA_J_prod_quotient_int` + `nat_le_norm_int_mul`:
  `lemmaA_J_prod_lower` gives `(p−1)!ⁿ ≤ ‖∏ᵢJᵢ‖` for primes `p ∤ C`);
  (iv) the **analytic bound** §15 (`lemmaA_f_eval_norm_bound`,
  `lemmaA_P_uniform`: `‖Σₖβₖ·P(fᵢ)‖ ≤ Cᵖ`) and §16 the product upper
  bound (`lemmaA_J_prod_upper`) and the **prime selection + contradiction
  = Lemma A** (`lemmaA_orbit_contradiction`: no nonzero class-constant
  integer coefficients on a cleared conj-closed injective family satisfy
  `Σₖβₖ·e^{αₖ} = 0`).  Lemma B and its Step-3 corollaries are **completed in
  `LindemannC.lean`** (the `S_N`-symmetrization over `LindemannB`'s
  choice-function data, conjugacy closure & class constancy through the
  family field and Galois automorphisms, the lexicographic nonzero
  coefficient, the conj-closed-extension, `lemmaB`, Lindemann's theorem
  `cexp_transcendental_of_algebraic_ne_zero`, and the corollaries
  `Transcendental ℚ (log q)`, `Transcendental ℚ π`, `Irrational
  (log(1+1/m)²)` — the `m = n` corner of Theorem C).

Commons lemmas used: `trace_rat_poly`, `norm_rat_poly`, and the
`RingTheory.IsIntegral` facts (`finset_sum`, `eval_of_coeffs`,
`isInt_of_rat`).
-/

noncomputable section

open Complex Polynomial
open scoped BigOperators

namespace Submission.Transcendence

/-! ## 1.  The full product `H` and the auxiliary polynomial `fᵢ`

`α : Fin n → ℂ` is the exponent family (later: pairwise distinct algebraic
numbers closed under conjugation).  `p : ℕ` is the prime parameter,
`ℓ : ℂ` the clearing scalar.
-/

/-- `H = ∏ₖ (X − αₖ)`: the polynomial vanishing at all exponents. -/
def lemmaA_H {n : ℕ} (α : Fin n → ℂ) : ℂ[X] :=
  ∏ k : Fin n, (X - C (α k))

/-- The auxiliary polynomial of Lemma A:

`fᵢ = ℓ^{n·p}·(X−αᵢ)^{p−1}·∏_{k ≠ i} (X−αₖ)ᵖ`   (= `ℓ^{n·p}·Hᵖ/(X−αᵢ)`).
-/
def lemmaA_f {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) (i : Fin n) : ℂ[X] :=
  C (ℓ ^ (n * p)) * (X - C (α i)) ^ (p - 1) *
    ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p

/-- The product `Hᵖ` splits as `(X−αᵢ)ᵖ` times the product over the other
exponents. -/
lemma lemmaA_H_pow_factor {n : ℕ} (α : Fin n → ℂ) (p : ℕ) (i : Fin n) :
    (X - C (α i)) ^ p *
      (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p)
      = (lemmaA_H α) ^ p := by
  unfold lemmaA_H
  have hfac : (∏ k : Fin n, (X - C (α k)) ^ p) =
      (X - C (α i)) ^ p * (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p) := by
    have h := Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
      (fun k : Fin n => (X - C (α k)) ^ p) (Finset.mem_univ i)
    -- h : (∏ x ∈ univ.erase i, f x) * f i = ∏ x ∈ univ, f x
    rw [← h, mul_comm]
  rw [← Finset.prod_pow]
  exact hfac.symm

lemma lemmaA_f_mul_X_sub_C {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p) (i : Fin n) :
    (X - C (α i)) * lemmaA_f α ℓ p i = C (ℓ ^ (n * p)) * (lemmaA_H α) ^ p := by
  unfold lemmaA_f
  have hpp : (X - C (α i)) * (X - C (α i)) ^ (p - 1) = (X - C (α i)) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel]
    exact Nat.succ_le_of_lt hp
  calc
    (X - C (α i)) * (C (ℓ ^ (n * p)) * (X - C (α i)) ^ (p - 1) *
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p))
        = C (ℓ ^ (n * p)) * ((X - C (α i)) * (X - C (α i)) ^ (p - 1)) *
            (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p) := by ring
    _ = C (ℓ ^ (n * p)) * (X - C (α i)) ^ p *
            (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p) := by
            rw [hpp]
    _ = C (ℓ ^ (n * p)) * ((X - C (α i)) ^ p *
            (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p)) := by
            ring
    _ = C (ℓ ^ (n * p)) * (lemmaA_H α) ^ p := by
            rw [lemmaA_H_pow_factor]


/-! ## 2.  Vanishing and factorial shapes of `sumIDeriv (fᵢ)` at the exponents

`fᵢ` has multiplicity `p` at every exponent `αₖ` with `k ≠ i` and
multiplicity `p−1` at `αᵢ`.  Consequently (Mathlib
`Polynomial.aeval_sumIDeriv` / `aeval_sumIDeriv_of_pos`):

* at `αₖ`, `k ≠ i`: `sumIDeriv (fᵢ)` is `p!`-divisible;
* at `αᵢ`: `sumIDeriv (fᵢ) = (p−1)!·ℓ^{np}·∏_{k≠i}(αᵢ−αₖ)ᵖ + p!·(·)`.

These are the *exact, integrality-free* statements; the clearing layer of
§3/§4 turns the remainders into algebraic integers.
-/

/-- `(X − αₖ)ᵖ` divides `fᵢ` for `k ≠ i`. -/
lemma lemmaA_f_dvd_X_sub_C_pow {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) {i k : Fin n}
    (hik : k ≠ i) : (X - C (α k)) ^ p ∣ lemmaA_f α ℓ p i := by
  unfold lemmaA_f
  have hk : k ∈ (Finset.univ : Finset (Fin n)).erase i := by
    simp [hik]
  have hfac : (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α t)) ^ p) =
      (X - C (α k)) ^ p *
        (∏ t ∈ ((Finset.univ : Finset (Fin n)).erase i).erase k, (X - C (α t)) ^ p) := by
    have h := Finset.prod_erase_mul ((Finset.univ : Finset (Fin n)).erase i)
      (fun t : Fin n => (X - C (α t)) ^ p) hk
    rw [← h, mul_comm]
  refine ⟨C (ℓ ^ (n * p)) * (X - C (α i)) ^ (p - 1) *
    (∏ t ∈ ((Finset.univ : Finset (Fin n)).erase i).erase k, (X - C (α t)) ^ p), ?_⟩
  rw [hfac]
  ring

/-- `sumIDeriv (fᵢ)` at `αₖ` (`k ≠ i`) is divisible by `p!`. -/
lemma lemmaA_f_sumIDeriv_offdiag {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} {i k : Fin n}
    (hik : k ≠ i) : ∃ u : ℂ,
      (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k) = (p.factorial : ℂ) * u := by
  obtain ⟨gp, _hdeg, hgp⟩ := Polynomial.aeval_sumIDeriv (R := ℂ) (A := ℂ)
    (p := lemmaA_f α ℓ p i) p
  have hdiv : (X - C (α k)) ^ p ∣ (lemmaA_f α ℓ p i).map (algebraMap ℂ ℂ) := by
    simpa using lemmaA_f_dvd_X_sub_C_pow α ℓ p hik
  have hmain := hgp (α k) hdiv
  refine ⟨aeval (α k) gp, ?_⟩
  calc
    (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k)
        = aeval (α k) (sumIDeriv (lemmaA_f α ℓ p i)) := by simp
    _ = (p.factorial : ℂ) * aeval (α k) gp := by simpa [nsmul_eq_mul] using hmain
    _ = (p.factorial : ℂ) * aeval (α k) gp := by rfl

/-- `(X − αᵢ)^{p−1}` divides `fᵢ` (definitional shape). -/
lemma lemmaA_f_eq_X_sub_C_pow_mul {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) (i : Fin n) :
    lemmaA_f α ℓ p i = (X - C (α i)) ^ (p - 1) *
      (C (ℓ ^ (n * p)) * (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p)) := by
  unfold lemmaA_f
  ring

/-- Diagonal shape: `sumIDeriv (fᵢ)` at `αᵢ` equals
`(p−1)!·ℓ^{np}·∏_{k≠i}(αᵢ−αₖ)ᵖ` plus a `p!`-multiple. -/
lemma lemmaA_f_sumIDeriv_diag {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p) (i : Fin n) :
    ∃ u : ℂ,
      (sumIDeriv (lemmaA_f α ℓ p i)).eval (α i) =
        ((p - 1).factorial : ℂ) * ℓ ^ (n * p) *
          (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (α i - α k) ^ p) +
        (p.factorial : ℂ) * u := by
  obtain ⟨gp, _hdeg, hgp⟩ := Polynomial.aeval_sumIDeriv_of_pos (R := ℂ) (A := ℂ)
    (p := lemmaA_f α ℓ p i) (q := p) hp Function.injective_id
  let pp : ℂ[X] := C (ℓ ^ (n * p)) *
    (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p)
  have hmain := hgp (α i) (p' := pp) (by
    -- lemmaA_f α ℓ p i = (X − C(α i))^(p−1) * pp
    simp [pp, lemmaA_f_eq_X_sub_C_pow_mul])
  refine ⟨aeval (α i) gp, ?_⟩
  calc
    (sumIDeriv (lemmaA_f α ℓ p i)).eval (α i)
        = aeval (α i) (sumIDeriv (lemmaA_f α ℓ p i)) := by simp
    _ = ((p - 1).factorial : ℂ) • pp.eval (α i) + (p.factorial : ℂ) • aeval (α i) gp := by
            simpa [nsmul_eq_mul] using hmain
    _ = ((p - 1).factorial : ℂ) * ℓ ^ (n * p) *
          (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (α i - α k) ^ p) +
        (p.factorial : ℂ) * aeval (α i) gp := by
            simp [pp]
            rw [Polynomial.eval_prod]
            simp [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
            ring


/-! ## 3.  The divided-difference quotient `(P − P(a))/(X − a)`

For a polynomial `P` and a point `a`, `(X − a) ∣ P − C(P.eval a)` with an
*explicit* quotient whose coefficients are polynomials in `a`:

`P(x) − P(a) = (x − a)·Σₘ (Σₙ Pₙ·a^{n−1−m})·xᵐ`.

This is the algebraic heart of the symmetric step of Lemma A: with
`P = ℓ^{np}·Hᵖ ∈ ℚ[x]` (vanishing at every `αᵢ`), each `fᵢ` is the quotient
`polyDivDiff P (αᵢ)`, and its `xᵐ`-coefficient is a polynomial (independent of
`i`) evaluated at `αᵢ`.
-/

/-- The explicit divided-difference quotient:

`polyDivDiff P a = Σₙ Pₙ·Σ_{i<n} Xⁱ·a^{n−1−i}`,  so that
`(X − a)·polyDivDiff P a = P − P(a)`.
-/
def polyDivDiff {R : Type*} [CommRing R] (P : R[X]) (a : R) : R[X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    C (P.coeff n) * (∑ i ∈ Finset.range n, X ^ i * C (a ^ (n - 1 - i)))

/-- Basic identity: `(X − a)·polyDivDiff P a = P − P(a)`. -/
lemma polyDivDiff_mul {R : Type*} [CommRing R] (P : R[X]) (a : R) :
    (X - C a) * polyDivDiff P a = P - C (P.eval a) := by
  have hP : P = ∑ n ∈ Finset.range (P.natDegree + 1), C (P.coeff n) * X ^ n :=
    P.as_sum_range_C_mul_X_pow
  have hEv : P.eval a = ∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * a ^ n := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self P.natDegree) a]
  calc
    (X - C a) * polyDivDiff P a
        = ∑ n ∈ Finset.range (P.natDegree + 1),
            (X - C a) * (C (P.coeff n) * (∑ i ∈ Finset.range n, X ^ i * C (a ^ (n - 1 - i)))) := by
            simp [polyDivDiff, Finset.mul_sum]
    _ = ∑ n ∈ Finset.range (P.natDegree + 1),
            C (P.coeff n) * ((X - C a) * ∑ i ∈ Finset.range n, X ^ i * C (a ^ (n - 1 - i))) := by
            apply Finset.sum_congr rfl
            intro n hn
            ring
    _ = ∑ n ∈ Finset.range (P.natDegree + 1),
            C (P.coeff n) * (X ^ n - C (a ^ n)) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Commons.Algebra.Polynomial.X_pow_sub_C_pow_eq_mul_sum a n]
    _ = ∑ n ∈ Finset.range (P.natDegree + 1),
            (C (P.coeff n) * X ^ n - C (P.coeff n * a ^ n)) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [mul_sub, ← C_mul]
    _ = ∑ n ∈ Finset.range (P.natDegree + 1), C (P.coeff n) * X ^ n -
            ∑ n ∈ Finset.range (P.natDegree + 1), C (P.coeff n * a ^ n) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ n ∈ Finset.range (P.natDegree + 1), C (P.coeff n) * X ^ n) -
            C (∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * a ^ n) := by
            rw [← map_sum (C : R →+* R[X]) (fun n : ℕ => P.coeff n * a ^ n)
              (Finset.range (P.natDegree + 1))]
    _ = P - C (P.eval a) := by
            rw [← hP]
            rw [← hEv]

/-- When `P(a) = 0`, `P = (X − a)·polyDivDiff P a`. -/
lemma polyDivDiff_eq_of_root {R : Type*} [CommRing R] (P : R[X]) (a : R) (hPa : P.eval a = 0) :
    P = (X - C a) * polyDivDiff P a := by
  rw [polyDivDiff_mul]
  simp [hPa]


/-- `H` vanishes at every exponent. -/
lemma lemmaA_H_eval (n : ℕ) (α : Fin n → ℂ) (i : Fin n) : (lemmaA_H α).eval (α i) = 0 := by
  unfold lemmaA_H
  have hfac : (∏ k : Fin n, (X - C (α k))) =
      (X - C (α i)) * (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k))) := by
    have h := Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
      (fun k : Fin n => X - C (α k)) (Finset.mem_univ i)
    rw [← h, mul_comm]
  rw [hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  simp

/-- The auxiliary polynomial is the divided-difference quotient of
`P := ℓ^{np}·Hᵖ` at `αᵢ` (with which it shares the factor identity). -/
lemma lemmaA_f_eq_polyDivDiff {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p) (i : Fin n) :
    lemmaA_f α ℓ p i = polyDivDiff (C (ℓ ^ (n * p)) * (lemmaA_H α) ^ p) (α i) := by
  let P : ℂ[X] := C (ℓ ^ (n * p)) * (lemmaA_H α) ^ p
  have hP0 : P.eval (α i) = 0 := by
    dsimp [P]
    rw [Polynomial.eval_mul, Polynomial.eval_pow, lemmaA_H_eval n α i]
    simp [hp.ne']
  have h1 : P = (X - C (α i)) * polyDivDiff P (α i) := polyDivDiff_eq_of_root P (α i) hP0
  have h2 : (X - C (α i)) * lemmaA_f α ℓ p i = P := by
    dsimp [P]
    exact lemmaA_f_mul_X_sub_C α ℓ hp i
  have hXnz : X - C (α i) ≠ 0 := Polynomial.X_sub_C_ne_zero (α i)
  apply mul_left_cancel₀ hXnz
  rw [h2, h1]



/-! ## 4.  Algebraic-integer coefficients: the clearing layer begins

We record the fact (used throughout Lemma A's arithmetic) that the *scaled*
polynomials — the ones whose roots are the cleared exponents `bₖ = ℓαₖ`,
with coefficients `1`, `ℓ ∈ ℤ`, and `−bₖ` all integral over `ℤ` — have
integral coefficients, and that evaluating their iterated derivatives at the
(integral) points `bₖ` gives algebraic integers (Commons `eval_of_coeffs`,
`finset_sum`).  The multiplicity structure then yields the
`p!` / `(p−1)!` factorial shapes exactly in the ring of algebraic integers.
-/

/-- A polynomial over `A` all of whose coefficients are algebraic integers. -/
def PolyInt {A : Type*} [CommRing A] [Algebra ℤ A] (p : A[X]) : Prop :=
  ∀ n : ℕ, IsIntegral ℤ (p.coeff n)

namespace PolyInt

variable {A : Type*} [CommRing A] [Algebra ℤ A]

/-- Polynomials with integral coefficients are closed under multiplication. -/
lemma mul {p q : A[X]} (hp : PolyInt p) (hq : PolyInt q) : PolyInt (p * q) := by
  intro n
  rw [Polynomial.coeff_mul]
  exact Commons.RingTheory.IsIntegral.finset_sum (Finset.HasAntidiagonal.antidiagonal n)
    (fun x : ℕ × ℕ => p.coeff x.1 * q.coeff x.2) (by
      intro x hx
      exact IsIntegral.mul (hp x.1) (hq x.2))

/-- Polynomials with integral coefficients are closed under addition. -/
lemma add {p q : A[X]} (hp : PolyInt p) (hq : PolyInt q) : PolyInt (p + q) := by
  intro n
  rw [Polynomial.coeff_add]
  exact IsIntegral.add (hp n) (hq n)

/-- Polynomials with integral coefficients are closed under negation. -/
lemma neg {p : A[X]} (hp : PolyInt p) : PolyInt (-p) := by
  intro n
  rw [Polynomial.coeff_neg]
  exact IsIntegral.neg (hp n)

/-- Polynomials with integral coefficients are closed under subtraction. -/
lemma sub {p q : A[X]} (hp : PolyInt p) (hq : PolyInt q) : PolyInt (p - q) := by
  intro n
  rw [Polynomial.coeff_sub]
  exact IsIntegral.sub (hp n) (hq n)

/-- Powers of integral-coefficient polynomials have integral coefficients. -/
lemma pow {p : A[X]} (hp : PolyInt p) (m : ℕ) : PolyInt (p ^ m) := by
  induction m with
  | zero =>
      intro n
      rw [pow_zero, Polynomial.coeff_one]
      split_ifs with hn
      · exact isIntegral_one
      · exact isIntegral_zero
  | succ m ih =>
      rw [pow_succ]
      exact PolyInt.mul ih hp

/-- The constant polynomial of an integral element has integral coefficients. -/
lemma C_of_isIntegral {a : A} (ha : IsIntegral ℤ a) : PolyInt (C a) := by
  intro n
  rw [Polynomial.coeff_C]
  split_ifs with hn
  · simpa [hn] using ha
  · exact isIntegral_zero

/-- `X` has integral coefficients. -/
lemma X_poly : PolyInt (X : A[X]) := by
  intro n
  rw [Polynomial.coeff_X]
  split_ifs with hn
  · exact isIntegral_one
  · exact isIntegral_zero

/-- Subtracting a constant polynomial from `X`. -/
lemma X_sub_C {a : A} (ha : IsIntegral ℤ a) : PolyInt ((X : A[X]) - C a) := by
  exact PolyInt.sub PolyInt.X_poly (C_of_isIntegral ha)

/-- Iterated derivatives of integral-coefficient polynomials have integral
coefficients. -/
lemma iterate_derivative {p : A[X]} (hp : PolyInt p) (m : ℕ) : PolyInt ((derivative^[m]) p) := by
  have hder : ∀ {q : A[X]}, PolyInt q → PolyInt (derivative q) := by
    intro q hq n
    rw [Polynomial.coeff_derivative]
    exact IsIntegral.mul (hq (n + 1)) (by
      simpa [nsmul_eq_mul] using (IsIntegral.nsmul (isIntegral_one : IsIntegral ℤ (1 : A)) (n + 1)))
  induction m generalizing p with
  | zero => simpa using hp
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      exact ih (hder hp)

lemma one : PolyInt (1 : A[X]) := by
  intro n
  rw [Polynomial.coeff_one]
  split_ifs with hn
  · exact isIntegral_one
  · exact isIntegral_zero

/-- Products (over a finite index set) of integral-coefficient polynomials
have integral coefficients. -/
lemma prod_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A[X])
    (h : ∀ k ∈ s, PolyInt (f k)) : PolyInt (∏ k ∈ s, f k) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
      exact (one : PolyInt (1 : A[X]))
  | insert a s' has' ih =>
      rw [Finset.prod_insert has']
      exact PolyInt.mul (h a (Finset.mem_insert_self a s'))
        (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

end PolyInt


/-! ## 5.  The scaled (cleared) auxiliary polynomials and their values at roots

With the exponents cleared to algebraic integers `bₖ = ℓαₖ`, the auxiliary
polynomial of Lemma A becomes (up to the `x = y/ℓ` change of variable)

`f̃ᵢ(y) = ℓ·(y − bᵢ)^{p−1}·∏_{t ≠ i} (y − bₜ)ᵖ`.

Its iterated derivatives at the integral points `bₖ` have the exact value
formulas (`deriv_mul_pow_eval_root`) that encode the multiplicity structure:
at `bₖ`, `k ≠ i`, all derivatives of order `< p` vanish and higher ones are
`p!`-divisible in the ring of algebraic integers; at `bᵢ` the order-`p−1`
derivative is the nonzero diagonal `(p−1)!·ℓ·δᵢᵖ`, `δᵢ = ∏_{t≠i}(bᵢ−bₜ)`.
-/

/-- Value of an iterated derivative of a power of a linear factor at its
root: `(X−a)ᵠ` differentiated `j` times and evaluated at `a` equals `q!`
when `j = q` and `0` otherwise. -/
lemma deriv_X_sub_C_pow_root (q j : ℕ) (a : ℂ) :
    ((derivative^[j]) ((X - C a) ^ q)).eval a = if j = q then (q.factorial : ℂ) else 0 := by
  rw [Polynomial.iterate_derivative_X_sub_pow q j a]
  rw [eval_smul, eval_pow, eval_sub, eval_X, eval_C]
  by_cases h : j = q
  · subst j
    rw [Nat.descFactorial_self]
    simp
  · rw [if_neg h]
    by_cases hlt : j < q
    · have hqj : q - j ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)
      have hz : (a - a) ^ (q - j) = 0 := by
        rw [sub_self, zero_pow hqj]
      rw [hz, smul_zero]
    · have hqle : q ≤ j := Nat.le_of_not_gt hlt
      have hne : q ≠ j := by intro hj; exact h hj.symm
      have hgt : q < j := lt_of_le_of_ne hqle hne
      have hd : q.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hgt
      simp [hd]

/-- Leibniz expansion of the `j`-th derivative of `(X−a)ᵠ·w` evaluated at `a`. -/
lemma deriv_mul_pow_eval (q j : ℕ) (a : ℂ) (w : ℂ[X]) :
    ((derivative^[j]) ((X - C a) ^ q * w)).eval a =
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℂ) *
        (((derivative^[j - k]) ((X - C a) ^ q)).eval a) * (((derivative^[k]) w).eval a) := by
  rw [Polynomial.iterate_derivative_mul]
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [eval_smul, eval_mul]
  ring_nf

/-- Closed form of the value at `a`: only the term differentiating the
`(X−a)ᵠ`-factor exactly `q` times survives. -/
lemma deriv_mul_pow_eval_root (q j : ℕ) (a : ℂ) (w : ℂ[X]) :
    ((derivative^[j]) ((X - C a) ^ q * w)).eval a =
      if q ≤ j then (j.choose (j - q) : ℂ) * (q.factorial : ℂ) * (((derivative^[j - q]) w).eval a)
      else 0 := by
  rw [deriv_mul_pow_eval]
  by_cases hqj : q ≤ j
  · rw [Finset.sum_eq_single (j - q)]
    · rw [if_pos hqj]
      rw [deriv_X_sub_C_pow_root]
      have hsub : j - (j - q) = q := Nat.sub_sub_self hqj
      rw [hsub, if_pos rfl]
    · intro k hk hneq
      rw [deriv_X_sub_C_pow_root]
      have h : j - k ≠ q := by
        intro hjk
        apply hneq
        have hkl : k ≤ j := by
          rw [Finset.mem_range] at hk
          omega
        omega
      rw [if_neg h]
      ring
    · intro hknot
      have : j - q ∈ Finset.range (j + 1) := by
        rw [Finset.mem_range]
        omega
      exact False.elim (hknot this)
  · have hgt : j < q := Nat.lt_of_not_ge hqj
    rw [if_neg hqj]
    apply Finset.sum_eq_zero
    intro k hk
    rw [deriv_X_sub_C_pow_root]
    have hjkq : j - k ≠ q := by
      intro hjq
      have : j - k ≤ j := Nat.sub_le _ _
      omega
    rw [if_neg hjkq]
    ring

/-- The "off-diagonal" factor product `Qᵢ(y) = ∏_{t≠i} (y − bₜ)ᵖ`. -/
def scaledQ {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n) : ℂ[X] :=
  ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (b k)) ^ p

/-- The scaled auxiliary polynomial `f̃ᵢ(y) = ℓ·(y−bᵢ)^{p−1}·∏_{t≠i}(y−bₜ)ᵖ`. -/
def scaledF {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) (i : Fin n) : ℂ[X] :=
  C ℓ * (X - C (b i)) ^ (p - 1) * scaledQ b p i

/-- The factor of `scaledF` complementary to `(X − bₖ)ᵖ` for `k ≠ i`. -/
def scaledR {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) (i k : Fin n) : ℂ[X] :=
  C ℓ * (X - C (b i)) ^ (p - 1) *
    (∏ t ∈ ((Finset.univ : Finset (Fin n)).erase i).erase k, (X - C (b t)) ^ p)

/-- Off-diagonal factor decomposition of the scaled polynomial:
`f̃ᵢ = (X − bₖ)ᵖ·R` for `k ≠ i`. -/
lemma scaledF_eq_pow_mul {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) {i k : Fin n}
    (hik : k ≠ i) : scaledF b ℓ p i = (X - C (b k)) ^ p * scaledR b ℓ p i k := by
  unfold scaledF scaledQ scaledR
  have hk : k ∈ (Finset.univ : Finset (Fin n)).erase i := by
    simp [hik]
  have hfac : (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (b t)) ^ p) =
      (X - C (b k)) ^ p *
        (∏ t ∈ ((Finset.univ : Finset (Fin n)).erase i).erase k, (X - C (b t)) ^ p) := by
    have h := Finset.prod_erase_mul ((Finset.univ : Finset (Fin n)).erase i)
      (fun t : Fin n => (X - C (b t)) ^ p) hk
    rw [← h, mul_comm]
  rw [hfac]
  ring

/-- Diagonal factor decomposition of the scaled polynomial:
`f̃ᵢ = (X − bᵢ)^{p−1}·(ℓ·Qᵢ)`. -/
lemma scaledF_eq_pow_pred_mul {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) (i : Fin n) :
    scaledF b ℓ p i = (X - C (b i)) ^ (p - 1) * (C ℓ * scaledQ b p i) := by
  unfold scaledF
  ring



/-- `Qᵢ` has algebraic-integer coefficients when every `bₖ` is an algebraic
integer. -/
lemma PolyInt_scaledQ {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) : PolyInt (scaledQ b p i) := by
  unfold scaledQ
  exact PolyInt.prod_finset ((Finset.univ : Finset (Fin n)).erase i)
    (fun k => (X - C (b k)) ^ p) (by
      intro k hk
      exact PolyInt.pow (PolyInt.X_sub_C (hb k)) p)

/-- `f̃ᵢ` has algebraic-integer coefficients when every `bₖ` and `ℓ` are
algebraic integers. -/
lemma PolyInt_scaledF {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) (i : Fin n)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) (hℓ : IsIntegral ℤ ℓ) : PolyInt (scaledF b ℓ p i) := by
  unfold scaledF
  exact PolyInt.mul (PolyInt.mul (PolyInt.C_of_isIntegral hℓ)
    (PolyInt.pow (PolyInt.X_sub_C (hb i)) (p - 1))) (PolyInt_scaledQ b p i hb)

/-- The complementary factor `R` of `f̃ᵢ` at `bₖ` (`k ≠ i`) has algebraic
integer coefficients. -/
lemma PolyInt_scaledR {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) (i k : Fin n)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) (hℓ : IsIntegral ℤ ℓ) :
    PolyInt (scaledR b ℓ p i k) := by
  unfold scaledR
  exact PolyInt.mul (PolyInt.mul (PolyInt.C_of_isIntegral hℓ)
    (PolyInt.pow (PolyInt.X_sub_C (hb i)) (p - 1))) (by
      apply PolyInt.prod_finset
      intro t ht
      exact PolyInt.pow (PolyInt.X_sub_C (hb t)) p)

/-- A value of an integral-coefficient polynomial at an algebraic-integer
point is an algebraic integer. -/
lemma eval_PolyInt_isIntegral (p : ℂ[X]) (hp : PolyInt p) {x : ℂ} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (p.eval x) := by
  exact Commons.RingTheory.IsIntegral.eval_of_coeffs p hp hx

/-- A natural number, seen as a complex number, is an algebraic integer. -/
lemma isIntegral_natCast_complex (n : ℕ) : IsIntegral ℤ (n : ℂ) := by
  simpa [nsmul_eq_mul] using (IsIntegral.nsmul (isIntegral_one : IsIntegral ℤ (1 : ℂ)) n)

/-- Exact value of the `j`-th derivative of `f̃ᵢ` at `bₖ` (`k ≠ i`): all
derivatives of order `< p` vanish, and the higher ones are described by
`deriv_mul_pow_eval_root`. -/
lemma scaledF_deriv_offdiag {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) {i k : Fin n}
    (hik : k ≠ i) (j : ℕ) :
    ((derivative^[j]) (scaledF b ℓ p i)).eval (b k) =
      if p ≤ j then (j.choose (j - p) : ℂ) * (p.factorial : ℂ) *
        (((derivative^[j - p]) (scaledR b ℓ p i k)).eval (b k))
      else 0 := by
  rw [scaledF_eq_pow_mul (b := b) (ℓ := ℓ) (p := p) (hik := hik)]
  exact deriv_mul_pow_eval_root p j (b k) (scaledR b ℓ p i k)

/-- Vanishing at `bₖ` (`k ≠ i`) of derivatives of order `< p`. -/
lemma scaledF_deriv_offdiag_lt {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} {i k : Fin n}
    (hik : k ≠ i) {j : ℕ} (hj : j < p) :
    ((derivative^[j]) (scaledF b ℓ p i)).eval (b k) = 0 := by
  rw [scaledF_deriv_offdiag b ℓ p hik j]
  have hnp : ¬ p ≤ j := Nat.not_le_of_gt hj
  rw [if_neg hnp]

/-- For `j ≥ p`, the `j`-th derivative of `f̃ᵢ` at `bₖ` (`k ≠ i`) is
`p!`-divisible in the ring of algebraic integers. -/
lemma scaledF_deriv_offdiag_ge {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) {i k : Fin n}
    (hik : k ≠ i) (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) (hℓ : IsIntegral ℤ ℓ)
    {j : ℕ} (hj : p ≤ j) :
    ∃ u : ℂ, IsIntegral ℤ u ∧
      ((derivative^[j]) (scaledF b ℓ p i)).eval (b k) = (p.factorial : ℂ) * u := by
  rw [scaledF_deriv_offdiag b ℓ p hik j, if_pos hj]
  refine ⟨(j.choose (j - p) : ℂ) * (((derivative^[j - p]) (scaledR b ℓ p i k)).eval (b k)), ?_, ?_⟩
  · -- u is an algebraic integer
    exact IsIntegral.mul (isIntegral_natCast_complex (j.choose (j - p)))
      (eval_PolyInt_isIntegral ((derivative^[j - p]) (scaledR b ℓ p i k))
        (PolyInt.iterate_derivative (PolyInt_scaledR b ℓ p i k hb hℓ) (j - p)) (hb k))
  · -- value = p!·u
    ring

/-- Exact diagonal value: the `(p−1)`-st derivative of `f̃ᵢ` at `bᵢ` is
`(p−1)!·ℓ·∏_{t≠i}(bᵢ−bₜ)ᵖ`. -/
lemma scaledF_deriv_diag {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p) (i : Fin n) :
    ((derivative^[p - 1]) (scaledF b ℓ p i)).eval (b i) =
      ((p - 1).factorial : ℂ) * ℓ * (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (b i - b k) ^ p) := by
  rw [scaledF_eq_pow_pred_mul]
  rw [deriv_mul_pow_eval_root (p - 1) (p - 1) (b i) (C ℓ * scaledQ b p i)]
  have hqj : p - 1 ≤ p - 1 := le_rfl
  rw [if_pos hqj]
  have hsub : (p - 1) - (p - 1) = 0 := by omega
  rw [hsub]
  have hc : ((p - 1).choose 0 : ℂ) = 1 := by simp
  rw [hc]
  have hw : ((derivative^[0]) (C ℓ * scaledQ b p i)).eval (b i) = ℓ * (scaledQ b p i).eval (b i) := by
    simp
  rw [hw]
  -- (Cℓ·Q).eval(bᵢ) computed: ℓ·Q(bᵢ); Q(bᵢ) = ∏ (bᵢ − bₜ)^p
  have hQ : (scaledQ b p i).eval (b i) = ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (b i - b k) ^ p := by
    unfold scaledQ
    rw [Polynomial.eval_prod]
    simp [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  calc
    1 * ((p - 1).factorial : ℂ) * (ℓ * (scaledQ b p i).eval (b i))
        = ((p - 1).factorial : ℂ) * ℓ * (scaledQ b p i).eval (b i) := by ring
    _ = ((p - 1).factorial : ℂ) * ℓ * (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (b i - b k) ^ p) := by
            rw [hQ]

/-- At `bᵢ`, derivatives of order `< p−1` of `f̃ᵢ` vanish. -/
lemma scaledF_deriv_diag_lt {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (i : Fin n)
    {j : ℕ} (hj : j < p - 1) :
    ((derivative^[j]) (scaledF b ℓ p i)).eval (b i) = 0 := by
  rw [scaledF_eq_pow_pred_mul]
  rw [deriv_mul_pow_eval_root (p - 1) j (b i) (C ℓ * scaledQ b p i)]
  have hnp : ¬ p - 1 ≤ j := Nat.not_le_of_gt hj
  rw [if_neg hnp]



/-! ## 6.  Clearing denominators of a finite algebraic exponent family

One fixed positive integer `ℓ` makes every exponent an algebraic integer:
for each `k`, `Algebra.natDenominator (α k)` works, and the product over the
whole family clears everything at once.
-/

/-- For a finite family of algebraic numbers, one positive integer `ℓ`
clears all of them to algebraic integers. -/
lemma exists_clearing_fin {n : ℕ} (α : Fin n → ℂ) (hα : ∀ k : Fin n, IsAlgebraic ℚ (α k)) :
    ∃ ℓ : ℕ, ℓ ≠ 0 ∧ ∀ k : Fin n, IsIntegral ℤ (ℓ • α k) := by
  classical
  let ds : Fin n → ℕ := fun k => Algebra.natDenominator (α k)
  let ℓ : ℕ := ∏ k : Fin n, ds k
  have hd0 : ∀ k : Fin n, ds k ≠ 0 := by
    intro k
    have hz : IsAlgebraic ℤ (α k) :=
      (IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := ℂ)).mpr (hα k)
    exact IsAlgebraic.natDenominator_ne_zero hz
  refine ⟨ℓ, ?_, ?_⟩
  · -- ℓ ≠ 0 (a finite product of nonzero naturals is nonzero)
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact hd0 k
  · intro k
    -- ℓ • α k = (∏_{t ≠ k} d_t) • (d_k • α k), both sides of the product
    have hdk : IsIntegral ℤ (ds k • α k) := Algebra.isIntegral_natDenominator_smul (α k)
    have hfac : ℓ = ds k * (∏ t ∈ (Finset.univ : Finset (Fin n)).erase k, ds t) := by
      have h := Finset.prod_erase_mul (Finset.univ : Finset (Fin n)) ds (Finset.mem_univ k)
      -- h : (∏ t ∈ univ.erase k, ds t) * ds k = ∏ t ∈ univ, ds t
      dsimp [ℓ]
      rw [← h, mul_comm]
    -- (ds k • α k) is integral; scaling further by the product over the rest is integral
    have hℓeq : ℓ • α k =
        (∏ t ∈ (Finset.univ : Finset (Fin n)).erase k, ds t) • (ds k • α k) := by
      rw [hfac]
      simp [nsmul_eq_mul, Nat.cast_mul, Nat.cast_prod, mul_assoc, mul_comm]
    rw [hℓeq]
    exact IsIntegral.nsmul hdk (∏ t ∈ (Finset.univ : Finset (Fin n)).erase k, ds t)


/-! ## 7.  The `x ↔ y` translation and the arithmetic of `sumIDeriv (fᵢ)` at the exponents

**Status.**  This section completes the *clearing-layer arithmetic* of Lemma A:
for exponents `α : Fin n → ℂ` cleared by a scalar `ℓ` (so `bₖ = ℓ·αₖ` are
algebraic integers — for a *natural* `ℓ` this is `exists_clearing_fin`), the
auxiliary polynomial `fᵢ` of §1 is the composition `f̃ᵢ∘(ℓX)` of the scaled
polynomial `f̃ᵢ` of §5 (`lemmaA_f_eq_scaledF_comp`), and iterated derivatives
obey the chain rule `(f̃ᵢ∘(ℓX))⁽ʲ⁾ = ℓʲ·f̃ᵢ⁽ʲ⁾∘(ℓX)`
(`iterate_derivative_comp_C_mul_X`, `deriv_lemmaA_f_eval`).  Combined with
the exact scaled root-value formulas of §5 and the new *diagonal*
`p`-divisibility for orders `≥ p` at `bᵢ` (`scaledQ_deriv`,
`scaledQ_deriv_eval_diag_p`, `scaledF_deriv_diag_ge` — the heart of this
section: `derivative (∏_t (X−bₜ)ᵖ) = p·Σₜ (X−bₜ)^(p−1)·∏_{u≠t}(X−b_u)ᵖ`,
so every higher derivative carries a factor `p`), we obtain the two
**`sumIDeriv`-level arithmetic facts of Lemma A with algebraic-integer
remainders**:

* off-diagonal (`k ≠ i`): `F(αₖ) = p!·u` with `u` an algebraic integer
  (`lemmaA_f_sumIDeriv_offdiag_int`; `F = sumIDeriv fᵢ`), and
* diagonal (`k = i`):
  `F(αᵢ) = (p−1)!·ℓᵖ·∏_{t≠i}(ℓαᵢ−ℓαₜ)ᵖ + p!·u`, `u` an algebraic integer
  (`lemmaA_f_sumIDeriv_diag_int`; exact diagonal, `p!`-remainder).

These are exactly the statements the class-step (§§8–9 of the roadmap) feeds
into `Jᵢ = Σₖ βₖ·F(αₖ)` to conclude that `Jᵢ` is a nonzero algebraic integer
divisible by `(p−1)!`.
-/
/-! ################################################################
NEW CONTENT (§5b translation + diagonal divisibility + sumIDeriv shapes)
################################################################ -/

lemma C_mul_X_sub_C_mul (ℓ a : ℂ) : C ℓ * X - C (ℓ * a) = C ℓ * (X - C a) := by
  rw [C_mul, ← mul_sub]

lemma C_mul_X_sub_C_pow (ℓ a : ℂ) (q : ℕ) : (C ℓ * (X - C a)) ^ q = C (ℓ ^ q) * (X - C a) ^ q := by
  rw [mul_pow, C_pow]

lemma scaledF_comp_eq {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) (i : Fin n) :
    (scaledF b ℓ p i).comp (C ℓ * X) =
      C ℓ * (C ℓ * X - C (b i)) ^ (p - 1) *
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (C ℓ * X - C (b k)) ^ p) := by
  unfold scaledF scaledQ
  rw [mul_comp, mul_comp, C_comp, pow_comp, sub_comp, X_comp, C_comp]
  rw [Polynomial.prod_comp]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [pow_comp, sub_comp, X_comp, C_comp]

lemma scaledF_comp_eq_alpha {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) (i : Fin n) :
    (scaledF (fun k : Fin n => ℓ * α k) ℓ p i).comp (C ℓ * X) =
      C ℓ * (C ℓ * (X - C (α i))) ^ (p - 1) *
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (C ℓ * (X - C (α k))) ^ p) := by
  rw [scaledF_comp_eq]
  congr 1
  · rw [C_mul_X_sub_C_mul]
  · apply Finset.prod_congr rfl
    intro k hk
    rw [C_mul_X_sub_C_mul]

lemma scalar_pow_comb (ℓ : ℂ) {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    ℓ * ℓ ^ (p - 1) * (ℓ ^ p) ^ (n - 1) = ℓ ^ (n * p) := by
  have h1 : ℓ * ℓ ^ (p - 1) = ℓ ^ p := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h1]
  have h2 : ℓ ^ p * (ℓ ^ p) ^ (n - 1) = (ℓ ^ p) ^ n := by
    rw [← pow_succ' (ℓ ^ p) (n - 1)]
    congr 1
    exact Nat.sub_add_cancel hn
  rw [h2]
  rw [← pow_mul]
  congr 1
  rw [mul_comm p n]

lemma C_scalar_pow_comb (ℓ : ℂ) {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    C ℓ * C (ℓ ^ (p - 1)) * (C (ℓ ^ p)) ^ (n - 1) = C (ℓ ^ (n * p)) := by
  rw [← C_pow]
  rw [← C_mul]
  rw [← C_mul]
  congr 1
  exact scalar_pow_comb ℓ hp hn

lemma iterate_derivative_comp_C_mul_X (q : ℂ[X]) (ℓ : ℂ) (j : ℕ) :
    (derivative^[j]) (q.comp (C ℓ * X)) = C (ℓ ^ j) * ((derivative^[j]) q).comp (C ℓ * X) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hiter : derivative ((derivative^[j]) q) = (derivative^[j + 1]) q := by
        rw [← Function.iterate_succ_apply' (f := (derivative : ℂ[X] → ℂ[X]))]
      calc
        (derivative^[j + 1]) (q.comp (C ℓ * X))
            = derivative ((derivative^[j]) (q.comp (C ℓ * X))) := by
                rw [Function.iterate_succ_apply']
        _ = derivative (C (ℓ ^ j) * (((derivative^[j]) q).comp (C ℓ * X))) := by rw [ih]
        _ = C (ℓ ^ j) * derivative (((derivative^[j]) q).comp (C ℓ * X)) := by
              rw [derivative_mul, derivative_C]
              ring
        _ = C (ℓ ^ j) * (C ℓ * ((derivative ((derivative^[j]) q)).comp (C ℓ * X))) := by
              rw [derivative_comp]
              have hd : derivative (C ℓ * X) = C ℓ := by
                rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X]
                simp
              rw [hd]
        _ = C (ℓ ^ (j + 1)) * (((derivative^[j + 1]) q).comp (C ℓ * X)) := by
              rw [hiter]
              rw [← mul_assoc, ← C_mul, pow_succ]

lemma lemmaA_f_eq_scaledF_comp {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p) (i : Fin n) :
    lemmaA_f α ℓ p i = (scaledF (fun k : Fin n => ℓ * α k) ℓ p i).comp (C ℓ * X) := by
  classical
  let e : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase i
  have hn : 0 < n := by
    have : (i : ℕ) < n := i.isLt
    omega
  have hcard : e.card = n - 1 := by
    dsimp [e]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    simp
  have hR : (scaledF (fun k : Fin n => ℓ * α k) ℓ p i).comp (C ℓ * X) =
      (C ℓ * C (ℓ ^ (p - 1)) * (C (ℓ ^ p)) ^ (n - 1)) *
        ((X - C (α i)) ^ (p - 1) * (∏ k ∈ e, (X - C (α k)) ^ p)) := by
    rw [scaledF_comp_eq_alpha]
    rw [C_mul_X_sub_C_pow]
    have hpe : (∏ k ∈ e, (C ℓ * (X - C (α k))) ^ p) =
        (C (ℓ ^ p)) ^ (n - 1) * (∏ k ∈ e, (X - C (α k)) ^ p) := by
      have hf : (∏ k ∈ e, (C ℓ * (X - C (α k))) ^ p) =
          ∏ k ∈ e, (C (ℓ ^ p) * (X - C (α k)) ^ p) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [C_mul_X_sub_C_pow]
      rw [hf]
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_const, hcard]
    rw [hpe]
    ac_rfl
  calc
    lemmaA_f α ℓ p i
        = C (ℓ ^ (n * p)) * (X - C (α i)) ^ (p - 1) * (∏ k ∈ e, (X - C (α k)) ^ p) := by
            unfold lemmaA_f
            rfl
    _ = (C ℓ * C (ℓ ^ (p - 1)) * (C (ℓ ^ p)) ^ (n - 1)) *
          ((X - C (α i)) ^ (p - 1) * (∏ k ∈ e, (X - C (α k)) ^ p)) := by
          rw [C_scalar_pow_comb ℓ hp hn]
          ac_rfl
    _ = (scaledF (fun k : Fin n => ℓ * α k) ℓ p i).comp (C ℓ * X) := hR.symm

/-- `Qᵢ' = Σₜ (∏_{u≠t,i} (X−b_u)^p)·(X−bₜ)^(p−1)`, with `derivative Qᵢ = p·Qᵢ'`. -/
def scaledQderiv {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n) : ℂ[X] :=
  ∑ t ∈ (Finset.univ : Finset (Fin n)).erase i,
    (∏ u ∈ ((Finset.univ : Finset (Fin n)).erase i).erase t, (X - C (b u)) ^ p) *
      (X - C (b t)) ^ (p - 1)

lemma scaledQ_deriv {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n) :
    derivative (scaledQ b p i) = C (p : ℂ) * scaledQderiv b p i := by
  unfold scaledQ scaledQderiv
  calc
    derivative (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (b k)) ^ p)
        = ∑ a ∈ (Finset.univ : Finset (Fin n)).erase i,
            (∏ u ∈ ((Finset.univ : Finset (Fin n)).erase i).erase a, (X - C (b u)) ^ p) *
              derivative ((X - C (b a)) ^ p) := by
            rw [Polynomial.derivative_prod_finset]
    _ = ∑ a ∈ (Finset.univ : Finset (Fin n)).erase i,
            (∏ u ∈ ((Finset.univ : Finset (Fin n)).erase i).erase a, (X - C (b u)) ^ p) *
              (C (p : ℂ) * (X - C (b a)) ^ (p - 1)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Polynomial.derivative_X_sub_C_pow]
    _ = C (p : ℂ) * (∑ a ∈ (Finset.univ : Finset (Fin n)).erase i,
            (∏ u ∈ ((Finset.univ : Finset (Fin n)).erase i).erase a, (X - C (b u)) ^ p) *
              (X - C (b a)) ^ (p - 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a ha
            ring

lemma derivative_C_mul (a : ℂ) (q : ℂ[X]) : derivative (C a * q) = C a * derivative q := by
  rw [derivative_mul, derivative_C]
  ring

namespace PolyInt

variable {A : Type*} [CommRing A] [Algebra ℤ A]

lemma sum_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A[X])
    (h : ∀ k ∈ s, PolyInt (f k)) : PolyInt (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro n
      simpa using (isIntegral_zero : IsIntegral ℤ (0 : A))
  | insert a s' has' ih =>
      rw [Finset.sum_insert has']
      exact PolyInt.add (h a (Finset.mem_insert_self a s')) (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

end PolyInt

lemma PolyInt_scaledQderiv {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) : PolyInt (scaledQderiv b p i) := by
  unfold scaledQderiv
  refine PolyInt.sum_finset ((Finset.univ : Finset (Fin n)).erase i)
    (fun t => (∏ u ∈ (((Finset.univ : Finset (Fin n)).erase i).erase t), (X - C (b u)) ^ p) *
      (X - C (b t)) ^ (p - 1)) ?_
  intro t ht
  exact PolyInt.mul
    (PolyInt.prod_finset (((Finset.univ : Finset (Fin n)).erase i).erase t)
      (fun u => (X - C (b u)) ^ p) (by
        intro u hu
        exact PolyInt.pow (PolyInt.X_sub_C (hb u)) p))
    (PolyInt.pow (PolyInt.X_sub_C (hb t)) (p - 1))

lemma iterate_derivative_C_mul (a : ℂ) (q : ℂ[X]) (m : ℕ) :
    (derivative^[m]) (C a * q) = C a * (derivative^[m]) q := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      rw [derivative_C_mul]
      congr 1
      rw [Function.iterate_succ_apply']

lemma scaledQ_deriv_iter {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n) {s : ℕ} (hs : 0 < s) :
    (derivative^[s]) (scaledQ b p i) = C (p : ℂ) * (derivative^[s - 1]) (scaledQderiv b p i) := by
  have hsucc : s = (s - 1) + 1 := (Nat.sub_add_cancel hs).symm
  rw [hsucc]
  rw [Function.iterate_succ_apply]
  rw [scaledQ_deriv]
  exact iterate_derivative_C_mul (p : ℂ) (scaledQderiv b p i) (s - 1)

lemma scaledQ_deriv_eval_diag_p {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) {s : ℕ} (hs : 0 < s) :
    ∃ v : ℂ, IsIntegral ℤ v ∧
      ((derivative^[s]) (scaledQ b p i)).eval (b i) = (p : ℂ) * v := by
  rw [scaledQ_deriv_iter b p i hs]
  refine ⟨((derivative^[s - 1]) (scaledQderiv b p i)).eval (b i), ?_, ?_⟩
  · exact eval_PolyInt_isIntegral ((derivative^[s - 1]) (scaledQderiv b p i))
      (PolyInt.iterate_derivative (PolyInt_scaledQderiv b p i hb) (s - 1)) (hb i)
  · simp

lemma scaledF_deriv_diag_ge {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) (p : ℕ) (i : Fin n)
    (hp : 0 < p) (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) (hℓ : IsIntegral ℤ ℓ)
    {j : ℕ} (hj : p ≤ j) :
    ∃ u : ℂ, IsIntegral ℤ u ∧
      ((derivative^[j]) (scaledF b ℓ p i)).eval (b i) = (p.factorial : ℂ) * u := by
  rw [scaledF_eq_pow_pred_mul]
  rw [deriv_mul_pow_eval_root (p - 1) j (b i) (C ℓ * scaledQ b p i)]
  have hle : p - 1 ≤ j := by omega
  rw [if_pos hle]
  let s : ℕ := j - (p - 1)
  have hs : 0 < s := by
    dsimp [s]
    omega
  obtain ⟨v, hvint, hv⟩ := scaledQ_deriv_eval_diag_p b p i hb (s := s) hs
  have hdq : ((derivative^[j - (p - 1)]) (C ℓ * scaledQ b p i)).eval (b i) =
      ℓ * ((derivative^[s]) (scaledQ b p i)).eval (b i) := by
    dsimp [s]
    rw [iterate_derivative_C_mul]
    simp
  rw [hdq]
  rw [hv]
  have hfac : (p.factorial : ℂ) = (p : ℂ) * ((p - 1).factorial : ℂ) := by
    have hfacn : p.factorial = p * (p - 1).factorial := by
      have hsucc : p.factorial = (p - 1 + 1).factorial := by
        congr 1
        omega
      rw [hsucc, Nat.factorial_succ]
      congr 1
      omega
    rw [hfacn]
    norm_cast
  refine ⟨(j.choose (j - (p - 1)) : ℂ) * ℓ * v, ?_, ?_⟩
  · exact IsIntegral.mul
      (IsIntegral.mul (isIntegral_natCast_complex (j.choose (j - (p - 1)))) hℓ) hvint
  · rw [hfac]
    ring

lemma deriv_lemmaA_f_eq {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p) (i : Fin n) (j : ℕ) :
    (derivative^[j]) (lemmaA_f α ℓ p i) =
      C (ℓ ^ j) * ((derivative^[j]) (scaledF (fun k : Fin n => ℓ * α k) ℓ p i)).comp (C ℓ * X) := by
  rw [lemmaA_f_eq_scaledF_comp α ℓ hp i]
  exact iterate_derivative_comp_C_mul_X (scaledF (fun k : Fin n => ℓ * α k) ℓ p i) ℓ j

lemma deriv_lemmaA_f_eval {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p) (i : Fin n) (j : ℕ) (k : Fin n) :
    ((derivative^[j]) (lemmaA_f α ℓ p i)).eval (α k) =
      (ℓ ^ j) * (((derivative^[j]) (scaledF (fun t : Fin n => ℓ * α t) ℓ p i)).eval (ℓ * α k)) := by
  rw [deriv_lemmaA_f_eq α ℓ hp i j]
  simp

lemma natDegree_X_sub_C_pow_le (a : ℂ) (q : ℕ) : ((X - C a) ^ q).natDegree ≤ q := by
  calc ((X - C a) ^ q).natDegree ≤ q * (X - C a).natDegree := Polynomial.natDegree_pow_le
       _ ≤ q * 1 := Nat.mul_le_mul_left q (Polynomial.natDegree_X_sub_C_le a)
       _ = q := by rw [mul_one]

lemma lemmaA_f_natDegree_le {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p) (i : Fin n) :
    (lemmaA_f α ℓ p i).natDegree ≤ n * p := by
  have hn : 0 < n := by
    have : (i : ℕ) < n := i.isLt
    omega
  let e : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase i
  have hc : e.card = n - 1 := by
    dsimp [e]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    simp
  have hdegA : ((X - C (α i)) ^ (p - 1)).natDegree ≤ p - 1 := natDegree_X_sub_C_pow_le (α i) (p - 1)
  have hdegB : (∏ k ∈ e, (X - C (α k)) ^ p).natDegree ≤ p * (n - 1) := by
    calc (∏ k ∈ e, (X - C (α k)) ^ p).natDegree ≤ ∑ k ∈ e, ((X - C (α k)) ^ p).natDegree :=
            Polynomial.natDegree_prod_le e (fun k => (X - C (α k)) ^ p)
         _ ≤ ∑ k ∈ e, p := by
            apply Finset.sum_le_sum
            intro k hk
            exact natDegree_X_sub_C_pow_le (α k) p
         _ = p * e.card := by
            rw [Finset.sum_const]
            simp [mul_comm]
         _ = p * (n - 1) := by rw [hc]
  have hC : (C (ℓ ^ (n * p)) * (X - C (α i)) ^ (p - 1)).natDegree ≤ p - 1 := by
    calc (C (ℓ ^ (n * p)) * (X - C (α i)) ^ (p - 1)).natDegree
        ≤ (C (ℓ ^ (n * p))).natDegree + ((X - C (α i)) ^ (p - 1)).natDegree := Polynomial.natDegree_mul_le
        _ = ((X - C (α i)) ^ (p - 1)).natDegree := by simp [Polynomial.natDegree_C]
        _ ≤ p - 1 := hdegA
  unfold lemmaA_f
  calc
    (C (ℓ ^ (n * p)) * (X - C (α i)) ^ (p - 1) *
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p)).natDegree
        ≤ (C (ℓ ^ (n * p)) * (X - C (α i)) ^ (p - 1)).natDegree +
            (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p).natDegree := by
            exact Polynomial.natDegree_mul_le
    _ ≤ (p - 1) + p * (n - 1) := by
            have h2 : (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (α k)) ^ p).natDegree ≤ p * (n - 1) := by
              simpa [e] using hdegB
            omega
    _ ≤ n * p := by
            have hnp : n * p = p * (n - 1) + p := by
              calc
                n * p = (n - 1 + 1) * p := by congr 1; exact (Nat.sub_add_cancel hn).symm
                _ = (n - 1) * p + 1 * p := by rw [add_mul]
                _ = p * (n - 1) + p := by rw [one_mul, mul_comm (n - 1) p]
            rw [hnp]
            omega

lemma sumIDeriv_lemmaA_f_eval_range {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p)
    (i : Fin n) (k : Fin n) :
    (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k) =
      ∑ j ∈ Finset.range (n * p + 1),
        (ℓ ^ j) * (((derivative^[j]) (scaledF (fun t : Fin n => ℓ * α t) ℓ p i)).eval (ℓ * α k)) := by
  have hdeg : (lemmaA_f α ℓ p i).natDegree ≤ n * p := lemmaA_f_natDegree_le α ℓ hp i
  rw [Polynomial.sumIDeriv_apply_of_le hdeg]
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  exact deriv_lemmaA_f_eval α ℓ hp i j k

-- ============ D3: off-diagonal p!-divisibility at sumIDeriv level ============

lemma lemmaA_f_sumIDeriv_offdiag_int {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p)
    (hℓ : IsIntegral ℤ ℓ) (hb : ∀ k : Fin n, IsIntegral ℤ (ℓ * α k)) {i k : Fin n} (hik : k ≠ i) :
    ∃ u : ℂ, IsIntegral ℤ u ∧
      (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k) = (p.factorial : ℂ) * u := by
  classical
  let R : Finset ℕ := Finset.range (n * p + 1)
  let term : ℕ → ℂ := fun j =>
    (ℓ ^ j) * (((derivative^[j]) (scaledF (fun t : Fin n => ℓ * α t) ℓ p i)).eval (ℓ * α k))
  have hterm : ∀ j ∈ R, ∃ w : ℂ, IsIntegral ℤ w ∧ term j = (p.factorial : ℂ) * w := by
    intro j hj
    dsimp [term]
    by_cases hjp : j < p
    · have hz : ((derivative^[j]) (scaledF (fun t : Fin n => ℓ * α t) ℓ p i)).eval (ℓ * α k) = 0 := by
        have hz' := scaledF_deriv_offdiag_lt (fun t : Fin n => ℓ * α t) ℓ hik hjp
        simpa using hz'
      refine ⟨0, isIntegral_zero, ?_⟩
      simp [hz]
    · have hpj : p ≤ j := Nat.le_of_not_gt hjp
      obtain ⟨u0, hu0, hval⟩ := scaledF_deriv_offdiag_ge (fun t : Fin n => ℓ * α t) ℓ p hik
        (by intro t; exact hb t) hℓ hpj
      refine ⟨(ℓ ^ j) * u0, ?_, ?_⟩
      · exact IsIntegral.mul (IsIntegral.pow hℓ j) hu0
      · rw [hval]
        ring
  let w : ℕ → ℂ := fun j => if h : j ∈ R then Classical.choose (hterm j h) else 0
  have hw : ∀ j ∈ R, IsIntegral ℤ (w j) := by
    intro j hj
    dsimp [w]
    rw [dif_pos hj]
    exact (Classical.choose_spec (hterm j hj)).1
  have htw : ∀ j ∈ R, term j = (p.factorial : ℂ) * w j := by
    intro j hj
    dsimp [w]
    rw [dif_pos hj]
    exact (Classical.choose_spec (hterm j hj)).2
  refine ⟨∑ j ∈ R, w j, ?_, ?_⟩
  · exact IsIntegral.sum w (by intro j hj; exact hw j hj)
  · calc
      (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k)
          = ∑ j ∈ R, term j := by
              rw [sumIDeriv_lemmaA_f_eval_range α ℓ hp i k]
      _ = ∑ j ∈ R, (p.factorial : ℂ) * w j := by
              apply Finset.sum_congr rfl
              intro j hj
              exact htw j hj
      _ = (p.factorial : ℂ) * (∑ j ∈ R, w j) := by rw [Finset.mul_sum]

-- ============ D4: diagonal shape at sumIDeriv level ============

lemma lemmaA_f_sumIDeriv_diag_int {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p)
    (hℓ : IsIntegral ℤ ℓ) (hb : ∀ k : Fin n, IsIntegral ℤ (ℓ * α k)) (i : Fin n) :
    ∃ u : ℂ, IsIntegral ℤ u ∧
      (sumIDeriv (lemmaA_f α ℓ p i)).eval (α i) =
        ((p - 1).factorial : ℂ) * ℓ ^ p *
            (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (ℓ * α i - ℓ * α k) ^ p) +
          (p.factorial : ℂ) * u := by
  classical
  have hn : 0 < n := by
    have : (i : ℕ) < n := i.isLt
    omega
  let R : Finset ℕ := Finset.range (n * p + 1)
  let D : ℂ := ((p - 1).factorial : ℂ) * ℓ ^ p *
    (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (ℓ * α i - ℓ * α k) ^ p)
  let b : Fin n → ℂ := fun t => ℓ * α t
  let term : ℕ → ℂ := fun j =>
    (ℓ ^ j) * (((derivative^[j]) (scaledF b ℓ p i)).eval (b i))
  have hb' : ∀ t : Fin n, IsIntegral ℤ (b t) := by
    intro t
    simpa [b] using hb t
  have hpe : p - 1 ∈ R := by
    dsimp [R]
    rw [Finset.mem_range]
    have hple : p ≤ n * p := by
      calc p = p * 1 := by rw [mul_one]
           _ ≤ p * n := Nat.mul_le_mul_left p hn
           _ = n * p := by rw [mul_comm]
    omega
  -- exact value of the diagonal term j = p − 1
  have htermp : term (p - 1) = D := by
    dsimp [term, D, b]
    have hd := scaledF_deriv_diag (fun t : Fin n => ℓ * α t) ℓ hp i
    rw [hd]
    have hℓp : ℓ ^ (p - 1) * ℓ = ℓ ^ p := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      (ℓ ^ (p - 1)) * (((p - 1).factorial : ℂ) * ℓ *
          (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (ℓ * α i - ℓ * α k) ^ p))
          = (((p - 1).factorial : ℂ) * (ℓ ^ (p - 1) * ℓ)) *
              (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (ℓ * α i - ℓ * α k) ^ p) := by ring
      _ = (((p - 1).factorial : ℂ) * ℓ ^ p) *
              (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (ℓ * α i - ℓ * α k) ^ p) := by rw [hℓp]
  -- non-diagonal terms (j ≠ p−1) are p!-divisible (with algebraic-integer quotient)
  have htermo : ∀ j ∈ R.erase (p - 1), ∃ w : ℂ, IsIntegral ℤ w ∧ term j = (p.factorial : ℂ) * w := by
    intro j hj
    have hne : j ≠ p - 1 := (Finset.mem_erase.mp hj).1
    dsimp [term]
    by_cases hlt : j < p - 1
    · have hz : ((derivative^[j]) (scaledF b ℓ p i)).eval (b i) = 0 := by
        simpa [b] using (scaledF_deriv_diag_lt b ℓ i hlt)
      refine ⟨0, isIntegral_zero, ?_⟩
      simp [hz]
    · have hpj : p ≤ j := by
        have : p - 1 ≤ j := Nat.le_of_not_gt hlt
        omega
      obtain ⟨u0, hu0, hval⟩ := scaledF_deriv_diag_ge b ℓ p i hp hb' hℓ hpj
      refine ⟨(ℓ ^ j) * u0, ?_, ?_⟩
      · exact IsIntegral.mul (IsIntegral.pow hℓ j) hu0
      · rw [hval]
        ring
  let w : ℕ → ℂ := fun j => if h : j ∈ R.erase (p - 1) then Classical.choose (htermo j h) else 0
  have hw : ∀ j ∈ R.erase (p - 1), IsIntegral ℤ (w j) := by
    intro j hj
    dsimp [w]
    rw [dif_pos hj]
    exact (Classical.choose_spec (htermo j hj)).1
  have htw : ∀ j ∈ R.erase (p - 1), term j = (p.factorial : ℂ) * w j := by
    intro j hj
    dsimp [w]
    rw [dif_pos hj]
    exact (Classical.choose_spec (htermo j hj)).2
  refine ⟨∑ j ∈ R.erase (p - 1), w j, ?_, ?_⟩
  · exact IsIntegral.sum w (by intro j hj; exact hw j hj)
  · calc
      (sumIDeriv (lemmaA_f α ℓ p i)).eval (α i)
          = ∑ j ∈ R, term j := by
              rw [sumIDeriv_lemmaA_f_eval_range α ℓ hp i i]
      _ = (∑ j ∈ R.erase (p - 1), term j) + term (p - 1) := by
              rw [← Finset.sum_erase_add R term hpe]
      _ = (p.factorial : ℂ) * (∑ j ∈ R.erase (p - 1), w j) + D := by
              rw [htermp]
              congr 1
              calc
                (∑ j ∈ R.erase (p - 1), term j)
                    = ∑ j ∈ R.erase (p - 1), (p.factorial : ℂ) * w j := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        exact htw j hj
                _ = (p.factorial : ℂ) * (∑ j ∈ R.erase (p - 1), w j) := by rw [Finset.mul_sum]
      _ = D + (p.factorial : ℂ) * (∑ j ∈ R.erase (p - 1), w j) := by ring



/-! ## 7b.  The diagonal differences are nonzero (pairwise-distinct exponents)

With pairwise-distinct cleared exponents `b : Fin n → ℂ` the diagonal
difference product `∏_{k≠i}(bᵢ − bₖ)ᵖ` does not vanish (`prod_sub_pow_ne_zero`);
a nonzero clearing scalar preserves distinctness
(`mul_left_injective_of_ne_zero`).  These make the exact diagonal term of
`lemmaA_f_sumIDeriv_diag_int` a *nonzero* algebraic integer, which §8 (the
class step) needs to conclude that the `Jᵢ` are nonzero.
-/

/-- Multiplication by a nonzero scalar on `ℂ` is injective. -/
lemma mul_left_injective_of_ne_zero {ℓ : ℂ} (hℓ : ℓ ≠ 0) :
    Function.Injective (fun x : ℂ => ℓ * x) := by
  exact mul_right_injective₀ hℓ

/-- The diagonal difference product of an injective exponent family is
nonzero: `∏_{k ≠ i} (bᵢ − bₖ)ᵖ ≠ 0`. -/
lemma prod_sub_pow_ne_zero {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n)
    (hinj : Function.Injective b) :
    (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (b i - b k) ^ p) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro k hk
  have hkne : k ≠ i := by
    exact (Finset.mem_erase.mp hk).1
  have hbi : b i ≠ b k := by
    intro h
    have : i = k := hinj h
    exact hkne this.symm
  exact pow_ne_zero p (sub_ne_zero.mpr hbi)

/-! ## 8.  Lemma A assembly: the `Jᵢ`-shape

With the §7 `sumIDeriv` facts in hand, the arithmetic of Lemma A assembles:

* `lemmaA_J_eq`: under the exponential relation
  `Σₖ βₖ·cexp(αₖ) = 0`, the Hermite functional sum
  `Jᵢ := Σₖ βₖ·P(fᵢ, αₖ)` (`P f s = eˢ·F(0) − F(s)`) collapses to the pure
  arithmetic object `−Σₖ βₖ·F(αₖ)` (the `F(0)`-term kills the relation);
* `lemmaA_J_shape`: that object factors as `(p−1)!·Wᵢ` with
  `Wᵢ = −βᵢ·ℓᵖ·∏_{t≠i}(ℓαᵢ−ℓαₜ)ᵖ − p·Sᵢ` and `Sᵢ = Σₖ βₖ·uₖ` an
  *algebraic integer* (the `uₖ` are the §7 `p!`-quotients; each `βₖ` is an
  integer, so the weighted sum stays in `ℤ̄`).

Consequently each `Jᵢ` is an algebraic integer divisible by `(p−1)!`, and
`Wᵢ ≡ −βᵢ·ℓᵖ·δᵢᵖ (mod p)` — the congruence the §11 norm argument feeds on.

* `lemmaA_J_ne_zero` (**nonzero criterion**): if the diagonal
  `(βᵢ:ℂ)·ℓᵖ·∏_{t≠i}(ℓαᵢ−ℓαₜ)ᵖ` is *not* of the form `p·w` with `w` an
  algebraic integer (`hnot`), then `Jᵢ ≠ 0`.  `hnot` is exactly what the
  Commons norm lemma supplies: `Commons.FieldTheory.Norm.norm_pow_not_mem_smul`
  (Submission/Commons/FieldTheory/Norm/norm_pow_not_mem_smul.lean) proves, for
  a finite field extension `L/ℚ`, `δ : L` integral with integer norm `N`, a
  nonzero integer `m` and a prime `p ∤ m·N`, that `m·δᵖ` is not `p`-times an
  integral element; its companion `norm_isInt` extracts `N ∈ ℤ` from
  integrality.  Filling `hnot` for the concrete family needs the ambient
  field `L = ℚ(ℓα₁,…,ℓαₙ)` (all cleared exponents integral, `δᵢ` integral
  nonzero, `m = βᵢ·ℓᵖ ≠ 0`) and the `ℂ`-to-`L` transfer of the `uₖ` (hence of
  `Sᵢ` and `Wᵢ`) — the remaining piece of the `Wᵢ ≠ 0` step.  The analytic
  side (bounding `|Σₖ βₖ·P(fᵢ,αₖ)|`, hence `|∏ᵢ Jᵢ|`) and the symmetric step
  (making `∏ᵢ Jᵢ ∈ ℚ`) are the other remaining steps of Lemma A.
-/

/-- **Lemma A assembly (the `Jᵢ`-shape).**  With the two `sumIDeriv` facts of
§7, `Jᵢ := −Σₖ βₖ·F(αₖ)` (the arithmetic form the Hermite functional takes
under the exponential relation) factors as `(p−1)!·Wᵢ` with
`Wᵢ = −βᵢ·ℓᵖ·∏_{t≠i}(ℓαᵢ−ℓαₜ)ᵖ − p·Sᵢ` an *algebraic integer*
(`Sᵢ = Σₖ βₖ·uₖ` the integer-weighted sum of the `p!`-quotients). -/
lemma lemmaA_J_shape {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p)
    (hℓ : IsIntegral ℤ ℓ) (hb : ∀ k : Fin n, IsIntegral ℤ (ℓ * α k))
    (β : Fin n → ℤ) (i : Fin n) :
    ∃ S : ℂ, IsIntegral ℤ S ∧
      - (∑ k : Fin n, (β k : ℂ) * (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k)) =
        ((p - 1).factorial : ℂ) *
          (-(β i : ℂ) * ℓ ^ p *
              (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (ℓ * α i - ℓ * α t) ^ p) -
            (p : ℂ) * S) := by
  classical
  let D : ℂ := ((p - 1).factorial : ℂ) * ℓ ^ p *
    (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (ℓ * α i - ℓ * α t) ^ p)
  obtain ⟨ui, hui, hvi⟩ := lemmaA_f_sumIDeriv_diag_int α ℓ hp hℓ hb i
  have hoff : ∀ k : Fin n, k ≠ i → ∃ u : ℂ, IsIntegral ℤ u ∧
      (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k) = (p.factorial : ℂ) * u := by
    intro k hik
    exact lemmaA_f_sumIDeriv_offdiag_int α ℓ hp hℓ hb hik
  let u : Fin n → ℂ := fun k => if hk : k = i then ui else Classical.choose (hoff k hk)
  have hu_int : ∀ k : Fin n, IsIntegral ℤ (u k) := by
    intro k
    by_cases hk : k = i
    · subst k
      dsimp [u]
      simp [hui]
    · dsimp [u]
      rw [dif_neg hk]
      exact (Classical.choose_spec (hoff k hk)).1
  have hu_off : ∀ {k : Fin n} (hk : k ≠ i),
      (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k) = (p.factorial : ℂ) * u k := by
    intro k hk
    dsimp [u]
    rw [dif_neg hk]
    exact (Classical.choose_spec (hoff k hk)).2
  have hui_u : u i = ui := by
    dsimp [u]
    simp
  have hF_diag : (sumIDeriv (lemmaA_f α ℓ p i)).eval (α i) = D + (p.factorial : ℂ) * u i := by
    dsimp [D]
    rw [hui_u]
    exact hvi
  let S : ℂ := ∑ k : Fin n, (β k : ℂ) * u k
  have hS_int : IsIntegral ℤ S := by
    dsimp [S]
    exact IsIntegral.sum (fun k => (β k : ℂ) * u k) (by
      intro k hk
      exact IsIntegral.mul (isIntegral_intCast (β k)) (hu_int k))
  let e : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase i
  let Fval : Fin n → ℂ := fun k => (β k : ℂ) * (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k)
  let g : Fin n → ℂ := fun k => (β k : ℂ) * u k
  have hsplit : (∑ k : Fin n, Fval k) = (∑ k ∈ e, Fval k) + Fval i := by
    dsimp [e, Fval]
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin n))
        (fun k => (β k : ℂ) * (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k)) (Finset.mem_univ i)]
  have hA : (∑ k ∈ e, Fval k) = (p.factorial : ℂ) * (∑ k ∈ e, g k) := by
    calc
      (∑ k ∈ e, Fval k) = (∑ k ∈ e, (p.factorial : ℂ) * g k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hne : k ≠ i := (Finset.mem_erase.mp hk).1
            dsimp [Fval, g]
            rw [hu_off hne]
            ring
      _ = (p.factorial : ℂ) * (∑ k ∈ e, g k) := by rw [Finset.mul_sum]
  have hB : Fval i = (β i : ℂ) * D + (p.factorial : ℂ) * g i := by
    dsimp [Fval, g]
    rw [hF_diag]
    ring
  have hsg : (∑ k ∈ e, g k) + g i = S := by
    dsimp [S, e, g]
    exact Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun k => (β k : ℂ) * u k) (Finset.mem_univ i)
  have hsum : (∑ k : Fin n, (β k : ℂ) * (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k)) =
      (p.factorial : ℂ) * S + (β i : ℂ) * D := by
    calc
      (∑ k : Fin n, (β k : ℂ) * (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k))
          = (∑ k ∈ e, Fval k) + Fval i := by
              dsimp [Fval]
              exact hsplit
      _ = (p.factorial : ℂ) * (∑ k ∈ e, g k) + ((β i : ℂ) * D + (p.factorial : ℂ) * g i) := by
              rw [hA, hB]
      _ = (p.factorial : ℂ) * ((∑ k ∈ e, g k) + g i) + (β i : ℂ) * D := by ring
      _ = (p.factorial : ℂ) * S + (β i : ℂ) * D := by rw [hsg]
  have hfac : (p.factorial : ℂ) = (p : ℂ) * ((p - 1).factorial : ℂ) := by
    exact_mod_cast factorial_eq_mul_pred hp
  refine ⟨S, hS_int, ?_⟩
  calc
    - (∑ k : Fin n, (β k : ℂ) * (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k))
        = -((p.factorial : ℂ) * S + (β i : ℂ) * D) := by rw [hsum]
    _ = ((p - 1).factorial : ℂ) *
          (-(β i : ℂ) * ℓ ^ p *
              (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (ℓ * α i - ℓ * α t) ^ p) -
            (p : ℂ) * S) := by
          dsimp [D]
          rw [hfac]
          ring

lemma lemmaA_J_eq {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (i : Fin n)
    (β : Fin n → ℤ)
    (hrel : (∑ k : Fin n, (β k : ℂ) * cexp (α k)) = 0) :
    (∑ k : Fin n, (β k : ℂ) * (P (lemmaA_f α ℓ p i) (α k))) =
      - (∑ k : Fin n, (β k : ℂ) * (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k)) := by
  let f : ℂ[X] := lemmaA_f α ℓ p i
  let F : ℂ[X] := sumIDeriv f
  have hP : ∀ s : ℂ, P f s = exp s * F.eval 0 - F.eval s := by
    intro s
    rfl
  have hsum1 : (∑ k : Fin n, (β k : ℂ) * (exp (α k) * F.eval 0)) =
      F.eval 0 * (∑ k : Fin n, (β k : ℂ) * exp (α k)) := by
    calc
      (∑ k : Fin n, (β k : ℂ) * (exp (α k) * F.eval 0))
          = (∑ k : Fin n, F.eval 0 * ((β k : ℂ) * exp (α k))) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = F.eval 0 * (∑ k : Fin n, (β k : ℂ) * exp (α k)) := by rw [Finset.mul_sum]
  calc
    (∑ k : Fin n, (β k : ℂ) * (P f (α k)))
        = (∑ k : Fin n, (β k : ℂ) * (exp (α k) * F.eval 0 - F.eval (α k))) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hP]
    _ = (∑ k : Fin n, (β k : ℂ) * (exp (α k) * F.eval 0)) -
          (∑ k : Fin n, (β k : ℂ) * F.eval (α k)) := by
            calc
              (∑ k : Fin n, (β k : ℂ) * (exp (α k) * F.eval 0 - F.eval (α k)))
                  = (∑ k : Fin n, ((β k : ℂ) * (exp (α k) * F.eval 0) - (β k : ℂ) * F.eval (α k))) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      ring
              _ = (∑ k : Fin n, (β k : ℂ) * (exp (α k) * F.eval 0)) -
                    (∑ k : Fin n, (β k : ℂ) * F.eval (α k)) := by
                      rw [Finset.sum_sub_distrib]
    _ = 0 - (∑ k : Fin n, (β k : ℂ) * F.eval (α k)) := by
            rw [hsum1]
            rw [hrel]
            simp
    _ = - (∑ k : Fin n, (β k : ℂ) * F.eval (α k)) := by simp

/-- **Nonzero criterion for the `Jᵢ` of Lemma A.**  Given the shape
`Jᵢ = (p−1)!·(−βᵢ·ℓᵖ·∏_{t≠i}(ℓαᵢ−ℓαₜ)ᵖ − p·Sᵢ)` (`lemmaA_J_shape`) and the
§11 norm input — the hypothesis `hnot`: the diagonal
`(βᵢ:ℂ)·ℓᵖ·∏_{t≠i}(ℓαᵢ−ℓαₜ)ᵖ` is *not* of the form `p·w` with `w` an
algebraic integer — `Jᵢ := −Σₖ βₖ·F(αₖ)` is nonzero.  (`hnot` is exactly
what the Commons norm lemma `norm_pow_not_mem_smul` supplies, once the
field/`ℤ̄`-reduction is made: for primes `p ∤ βᵢ·ℓ·N(δᵢ)`, with `βᵢ ≠ 0`,
`ℓ ≠ 0`, `∏_{t≠i}(ℓαᵢ−ℓαₜ)ᵖ ≠ 0`.) -/
lemma lemmaA_J_ne_zero {n : ℕ} (α : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p)
    (hℓ : IsIntegral ℤ ℓ) (hb : ∀ k : Fin n, IsIntegral ℤ (ℓ * α k))
    (β : Fin n → ℤ) (i : Fin n)
    (hnot : ¬ ∃ w : ℂ, IsIntegral ℤ w ∧
        (β i : ℂ) * ℓ ^ p *
            (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (ℓ * α i - ℓ * α t) ^ p) =
          (p : ℂ) * w) :
    - (∑ k : Fin n, (β k : ℂ) * (sumIDeriv (lemmaA_f α ℓ p i)).eval (α k)) ≠ 0 := by
  classical
  intro hJ0
  obtain ⟨S, hSint, hshape⟩ := lemmaA_J_shape α ℓ hp hℓ hb β i
  let A : ℂ := (β i : ℂ) * ℓ ^ p *
    (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (ℓ * α i - ℓ * α t) ^ p)
  have hfac0 : ((p - 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (p - 1))
  have hmul : ((p - 1).factorial : ℂ) * (-A - (p : ℂ) * S) = 0 := by
    simpa [A] using (hshape.symm.trans hJ0)
  have hW0 : -A - (p : ℂ) * S = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_left hfac0
  have hAS : A + (p : ℂ) * S = 0 := by
    calc
      A + (p : ℂ) * S = -(-A - (p : ℂ) * S) := by ring
      _ = 0 := by rw [hW0]; simp
  have hA : A = (p : ℂ) * (-S) := by
    calc
      A = (A + (p : ℂ) * S) - (p : ℂ) * S := by ring
      _ = -((p : ℂ) * S) := by rw [hAS]; ring
      _ = (p : ℂ) * (-S) := by ring
  apply hnot
  refine ⟨-S, IsIntegral.neg hSint, ?_⟩
  simpa [A] using hA


/-! ## 9.  The ambient number field of a finite algebraic family

For a finite family `b : Fin n → ℂ` of algebraic integers (the *cleared*
exponents `bₖ = ℓαₖ` of §7/§8), the ambient field is the smallest
intermediate field of `ℂ/ℚ` containing every `bₖ`:

`L := clearedField b = ⨆ₖ ℚ⟮bₖ⟯ ≤ ℂ`.

It is finite-dimensional over `ℚ` (`clearedField_finiteDimensional`; each
`ℚ⟮bₖ⟯` is finite because `bₖ` is algebraic —
`clearedField_finiteDimensional_of_isIntegral` for the ℤ-integral inputs),
and each generator is an element `clearedElem b k : L` (`clearedField_mem`,
`clearedElem_coe`) integral over `ℤ` (`clearedElem_isIntegral`).

This is the field in which the §11 norm argument runs: with
`δᵢᵖ := ∏_{t≠i}(bᵢ−bₜ)ᵖ ∈ L` (`clearedDelta`, `clearedDelta_coe`) integral
over `ℤ` (`clearedDelta_isIntegral`), the Commons lemma
`norm_pow_not_mem_smul` supplies the `hnot` hypothesis of
`lemmaA_J_ne_zero` (after the ℂ-to-L transfer of `Sᵢ`, `Wᵢ`).
-/

def clearedField {n : ℕ} (b : Fin n → ℂ) : IntermediateField ℚ ℂ :=
  (⨆ k : Fin n, IntermediateField.adjoin ℚ ({b k} : Set ℂ) : IntermediateField ℚ ℂ)

lemma clearedField_finiteDimensional {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ k : Fin n, IsIntegral ℚ (b k)) :
    FiniteDimensional ℚ (clearedField b) := by
  haveI : ∀ k : Fin n, FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({b k} : Set ℂ)) := by
    intro k
    exact IntermediateField.adjoin.finiteDimensional (x := b k) (hb k)
  exact IntermediateField.finiteDimensional_iSup_of_finite (K := ℚ) (L := ℂ) (ι := Fin n)
    (t := fun k : Fin n => IntermediateField.adjoin ℚ ({b k} : Set ℂ))

lemma clearedField_finiteDimensional_of_isIntegral {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) :
    FiniteDimensional ℚ (clearedField b) := by
  exact clearedField_finiteDimensional b (fun k =>
    IsIntegral.tower_top (R := ℤ) (A := ℚ) (B := ℂ) (hb k))

lemma clearedField_mem {n : ℕ} (b : Fin n → ℂ) (k : Fin n) : (b k : ℂ) ∈ clearedField b := by
  exact (le_iSup (fun j : Fin n => IntermediateField.adjoin ℚ ({b j} : Set ℂ)) k)
    (IntermediateField.mem_adjoin_simple_self (F := ℚ) (E := ℂ) (b k))

def clearedElem {n : ℕ} (b : Fin n → ℂ) (k : Fin n) : clearedField b :=
  ⟨b k, clearedField_mem b k⟩

lemma clearedElem_coe {n : ℕ} (b : Fin n → ℂ) (k : Fin n) :
    ((clearedElem b k : clearedField b) : ℂ) = b k := by
  rfl

lemma clearedElem_isIntegral {n : ℕ} (b : Fin n → ℂ) (k : Fin n)
    (hb : IsIntegral ℤ (b k)) : IsIntegral ℤ (clearedElem b k) := by
  rcases hb with ⟨f, hfmonic, hfroot⟩
  refine ⟨f, hfmonic, ?_⟩
  apply (algebraMap (clearedField b) ℂ).injective
  rw [Polynomial.hom_eval₂]
  have hc : (algebraMap (clearedField b) ℂ) (clearedElem b k) = b k := by
    rfl
  have hcomp : (algebraMap (clearedField b) ℂ).comp (algebraMap ℤ (clearedField b)) =
      algebraMap ℤ ℂ := by
    ext z
    simp
  rw [hc, hcomp]
  simpa using hfroot

/-- `δᵢᵖ := ∏_{t≠i} (bᵢ − bₜ)ᵖ` as an element of the ambient field. -/
def clearedDelta {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n) : clearedField b :=
  ∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (clearedElem b i - clearedElem b t) ^ p

lemma clearedDelta_coe {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n) :
    ((clearedDelta b p i : clearedField b) : ℂ) =
      ∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (b i - b t) ^ p := by
  dsimp [clearedDelta]
  change (algebraMap (clearedField b) ℂ)
    (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (clearedElem b i - clearedElem b t) ^ p) =
      ∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (b i - b t) ^ p
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro t ht
  rw [map_pow, map_sub]
  simp [clearedElem_coe]

lemma clearedDelta_isIntegral {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) : IsIntegral ℤ (clearedDelta b p i) := by
  dsimp [clearedDelta]
  exact IsIntegral.prod (fun t => (clearedElem b i - clearedElem b t) ^ p) (by
    intro t ht
    exact IsIntegral.pow (IsIntegral.sub (clearedElem_isIntegral b i (hb i))
      (clearedElem_isIntegral b t (hb t))) p)



/-! ## 9b.  Nonzero of the diagonal in the ambient field

For an injective cleared family, `δᵢᵖ = ∏_{t≠i}(bᵢ−bₜ)ᵖ` is nonzero in
`L` (`clearedDelta_ne_zero`, via the §7b product-nonzero lemma and the
injectivity of the coefficient map to `ℂ`).  Together with
`clearedDelta_isIntegral` this gives the nonzero integral element the
`norm_pow_not_mem_smul` application needs (its norm `N(δᵢ) ≠ 0`, and the
prime-exclusion `p ∤ βᵢ·ℓ·N(δᵢ)` is then a finite avoidance).
-/

/-- For an injective family `b`, the diagonal element `δᵢᵖ ∈ L` is nonzero. -/
lemma clearedDelta_ne_zero {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n)
    (hinj : Function.Injective b) : clearedDelta b p i ≠ 0 := by
  intro h0
  have hc0 : ((clearedDelta b p i : clearedField b) : ℂ) = 0 := by
    simpa using congrArg (fun x : clearedField b => (x : ℂ)) h0
  have hc : ((clearedDelta b p i : clearedField b) : ℂ) ≠ 0 := by
    rw [clearedDelta_coe]
    exact prod_sub_pow_ne_zero b p i hinj
  exact hc hc0


/-! ## 10.  `Jᵢ ≠ 0` for suitable primes (the `Wᵢ ≠ 0` step)

This section completes the arithmetic of Lemma A.  For a *cleared* exponent
family — `α : Fin n → ℂ` with a positive integer `ℓ₀` such that every
`ℓ₀·αₖ` is an algebraic integer, pairwise distinct after clearing, and
`βᵢ ≠ 0` — there is a fixed nonzero integer `c` (`βᵢ·ℓ₀·N(δᵢ)`, with
`δᵢ = ∏_{t≠i}(ℓ₀αᵢ−ℓ₀αₜ)`) such that for every prime `p ∤ c`:

`Jᵢ := −Σₖ βₖ·F(αₖ) ≠ 0`   (`F = sumIDeriv (fᵢ)` at `ℓ = ℓ₀`)

(`lemmaA_J_ne_zero_cleared`).  The proof chains the pieces built so far:

* §9 puts the diagonal in the ambient field: `δL := clearedDelta b 1 i ∈ L`
  with `bₖ = ℓ₀αₖ`, integral over `ℤ` (`clearedDelta_isIntegral`), nonzero
  for the injective family (`clearedDelta_ne_zero`), coefficient `δᵢ`
  (`clearedDelta_coe`, `clearedDelta_one_pow_coe`);
* the diagonal of `lemmaA_J_shape` is `m·δLᵖ` with the integer
  `m = βᵢ·(ℓ₀:ℤ)ᵖ` (`int_mul_pow_cast`);
* `lemmaA_J_ne_zero` reduces `Jᵢ ≠ 0` to `hnot` (the diagonal is not
  `p`-times an algebraic integer); assuming a witness `w`, the field transfer
  `wL = m·δLᵖ/p ∈ L` (coe `w`, integral by downward `isIntegral_algebraMap`)
  makes `m·δLᵖ = p·wL` in `L`, and
* the Commons norm lemma `norm_pow_not_mem_smul` (`norm_isInt` for the
  integer `Nδ = N(δL)`) kills that equation when `p ∤ m·Nδ` — which follows
  from `p ∤ βᵢ·ℓ₀·Nδ` by primality (`hpd`).

Combined with `lemmaA_J_eq` (the Hermite-functional bridge), the eventual
`Jᵢ := Σₖ βₖ·P(fᵢ,αₖ)` is the nonzero algebraic integer divisible by
`(p−1)!` that the symmetric step and the analytic bound feed on.  The three
small helpers at the head of this section (`clearedDelta_one_pow_coe`,
`int_mul_pow_cast`, `norm_ne_zero_int`) are generic and reusable.
-/

lemma clearedDelta_one_pow_coe {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n) :
    (((clearedDelta b 1 i : clearedField b) : ℂ) ^ p) =
      ∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, (b i - b t) ^ p := by
  rw [clearedDelta_coe]
  simp only [pow_one]
  rw [← Finset.prod_pow]

lemma int_mul_pow_cast (β : ℤ) (ℓ₀ : ℕ) (p : ℕ) :
    (((β * (ℓ₀ : ℤ) ^ p : ℤ) : ℂ)) = (β : ℂ) * ((ℓ₀ : ℂ) ^ p) := by
  rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast]

lemma norm_ne_zero_int {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    {δ : L} (hδ0 : δ ≠ 0) {N : ℤ} (hN : (N : ℚ) = Algebra.norm ℚ δ) : N ≠ 0 := by
  intro hN0
  have hnorm0 : Algebra.norm ℚ δ = 0 := by
    rw [← hN, hN0]
    simp
  have hnf : Algebra.norm ℚ δ ≠ 0 := by
    exact (Algebra.norm_ne_zero_iff (R := ℚ) (S := L)).2 hδ0
  exact hnf hnorm0

/-- **§10: `Jᵢ ≠ 0` for primes avoiding a fixed integer.**  For a cleared
exponent family `α` (`ℓ₀•αₖ` algebraic integers), pairwise distinct after
clearing, and a nonzero class coefficient `βᵢ`, there is a fixed nonzero
integer `c` (essentially `βᵢ·ℓ₀·N(δᵢ)`) such that for every prime
`p ∤ c` the arithmetic object `Jᵢ = −Σₖ βₖ·F(αₖ)` is nonzero.  This is the
`Wᵢ ≠ 0` step of §11: `lemmaA_J_shape` + `lemmaA_J_ne_zero` plus the
Commons norm lemma `norm_pow_not_mem_smul` (the diagonal
`(βᵢ:ℂ)·ℓᵖ·∏(ℓαᵢ−ℓαₜ)ᵖ` is not `p`-times an algebraic integer when
`p ∤ βᵢ·ℓ₀·N(δᵢ)`). -/
lemma lemmaA_J_ne_zero_cleared {n : ℕ} (α : Fin n → ℂ) (ℓ₀ : ℕ) (hℓ0 : ℓ₀ ≠ 0)
    (hb : ∀ k : Fin n, IsIntegral ℤ ((ℓ₀ : ℂ) * α k))
    (β : Fin n → ℤ) (i : Fin n) (hβi : β i ≠ 0)
    (hinj : Function.Injective (fun k : Fin n => (ℓ₀ : ℂ) * α k)) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ p : ℕ, Nat.Prime p → ¬ (p : ℤ) ∣ c →
      - (∑ k : Fin n, (β k : ℂ) * (sumIDeriv (lemmaA_f α (ℓ₀ : ℂ) p i)).eval (α k)) ≠ 0 := by
  classical
  let b : Fin n → ℂ := fun k => (ℓ₀ : ℂ) * α k
  have hbL : ∀ k : Fin n, IsIntegral ℤ (b k) := by
    intro k
    simpa [b] using hb k
  haveI hfd : FiniteDimensional ℚ (clearedField b) :=
    clearedField_finiteDimensional b
      (fun k => IsIntegral.tower_top (R := ℤ) (A := ℚ) (B := ℂ) (hbL k))
  let δL : clearedField b := clearedDelta b 1 i
  have hδint : IsIntegral ℤ δL := clearedDelta_isIntegral b 1 i hbL
  have hδ0 : δL ≠ 0 := clearedDelta_ne_zero b 1 i hinj
  obtain ⟨Nδ, hNδ⟩ := Commons.FieldTheory.Norm.norm_isInt (L := clearedField b) (δ := δL) hδint
  have hNδ0 : Nδ ≠ 0 := norm_ne_zero_int (L := clearedField b) (δ := δL) hδ0 hNδ
  let c : ℤ := β i * (ℓ₀ : ℤ) * Nδ
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero hβi (by exact_mod_cast hℓ0)) hNδ0
  refine ⟨c, hc0, ?_⟩
  intro p hp hpnd
  let m : ℤ := β i * (ℓ₀ : ℤ) ^ p
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact mul_ne_zero hβi (pow_ne_zero p (by exact_mod_cast hℓ0))
  apply lemmaA_J_ne_zero α (ℓ₀ : ℂ) (Nat.Prime.pos hp) (isIntegral_natCast_complex ℓ₀) hb β i
  intro hw
  rcases hw with ⟨w, hwint, hEq⟩
  let wL : clearedField b := (m : clearedField b) * δL ^ p / (p : clearedField b)
  have hAm : (m : ℂ) * (((δL : clearedField b) : ℂ) ^ p) =
      (β i : ℂ) * (ℓ₀ : ℂ) ^ p *
        (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i,
          ((ℓ₀ : ℂ) * α i - (ℓ₀ : ℂ) * α t) ^ p) := by
    dsimp [m, δL, b]
    rw [int_mul_pow_cast]
    rw [clearedDelta_one_pow_coe]
  have hwL_c1 : (wL : ℂ) =
      (m : ℂ) * (((δL : clearedField b) : ℂ) ^ p) / (p : ℂ) := by
    rfl
  have hcoewL : (wL : ℂ) = w := by
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
    calc
      (wL : ℂ) = (m : ℂ) * (((δL : clearedField b) : ℂ) ^ p) / (p : ℂ) := hwL_c1
      _ = w := by
            rw [hAm, hEq]
            field_simp [hpC]
  have hwL_int : IsIntegral ℤ wL := by
    have hwLc : IsIntegral ℤ ((wL : clearedField b) : ℂ) := by
      rw [hcoewL]
      exact hwint
    exact (isIntegral_algebraMap_iff (R := ℤ) (A := clearedField b) (B := ℂ)).mp hwLc
  have hEqL : (m : clearedField b) * δL ^ p = (p : clearedField b) * wL := by
    dsimp [wL]
    field_simp [show (p : clearedField b) ≠ 0 by exact_mod_cast (Nat.Prime.ne_zero hp)]
  have hpd : ¬ (p : ℤ) ∣ m * Nδ := by
    intro hd
    have hpz : Prime (p : ℤ) := (Nat.prime_iff_prime_int).1 hp
    have hd' : (p : ℤ) ∣ (β i * (ℓ₀ : ℤ) ^ p) * Nδ := by
      simpa [m] using hd
    rcases (Prime.dvd_mul hpz).1 hd' with hX | hN
    · -- p | βᵢ·(ℓ₀:ℤ)^p : split into p | βᵢ or p | (ℓ₀)^p
      rcases (Prime.dvd_mul hpz).1 hX with hβ | hℓp
      · have h1 : (p : ℤ) ∣ β i * (ℓ₀ : ℤ) := dvd_mul_of_dvd_left hβ (ℓ₀ : ℤ)
        exact hpnd (dvd_mul_of_dvd_left h1 Nδ)
      · have hℓ : (p : ℤ) ∣ (ℓ₀ : ℤ) := hpz.dvd_of_dvd_pow hℓp
        have h1 : (p : ℤ) ∣ β i * (ℓ₀ : ℤ) := by
          simpa [mul_comm] using (dvd_mul_of_dvd_right hℓ (β i))
        exact hpnd (dvd_mul_of_dvd_left h1 Nδ)
    · -- p | Nδ
      exact hpnd (dvd_mul_of_dvd_right hN (β i * (ℓ₀ : ℤ)))
  exact (Commons.FieldTheory.Norm.norm_pow_not_mem_smul (L := clearedField b) (δ := δL)
    hδ0 hδint (m := m) hm0 hp (N := Nδ) hNδ hpd) ⟨wL, hwL_int, hEqL⟩


/-- The Hermite-functional `Jᵢ := Σₖ βₖ·P(fᵢ, αₖ)` of Lemma A is nonzero
for primes avoiding a fixed integer (given the exponential relation). -/
lemma lemmaA_J_functional_ne_zero {n : ℕ} (α : Fin n → ℂ) (ℓ₀ : ℕ) (hℓ0 : ℓ₀ ≠ 0)
    (hb : ∀ k : Fin n, IsIntegral ℤ ((ℓ₀ : ℂ) * α k))
    (β : Fin n → ℤ) (i : Fin n) (hβi : β i ≠ 0)
    (hinj : Function.Injective (fun k : Fin n => (ℓ₀ : ℂ) * α k))
    (hrel : (∑ k : Fin n, (β k : ℂ) * cexp (α k)) = 0) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ p : ℕ, Nat.Prime p → ¬ (p : ℤ) ∣ c →
      (∑ k : Fin n, (β k : ℂ) * (P (lemmaA_f α (ℓ₀ : ℂ) p i) (α k))) ≠ 0 := by
  obtain ⟨c, hc0, hJ⟩ := lemmaA_J_ne_zero_cleared α ℓ₀ hℓ0 hb β i hβi hinj
  refine ⟨c, hc0, ?_⟩
  intro p hp hpnd
  have hJp : - (∑ k : Fin n, (β k : ℂ) * (sumIDeriv (lemmaA_f α (ℓ₀ : ℂ) p i)).eval (α k)) ≠ 0 :=
    hJ p hp hpnd
  have hbridge := lemmaA_J_eq α (ℓ₀ : ℂ) (p := p) i β hrel
  rw [hbridge]
  exact hJp


/-! ## 11.  The `conjRoots`-closed class structure (scaled variables)

With `Wᵢ ≠ 0` done (§10), Lemma A's remaining algebra is the *class
structure* of the exponent families.  In the scaled variables (`bₖ = ℓαₖ`)
the relevant notion is that the family is **closed under `ℚ`-conjugation**
(`conjClosedFamily`: every conjugate of every member is a member; for the
§9/§10 families the members are algebraic integers and the family is
pairwise distinct, so the family is a disjoint union of full `conjRoots`-
classes).  The polynomial vanishing at the whole family is

`H̃(y) = ∏ₖ (y − bₖ)`   (`clearedH`).

Its coefficients are algebraic integers whenever the `bₖ` are
(`clearedH_PolyInt`, `clearedH_coeff_isIntegral`), and the full integrality
`H̃ ∈ ℤ[y]` holds for a pairwise-distinct conjugate-closed family
(`clearedH_mem_Z`: `∃ P : ℤ[X]`, `H̃ = P.map`).  This is committed in the
Commons as `Polynomial.Prod.MonicProdConjClosed` (grouping each
`conjRoots`-class: per class `∏_{w∈conjRoots z}(y−w) = minpoly ℚ z` —
`map_minpoly_eq_prod_X_sub_C` of `Lindemann.lean` §1 — and `minpoly` of an
algebraic integer has integer coefficients); `clearedH_mem_Z` is the module
bridge from the `conjRoots`-membership closure to the Commons statement.
The class power sums `Σ_{t ∈ class} (b t)ʳ ∈ ℚ`
(`class_power_sum_rat` below, from the Commons `trace_rat_poly`) are the
second input of the symmetric step.
-/

/-- A family closed under `ℚ`-conjugation: every conjugate of every member is
again a member. -/
def conjClosedFamily {n : ℕ} (b : Fin n → ℂ) : Prop :=
  ∀ k : Fin n, ∀ w : ℂ, w ∈ conjRoots (b k) → ∃ t : Fin n, b t = w

/-- `H̃ = ∏ₖ (X − bₖ)`: the monic polynomial vanishing at the family. -/
def clearedH {n : ℕ} (b : Fin n → ℂ) : ℂ[X] :=
  ∏ k : Fin n, (X - C (b k))

/-- Coefficients of `H̃` are algebraic integers whenever the family consists
of algebraic integers. -/
lemma clearedH_PolyInt {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) : PolyInt (clearedH b) := by
  dsimp [clearedH]
  exact PolyInt.prod_finset (Finset.univ : Finset (Fin n)) (fun k => X - C (b k)) (by
    intro k hk
    exact PolyInt.X_sub_C (hb k))

/-- Each coefficient of `H̃` is an algebraic integer. -/
lemma clearedH_coeff_isIntegral {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) (m : ℕ) : IsIntegral ℤ ((clearedH b).coeff m) := by
  exact clearedH_PolyInt b hb m


/-- power sum over a conjugate class is rational (index-level) -/
lemma class_power_sum_rat {n : ℕ} (b : Fin n → ℂ) (hinj : Function.Injective b)
    (hclosed : conjClosedFamily b) (hb : ∀ k : Fin n, IsIntegral ℤ (b k))
    (k : Fin n) (r : ℕ) :
    ∃ q : ℚ,
      (∑ t ∈ (Finset.univ.filter (fun t : Fin n => b t ∈ conjRoots (b k))), (b t) ^ r) = (q : ℂ) := by
  classical
  let C : Finset (Fin n) := Finset.univ.filter (fun t : Fin n => b t ∈ conjRoots (b k))
  have hsum_img : (∑ t ∈ C, (b t) ^ r) = ∑ w ∈ C.image b, w ^ r := by
    rw [Finset.sum_image]
    intro t ht t' ht' h
    exact hinj h
  -- C.image b = conjRoots(b k) as toFinset
  have hbkI : IsIntegral ℚ (b k) := IsIntegral.tower_top (R := ℤ) (A := ℚ) (B := ℂ) (hb k)
  have hbk : IsAlgebraic ℚ (b k) := (isAlgebraic_iff_isIntegral).mpr hbkI
  have hnoduproots : ((minpoly ℚ (b k)).aroots ℂ).Nodup := by
    rw [Polynomial.aroots_def]
    apply Polynomial.nodup_roots
    exact Polynomial.Separable.map (minpoly.irreducible hbkI).separable
  have himg : C.image b = (conjRoots (b k)).toFinset := by
    dsimp [C]
    ext w
    constructor
    · intro hw
      rcases (Finset.mem_image.mp hw) with ⟨t, ht, hbt⟩
      have htc : b t ∈ conjRoots (b k) := (Finset.mem_filter.mp ht).2
      have : w ∈ conjRoots (b k) := by
        rw [← hbt]
        exact htc
      exact (Multiset.mem_toFinset).2 this
    · intro hw
      have hw' : w ∈ conjRoots (b k) := (Multiset.mem_toFinset).1 hw
      rcases hclosed k w hw' with ⟨t, hbt⟩
      refine (Finset.mem_image.mpr) ⟨t, ?_, hbt⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, (by rwa [hbt])⟩
  -- sum over conjRoots-multiset of w^r is rational
  obtain ⟨q, hq⟩ := Commons.FieldTheory.Minpoly.ConjRoots.trace_rat_poly hbk (X ^ r)
  -- (X^r).map.eval w = w^r over the multiset
  have hms : (((minpoly ℚ (b k)).aroots ℂ).map (fun w : ℂ => w ^ r)).sum = (q : ℂ) := by
    simpa [Polynomial.eval_map, Polynomial.eval_pow] using hq
  -- multiset sum ↔ toFinset sum (nodup)
  have hnodup_sub : (∑ w : {y : ℂ // y ∈ (minpoly ℚ (b k)).aroots ℂ}, w.1 ^ r) =
      (((minpoly ℚ (b k)).aroots ℂ).map (fun w : ℂ => w ^ r)).sum := by
    exact Commons.FieldTheory.Minpoly.ConjRoots.multiset_nodup_sum_subtype
      ((minpoly ℚ (b k)).aroots ℂ) hnoduproots (fun w : ℂ => w ^ r)
  have hsum_toFinset : (∑ w ∈ ((minpoly ℚ (b k)).aroots ℂ).toFinset, w ^ r) = (q : ℂ) := by
    calc
      (∑ w ∈ ((minpoly ℚ (b k)).aroots ℂ).toFinset, w ^ r)
          = ∑ w : {y : ℂ // y ∈ (minpoly ℚ (b k)).aroots ℂ}, w.1 ^ r := by
              rw [Finset.sum_mem_multiset ((minpoly ℚ (b k)).aroots ℂ)
                (fun w : {y : ℂ // y ∈ (minpoly ℚ (b k)).aroots ℂ} => w.1 ^ r)
                (fun w : ℂ => w ^ r) (by intro x; rfl)]
      _ = (((minpoly ℚ (b k)).aroots ℂ).map (fun w : ℂ => w ^ r)).sum := hnodup_sub
      _ = (q : ℂ) := hms
  -- tie together
  have hmain : (∑ t ∈ C, (b t) ^ r) = (q : ℂ) := by
    rw [hsum_img, himg]
    exact hsum_toFinset
  exact ⟨q, hmain⟩


/-- `H̃ = ∏ₖ(y − bₖ) ∈ ℤ[y]` for a conjugate-closed family of pairwise
distinct algebraic integers. -/
lemma clearedH_mem_Z {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k)) (hinj : Function.Injective b)
    (hclosed : conjClosedFamily b) :
    ∃ P : ℤ[X], clearedH b = P.map (algebraMap ℤ ℂ) := by
  refine Commons.Polynomial.Prod.MonicProdConjClosed b hb hinj ?_
  intro k w hw
  have hbk : IsAlgebraic ℚ (b k) :=
    (isAlgebraic_iff_isIntegral).mpr (IsIntegral.tower_top (R := ℤ) (A := ℚ) (B := ℂ) (hb k))
  exact hclosed k w (conjRoots_of_aeval hbk hw)


/-! ## 12.  The symmetric step (foundation)

The symmetric step of Lemma A is the statement:

> **`∃ G ∈ ℚ[t]`, `∀ i, Jᵢ = G(bᵢ)`** — with `Jᵢ = −Σₖ βₖ·Σⱼ ℓʲ·f̃ᵢ⁽ʲ⁾(bₖ)`
> (the §8/§10 arithmetic object of `Σₖ βₖ·P(fᵢ,αₖ)` in the scaled
> variables), one fixed `G` for all indices `i`.

Its mechanism: `f̃ᵢ(y) = Cℓ·H̃(y)ᵖ/(y−bᵢ)` is the divided difference of the
*fixed* family polynomial `Q = Cℓ·H̃ᵖ` at `bᵢ`
(`scaledF_eq_polyDivDiff`, via `scaledF_mul_X_sub_C` = `(y−bᵢ)·f̃ᵢ = Cℓ·H̃ᵖ`
and `clearedH_pow_factor`), so expanding `polyDivDiff Q a = Σₘ gₘ(a)·yᵐ`
gives `gₘ ∈ (ℚ)[t]` *independent of* `i` (`H̃ ∈ ℤ[y]`, §11).  Each
derivative `f̃ᵢ⁽ʲ⁾(bₖ) = Σₘ gₘ(bᵢ)·(yᵐ)⁽ʲ⁾(bₖ)` is a polynomial in `bᵢ`
times monomials `bₖᵉ`, so the class sums `Σ_{k ∈ class} f̃ᵢ⁽ʲ⁾(bₖ)` become
polynomials in `bᵢ` with rational coefficients via the rational class power
sums `class_power_sum_rat` (§11); summing over the (β-constant) classes and
over `j` yields `Jᵢ = G(bᵢ)` for one `G ∈ ℚ[t]`.

This section currently contains the *foundation* of that argument (all
proved): the product splitting `clearedH_pow_factor`, the exact identity
`(y−bᵢ)·f̃ᵢ = Cℓ·H̃ᵖ` (`scaledF_mul_X_sub_C`), the divided-difference
representation `scaledF_eq_polyDivDiff`, and the **coefficient expansion**
`polyDivDiff_coeff_eq`:

`(polyDivDiff P a).coeff m = Σ_{n : m < n ≤ deg P} P.coeff n · a^{n−1−m}`,

so each coefficient of the quotient is an explicit polynomial in `a` whose
coefficients are those of `P`, and the derivative/factorial version
`polyDivDiff_deriv_coeff_eq` (via `coeff_iterate_derivative`):

`((polyDivDiff P a)⁽ʲ⁾).coeff m =
   (m+j).descFactorial j · Σ_{n : m+j < n ≤ deg P} P.coeff n · a^{n−1−m−j}`.

The class-glue part of the symmetric step (turn
`Σ_{k ∈ class} f̃ᵢ⁽ʲ⁾(bₖ)` into a rational polynomial in `bᵢ` via these two
expansion lemmas and `class_power_sum_rat`) is the next step.
-/

lemma clearedH_pow_factor {n : ℕ} (b : Fin n → ℂ) (p : ℕ) (i : Fin n) :
    (X - C (b i)) ^ p * scaledQ b p i = (clearedH b) ^ p := by
  dsimp [clearedH, scaledQ]
  have h := Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
    (fun t : Fin n => (X - C (b t)) ^ p) (Finset.mem_univ i)
  calc
    (X - C (b i)) ^ p * ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (b k)) ^ p
        = (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (b k)) ^ p) * (X - C (b i)) ^ p := by
            rw [mul_comm]
    _ = ∏ k : Fin n, (X - C (b k)) ^ p := h
    _ = (∏ k : Fin n, (X - C (b k))) ^ p := by rw [Finset.prod_pow]

-- (X − C(bᵢ))·f̃ᵢ = Cℓ·H̃ᵖ
lemma scaledF_mul_X_sub_C {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p) (i : Fin n) :
    (X - C (b i)) * scaledF b ℓ p i = C ℓ * (clearedH b) ^ p := by
  dsimp [scaledF]
  have hpp : (X - C (b i)) * (X - C (b i)) ^ (p - 1) = (X - C (b i)) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel]
    exact Nat.succ_le_of_lt hp
  calc
    (X - C (b i)) * (C ℓ * (X - C (b i)) ^ (p - 1) * scaledQ b p i)
        = C ℓ * ((X - C (b i)) * (X - C (b i)) ^ (p - 1)) * scaledQ b p i := by ring
    _ = C ℓ * (X - C (b i)) ^ p * scaledQ b p i := by rw [hpp]
    _ = C ℓ * ((X - C (b i)) ^ p * scaledQ b p i) := by ring
    _ = C ℓ * (clearedH b) ^ p := by rw [clearedH_pow_factor]

-- f̃ᵢ = polyDivDiff (Cℓ·H̃ᵖ) (bᵢ)
lemma scaledF_eq_polyDivDiff {n : ℕ} (b : Fin n → ℂ) (ℓ : ℂ) {p : ℕ} (hp : 0 < p) (i : Fin n) :
    scaledF b ℓ p i = polyDivDiff (C ℓ * (clearedH b) ^ p) (b i) := by
  let Q : ℂ[X] := C ℓ * (clearedH b) ^ p
  have hQ0 : Q.eval (b i) = 0 := by
    dsimp [Q]
    rw [Polynomial.eval_mul, Polynomial.eval_pow]
    -- clearedH(bᵢ) = 0
    have hH : (clearedH b).eval (b i) = 0 := by
      dsimp [clearedH]
      have hfac := Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
        (fun t : Fin n => X - C (b t)) (Finset.mem_univ i)
      rw [← hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      simp
    have hp0 : p ≠ 0 := Nat.ne_of_gt hp
    simp [hH, hp0]
  have h1 : Q = (X - C (b i)) * polyDivDiff Q (b i) := polyDivDiff_eq_of_root Q (b i) hQ0
  have h2 : (X - C (b i)) * scaledF b ℓ p i = Q := by
    dsimp [Q]
    exact scaledF_mul_X_sub_C b ℓ hp i
  have hXnz : X - C (b i) ≠ 0 := Polynomial.X_sub_C_ne_zero (b i)
  apply mul_left_cancel₀ hXnz
  rw [h2, h1]


/-- **Coefficient expansion of the divided difference.**  For
`polyDivDiff P a = Σ_{n ≤ deg P} C(Pₙ)·Σ_{i<n} Xⁱ·C(a^{n−1−i})` the
coefficient of `Xᵐ` is the polynomial in `a`

`(polyDivDiff P a).coeff m = Σ_{n : m < n ≤ deg P} Pₙ·a^{n−1−m}`.

So each coefficient of the quotient `(P − P(a))/(X−a)` is a polynomial in
`a` whose own coefficients are the coefficients of `P` — in particular, for
`P = Cℓ·H̃ᵖ` with `H̃ ∈ ℤ[y]`, the coefficients of `f̃ᵢ` are polynomials in
`bᵢ` with rational coefficients, *independent of* `i`. -/
lemma polyDivDiff_coeff_eq {R : Type*} [CommRing R] (P : R[X]) (a : R) (m : ℕ) :
    (polyDivDiff P a).coeff m =
      ∑ n ∈ (Finset.range (P.natDegree + 1)).filter (fun n : ℕ => m < n),
        P.coeff n * a ^ (n - 1 - m) := by
  classical
  have hinterm : ∀ n : ℕ,
      ((C (P.coeff n) * (∑ i ∈ Finset.range n, X ^ i * C (a ^ (n - 1 - i)))).coeff m) =
        P.coeff n * (if m < n then a ^ (n - 1 - m) else 0) := by
    intro n
    have hsum : (∑ i ∈ Finset.range n,
        ((X ^ i * C (a ^ (n - 1 - i))).coeff m)) =
        if m < n then a ^ (n - 1 - m) else 0 := by
      calc
        (∑ i ∈ Finset.range n, ((X ^ i * C (a ^ (n - 1 - i))).coeff m))
            = ∑ i ∈ Finset.range n, (if m = i then a ^ (n - 1 - i) else 0) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [mul_comm (X ^ i) (C (a ^ (n - 1 - i)))]
                rw [Polynomial.coeff_C_mul_X_pow]
        _ = if m ∈ Finset.range n then a ^ (n - 1 - m) else 0 := by
                rw [Finset.sum_ite_eq]
        _ = if m < n then a ^ (n - 1 - m) else 0 := by
                by_cases h : m < n
                · simp [h, Finset.mem_range]
                · simp [h, Finset.mem_range]
    calc
      (C (P.coeff n) * (∑ i ∈ Finset.range n, X ^ i * C (a ^ (n - 1 - i)))).coeff m
          = P.coeff n * (∑ i ∈ Finset.range n, ((X ^ i * C (a ^ (n - 1 - i))).coeff m)) := by
              rw [Polynomial.coeff_C_mul]
              rw [Polynomial.finsetSum_coeff]
      _ = P.coeff n * (if m < n then a ^ (n - 1 - m) else 0) := by rw [hsum]

  calc
    (polyDivDiff P a).coeff m
        = ∑ n ∈ Finset.range (P.natDegree + 1),
            ((C (P.coeff n) * (∑ i ∈ Finset.range n, X ^ i * C (a ^ (n - 1 - i)))).coeff m) := by
            dsimp [polyDivDiff]
            rw [Polynomial.finsetSum_coeff]
    _ = ∑ n ∈ Finset.range (P.natDegree + 1),
            P.coeff n * (if m < n then a ^ (n - 1 - m) else 0) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hinterm n
    _ = ∑ n ∈ (Finset.range (P.natDegree + 1)).filter (fun n : ℕ => m < n),
            P.coeff n * a ^ (n - 1 - m) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro n hn
            by_cases hmn : m < n
            · simp [hmn]
            · simp [hmn]


/-- **Derivative/factorial version of the coefficient expansion.**  The
`j`-th iterated derivative of the divided-difference quotient has
`Xᵐ`-coefficient

`((polyDivDiff P a)⁽ʲ⁾).coeff m = (m+j)!/(m)! · Σ_{n : m+j < n ≤ deg P} Pₙ·a^{n−1−m−j}`

with `(m+j).descFactorial j = (m+j)!/(m)!` the falling factorial.  (For
`P = Cℓ·H̃ᵖ` this is the rational polynomial in `bᵢ` that the symmetric step
sums over a class.) -/
lemma polyDivDiff_deriv_coeff_eq (P : ℂ[X]) (a : ℂ) (j m : ℕ) :
    (((derivative^[j]) (polyDivDiff P a)).coeff m) =
      ((m + j).descFactorial j : ℂ) *
        (∑ n ∈ (Finset.range (P.natDegree + 1)).filter (fun n : ℕ => m + j < n),
          P.coeff n * a ^ (n - 1 - (m + j))) := by
  have hc := Polynomial.coeff_iterate_derivative (k := j) (polyDivDiff P a) m
  rw [hc]
  rw [polyDivDiff_coeff_eq P a (m + j)]
  simp [nsmul_eq_mul]


/-- **Value form of the derivative expansion.**  Evaluating the `j`-th
derivative of the divided-difference quotient at `x`:

`(polyDivDiff Q a)⁽ʲ⁾(x) =
  Σ_{m} (m+j).descFactorial j · (Σ_{n : m+j<n} Qₙ·a^{n−1−m−j}) · xᵐ`.

With `Q = Cℓ·H̃ᵖ` and `a = bᵢ`, `x = bₖ` this is the term the symmetric
step substitutes into the class sum. -/
lemma polyDivDiff_deriv_eval_eq (Q : ℂ[X]) (a x : ℂ) (j : ℕ) :
    ((derivative^[j]) (polyDivDiff Q a)).eval x =
      ∑ m ∈ Finset.range ((((derivative^[j]) (polyDivDiff Q a)).natDegree) + 1),
        (((m + j).descFactorial j : ℂ) *
          (∑ n ∈ (Finset.range (Q.natDegree + 1)).filter (fun n : ℕ => m + j < n),
            Q.coeff n * a ^ (n - 1 - (m + j))) * x ^ m) := by
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m hm
  rw [polyDivDiff_deriv_coeff_eq Q a j m]


lemma polyDivDiff_natDegree_le {R : Type*} [CommRing R] (P : R[X]) (a : R) :
    (polyDivDiff P a).natDegree ≤ P.natDegree := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  -- coeff N = 0: use the coefficient formula: no n ≤ deg P satisfies N < n
  rw [polyDivDiff_coeff_eq P a N]
  have hf : ((Finset.range (P.natDegree + 1)).filter (fun n : ℕ => N < n)) = ∅ := by
    ext n
    constructor
    · intro hn
      have hn1 : n < P.natDegree + 1 :=
        Finset.mem_range.mp ((Finset.mem_filter.mp hn).1)
      have hnN : N < n := (Finset.mem_filter.mp hn).2
      omega
    · intro h
      simpa using h
  simp [hf]

/-- Uniformly bounded value form: evaluating the `j`-th derivative of the
divided-difference quotient at `x` with the `m`-sum over
`m < P.natDegree + 1` (terms beyond the true degree vanish). -/
lemma polyDivDiff_deriv_eval_bound (P : ℂ[X]) (a x : ℂ) (j : ℕ) :
    ((derivative^[j]) (polyDivDiff P a)).eval x =
      ∑ m ∈ Finset.range (P.natDegree + 1),
        (((m + j).descFactorial j : ℂ) *
          (∑ n ∈ (Finset.range (P.natDegree + 1)).filter (fun n : ℕ => m + j < n),
            P.coeff n * a ^ (n - 1 - (m + j))) * x ^ m) := by
  have hdeg : ((derivative^[j]) (polyDivDiff P a)).natDegree < P.natDegree + 1 := by
    have h1 : (polyDivDiff P a).natDegree ≤ P.natDegree := polyDivDiff_natDegree_le P a
    have h2 : ((derivative^[j]) (polyDivDiff P a)).natDegree ≤ (polyDivDiff P a).natDegree :=
      (Polynomial.natDegree_iterate_derivative (polyDivDiff P a) j).trans (Nat.sub_le _ _)
    omega
  rw [Polynomial.eval_eq_sum_range' hdeg x]
  apply Finset.sum_congr rfl
  intro m hm
  rw [polyDivDiff_deriv_coeff_eq P a j m]


/-! ## 13.  The symmetric-step substitution (class sum)

The first assembly step of the symmetric step (§12 roadmap): with
`f̃ᵢ = polyDivDiff Q (bᵢ)` (`Q = Cℓ₀·H̃ᵖ`, §12), the `β`-weighted sum over
all `k` of the `j`-th derivative values `f̃ᵢ⁽ʲ⁾(bₖ)` equals the `m`-sum of the
value-form coefficients (`polyDivDiff_deriv_eval_bound`, §12) times the
`β`-weighted power sums `Σₖ βₖ·(bₖ)ᵐ`:

`Σₖ βₖ·f̃ᵢ⁽ʲ⁾(bₖ) =
  Σₘ (m+j).descFactorial j · (Σₙ : m+j<n Qₙ·(bᵢ)^{n−1−m−j}) · (Σₖ βₖ·bₖᵐ)`

(`classSum_value_subst`; proof: rewrite each value by
`scaledF_eq_polyDivDiff` + the bounded value form, expand `βₖ·Σₘ` by
`mul_sum`, swap the two finite sums, and pull the `m`-factor out of the
`Σₖ` — pure `ac_rfl`/`sum_comm`/`mul_sum` bookkeeping).

With the `β`-weighted power sums rational (`betaPowerSum_rat`, the module
bridge of the Commons `WeightedPowerSumsConjClosed`) and the `Q`-coefficients
rational (`Q_coeff_rational`, `Q = Cℓ₀·H̃ᵖ` with `H̃ ∈ ℤ[y]`, §11), summing
`lemmaA_J_subst` over `j ∈ range(n·p+1)` with the `(ℓ₀:ℂ)ʲ` weights gives
`Jᵢ = G(bᵢ)` for one `G ∈ ℚ[t]` — the target `lemmaA_J_symmetric`
(statement in §12 docstring; assembly: replace each inner
`Σₖ βₖ·(bₖ)ᵐ` by its rational witness, identify each `Q.coeff n` via
`Q_coeff_rational`, and read off `G`; the falling-factorial and `(ℓ₀:ℚ)ʲ`
factors are rational casts; the finite sums are then pure bookkeeping).

**Gotcha (parser):** avoid the identifier `P̃` (a letter with a *combining*
tilde) — it silently breaks the parser; use a plain name such as `Pz` for
the `ℤ[X]` witness of `clearedH_mem_Z`.

**Assembly complete:** `lemmaA_J_symmetric` is proved and committed below.
The LHS-normalization is four `have`-steps: `hA1` (per-`(j,m)`
`rw [hB m]`, `ℓʲ` kept at the `j`-level via `congrArg`), `hA2` (expand to
the triple sum with `mul_sum`/`sum_mul` and per-`n0` `ac_rfl`), `hA3`
(per-`n0` `rw [hR n0]`), `hA4` (termwise cast match: `dsimp [coef, exp]`,
`norm_cast`, `simp`, `ring`).

**Payoff (`∏ᵢ Jᵢ ∈ ℚ`):** with `Jᵢ = G(bᵢ)` for one `G ∈ ℚ[t]`, the
product over the conjugate-closed family is rational: `evalProd_rat` (the
module bridge of the Commons `ProdEvalConjClosed`: `∏ₖ G(bₖ) ∈ ℚ`) and
`lemmaA_J_prod_rat` (`∏ᵢ Jᵢ = (q : ℂ)`) are proved and committed.  Together
with §10's `lemmaA_J_functional_ne_zero` (nonzero for suitable primes) and
the divisibility by `(p−1)!ⁿ` this yields the `|∏ᵢ Jᵢ| ≥ (p−1)!ⁿ` lower
bound — the next §13/§14 item, followed by the analytic upper bound.
-/

/-- **Class-sum substitution.**  With `f̃ᵢ = polyDivDiff Q (bᵢ)` (`Q =
Cℓ₀·H̃ᵖ`), the `β`-weighted sum over all `k` of `f̃ᵢ⁽ʲ⁾(bₖ)` is the `m`-sum
of the value-form coefficients times the `β`-weighted power sums
`Σₖ βₖ·(bₖ)ᵐ`:

`Σₖ βₖ·f̃ᵢ⁽ʲ⁾(bₖ) =
  Σₘ (m+j)!/(m)! · (Σₙ₊ : m+j<n Qₙ·(bᵢ)^{n−1−m−j}) · (Σₖ βₖ·bₖᵐ)`. -/
lemma classSum_value_subst {n : ℕ} (b : Fin n → ℂ) (ℓ₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (Q : ℂ[X]) (hQ : Q = C (ℓ₀ : ℂ) * (clearedH b) ^ p)
    (β : Fin n → ℤ) (i : Fin n) (j : ℕ) :
    let D : ℕ := Q.natDegree + 1
    (∑ k : Fin n, ((β k : ℤ) : ℂ) *
        ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k)) =
      ∑ m ∈ Finset.range D,
        (((m + j).descFactorial j : ℂ) *
          (∑ n ∈ (Finset.range D).filter (fun n : ℕ => m + j < n),
            Q.coeff n * (b i) ^ (n - 1 - (m + j)))) *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) * (b k) ^ m) := by
  classical
  let D : ℕ := Q.natDegree + 1
  -- per-k value: (deriv^j scaledF).eval(bₖ) = (deriv^j polyDivDiff Q (bᵢ)).eval (bₖ)
  have hval : ∀ k : Fin n,
      ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k) =
        ((derivative^[j]) (polyDivDiff Q (b i))).eval (b k) := by
    intro k
    have hs := scaledF_eq_polyDivDiff b (ℓ₀ : ℂ) hp i
    rw [← hQ] at hs
    rw [hs]
  -- expand each value via the uniformly-bounded value form
  have hvb : ∀ k : Fin n,
      ((derivative^[j]) (polyDivDiff Q (b i))).eval (b k) =
        ∑ m ∈ Finset.range D,
          (((m + j).descFactorial j : ℂ) *
            (∑ n ∈ (Finset.range D).filter (fun n : ℕ => m + j < n),
              Q.coeff n * (b i) ^ (n - 1 - (m + j)))) * (b k) ^ m := by
    intro k
    dsimp [D]
    -- polyDivDiff_deriv_eval_bound (P := Q) (a := b i) (x := b k) (j)
    rw [polyDivDiff_deriv_eval_bound Q (b i) (b k) j]
  calc
    (∑ k : Fin n, ((β k : ℤ) : ℂ) *
        ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k))
        = ∑ k : Fin n, ((β k : ℤ) : ℂ) *
            (∑ m ∈ Finset.range D,
              (((m + j).descFactorial j : ℂ) *
                (∑ n ∈ (Finset.range D).filter (fun n : ℕ => m + j < n),
                  Q.coeff n * (b i) ^ (n - 1 - (m + j)))) * (b k) ^ m) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hval, hvb]
    _ = ∑ k : Fin n, ∑ m ∈ Finset.range D,
            ((β k : ℤ) : ℂ) *
              (((m + j).descFactorial j : ℂ) *
                (∑ n ∈ (Finset.range D).filter (fun n : ℕ => m + j < n),
                  Q.coeff n * (b i) ^ (n - 1 - (m + j)))) * (b k) ^ m := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring
    _ = ∑ m ∈ Finset.range D,
            (((m + j).descFactorial j : ℂ) *
              (∑ n ∈ (Finset.range D).filter (fun n : ℕ => m + j < n),
                Q.coeff n * (b i) ^ (n - 1 - (m + j)))) *
              (∑ k : Fin n, ((β k : ℤ) : ℂ) * (b k) ^ m) := by
            -- swap the two finite sums
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro m hm
            calc
              (∑ k : Fin n, (((β k : ℤ) : ℂ) *
                  (((m + j).descFactorial j : ℂ) *
                    (∑ n ∈ (Finset.range D).filter (fun n : ℕ => m + j < n),
                      Q.coeff n * (b i) ^ (n - 1 - (m + j)))) * (b k) ^ m))
                  = (∑ k : Fin n, ((((m + j).descFactorial j : ℂ) *
                      (∑ n ∈ (Finset.range D).filter (fun n : ℕ => m + j < n),
                        Q.coeff n * (b i) ^ (n - 1 - (m + j)))) * (((β k : ℤ) : ℂ) * (b k) ^ m))) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      ac_rfl
              _ = (((m + j).descFactorial j : ℂ) *
                    (∑ n ∈ (Finset.range D).filter (fun n : ℕ => m + j < n),
                      Q.coeff n * (b i) ^ (n - 1 - (m + j)))) *
                  (∑ k : Fin n, ((β k : ℤ) : ℂ) * (b k) ^ m) := by
                      rw [← Finset.mul_sum]


/-- **The `j`-summed substitution (`Jᵢ` in expanded form).**  Summing
`classSum_value_subst` over `j ∈ range(n·p+1)` with the `(ℓ₀:ℂ)ʲ` weights
exhibits `Jᵢ = −Σₖ Σⱼ βₖ·ℓ₀ʲ·f̃ᵢ⁽ʲ⁾(bₖ)` with the inner `Σₖ βₖ·(bₖ)ᵐ`
standing alone in each term:

`Jᵢ = − Σⱼ ℓ₀ʲ · Σₘ (m+j).descFactorial j ·
        (Σₙ : m+j<n Qₙ·(bᵢ)^{n−1−m−j}) · (Σₖ βₖ·bₖᵐ)`. -/
lemma lemmaA_J_subst {n : ℕ} (b : Fin n → ℂ) (ℓ₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (Q : ℂ[X]) (hQ : Q = C (ℓ₀ : ℂ) * (clearedH b) ^ p)
    (β : Fin n → ℤ) (i : Fin n) :
    - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
        (∑ k : Fin n, ((β k : ℤ) : ℂ) *
          ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k))) =
    - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j * ∑ m ∈ Finset.range (Q.natDegree + 1),
        (((m + j).descFactorial j : ℂ) *
          (∑ n ∈ (Finset.range (Q.natDegree + 1)).filter (fun n : ℕ => m + j < n),
            Q.coeff n * (b i) ^ (n - 1 - (m + j)))) *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) * (b k) ^ m)) := by
  classical
  have hsubst : ∀ j : ℕ,
      (∑ k : Fin n, ((β k : ℤ) : ℂ) *
        ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k)) =
        ∑ m ∈ Finset.range (Q.natDegree + 1),
          (((m + j).descFactorial j : ℂ) *
            (∑ n ∈ (Finset.range (Q.natDegree + 1)).filter (fun n : ℕ => m + j < n),
              Q.coeff n * (b i) ^ (n - 1 - (m + j)))) *
            (∑ k : Fin n, ((β k : ℤ) : ℂ) * (b k) ^ m) := by
    intro j
    have hc := classSum_value_subst b ℓ₀ hp Q hQ β i j
    -- hc has the let-D form: reduce the let by change:
    dsimp at hc
    exact hc
  rw [neg_inj]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsubst j]


/-- **Rational `β`-weighted power sums (module form).**  For a
conjugate-closed pairwise-distinct family `b : Fin n → ℂ` of algebraic
integers and `β : Fin n → ℤ` constant on conjugacy classes, every
`β`-weighted power sum `Σₖ βₖ·(bₖ)ᵐ` is rational (bridge to the Commons
`WeightedPowerSumsConjClosed` through the `conjRoots`-formulation of closure
and of the class-constancy). -/
lemma betaPowerSum_rat {n : ℕ} (b : Fin n → ℂ) (β : Fin n → ℤ)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k))
    (hinj : Function.Injective b)
    (hclosed : conjClosedFamily b)
    (hβc : ∀ k t : Fin n, b t ∈ conjRoots (b k) → β k = β t)
    (m : ℕ) : ∃ q : ℚ, (∑ k : Fin n, ((β k : ℤ) : ℂ) * (b k) ^ m) = (q : ℂ) := by
  classical
  have hb_alg : ∀ k : Fin n, IsAlgebraic ℚ (b k) := fun k =>
    (isAlgebraic_iff_isIntegral).mpr (IsIntegral.tower_top (R := ℤ) (A := ℚ) (B := ℂ) (hb k))
  refine Commons.Polynomial.Prod.WeightedPowerSumsConjClosed b β hb hinj ?_ ?_ m
  · intro k w hw
    exact hclosed k w (conjRoots_of_aeval (hb_alg k) hw)
  · intro k t hw
    exact hβc k t (conjRoots_of_aeval (hb_alg k) hw)


/-- **Rational `Q`-coefficients.**  With `H̃ = Pz.map` for `Pz : ℤ[X]`
(`clearedH_mem_Z`), the coefficients of `Q = Cℓ₀·H̃ᵖ` are the rationals
`(ℓ₀:ℚ)·((Pzᵖ).coeff m : ℚ)`. -/
lemma Q_coeff_rational {n : ℕ} (b : Fin n → ℂ) (ℓ₀ : ℕ) (p : ℕ)
    (Pz : ℤ[X]) (hH : clearedH b = Pz.map (algebraMap ℤ ℂ)) (m : ℕ) :
    (((ℓ₀ : ℚ) * ((Pz ^ p).coeff m : ℚ)) : ℂ) =
      (C (ℓ₀ : ℂ) * (clearedH b) ^ p).coeff m := by
  rw [hH]
  rw [← Polynomial.map_pow]
  rw [Polynomial.coeff_C_mul]
  rw [Polynomial.coeff_map]
  norm_cast
  simp


/-- evaluating a finite sum of monomials `C (a i)·X^(e i)` at `x` -/
lemma eval_sum_C_mul_X_pow {ι R : Type*} [CommSemiring R] (s : Finset ι)
    (a : ι → R) (e : ι → ℕ) (x : R) :
    (∑ i ∈ s, C (a i) * X ^ e i).eval x = ∑ i ∈ s, a i * x ^ e i := by
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- mapping to ℂ and evaluating: `(Σᵢ C(aᵢ)·X^(eᵢ))` mapped by ℚ→ℂ, evaluated at `x` -/
lemma map_eval_sum_C_mul_X_pow {ι : Type*} (s : Finset ι)
    (a : ι → ℚ) (e : ι → ℕ) (x : ℂ) :
    ((∑ i ∈ s, C (a i) * X ^ e i).map (algebraMap ℚ ℂ)).eval x =
      ∑ i ∈ s, ((a i : ℚ) : ℂ) * x ^ e i := by
  rw [Polynomial.map_sum]
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [map_mul, map_pow]


/-- **The symmetric step: `Jᵢ = G(bᵢ)` for one `G ∈ ℚ[t]`.**

For a conjugate-closed, pairwise-distinct family `b : Fin n → ℂ` of
algebraic integers, a positive integer `ℓ₀`, and `β : Fin n → ℤ` constant on
conjugacy classes, there is a single `G ∈ ℚ[X]` such that for every index
`i`:

`Jᵢ := −Σₖ Σ_{j < n·p} (βₖ:ℂ)·(ℓ₀:ℂ)ʲ·f̃ᵢ⁽ʲ⁾(bₖ) = (G.map (algebraMap ℚ ℂ)).eval (b i)`

(one `G` for all `i`).  The proof chains the §13 machinery: `Pz` from
`clearedH_mem_Z`, `Q = Cℓ₀·H̃ᵖ` (§12), `lemmaA_J_subst` rewrites `Jᵢ` into
the `m`-sum with `β`-weighted power sums; `betaPowerSum_rat` witnesses each
`Σₖ βₖ·(bₖ)ᵐ` by a rational `B m`; `Q_coeff_rational` identifies each
`Q.coeff n` with the rational `R n`; `G` is assembled from these rationals
with the falling-factorial/`ℓ₀`-cast factors; and the monomial eval helpers
close the equality.  Together with `classSum_value_subst` this makes
`∏ᵢ Jᵢ ∈ ℚ` (via `norm_rat_poly` over the classes) the immediate next step
of Lemma A. -/
lemma lemmaA_J_symmetric {n : ℕ} (b : Fin n → ℂ) (ℓ₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k))
    (hinj : Function.Injective b)
    (hclosed : conjClosedFamily b)
    (β : Fin n → ℤ)
    (hβc : ∀ k t : Fin n, b t ∈ conjRoots (b k) → β k = β t) :
    ∃ G : ℚ[X], ∀ i : Fin n,
      - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k))) =
        (G.map (algebraMap ℚ ℂ)).eval (b i) := by
  classical
  obtain ⟨Pz, hPz⟩ := clearedH_mem_Z b hb hinj hclosed
  let Q : ℂ[X] := C (ℓ₀ : ℂ) * (clearedH b) ^ p
  have hQ : Q = C (ℓ₀ : ℂ) * (clearedH b) ^ p := rfl
  let B : ℕ → ℚ := fun m => Classical.choose (betaPowerSum_rat b β hb hinj hclosed hβc m)
  have hB : ∀ m : ℕ, (∑ k : Fin n, ((β k : ℤ) : ℂ) * (b k) ^ m) = (B m : ℂ) := by
    intro m
    exact (Classical.choose_spec (betaPowerSum_rat b β hb hinj hclosed hβc m))
  let R : ℕ → ℚ := fun n0 => (ℓ₀ : ℚ) * ((Pz ^ p).coeff n0 : ℚ)
  have hR : ∀ m : ℕ, (R m : ℂ) = Q.coeff m := by
    intro m
    dsimp [R, Q]
    simpa using (Q_coeff_rational b ℓ₀ p Pz hPz m)
  let D : ℕ := Q.natDegree + 1
  let coef : ℕ → ℕ → ℕ → ℚ := fun j m n0 =>
    ((ℓ₀ : ℚ) ^ j) * (((m + j).descFactorial j : ℚ)) * (R n0) * (B m)
  let exp : ℕ → ℕ → ℕ → ℕ := fun j m n0 => n0 - 1 - (m + j)
  let G : ℚ[X] := - (∑ j ∈ Finset.range (n * p + 1), ∑ m ∈ Finset.range D,
      ∑ n0 ∈ (Finset.range D).filter (fun n0 : ℕ => m + j < n0),
        C (coef j m n0) * X ^ exp j m n0)
  refine ⟨G, ?_⟩
  intro i
  rw [lemmaA_J_subst b ℓ₀ hp Q hQ β i]
  have hG : (G.map (algebraMap ℚ ℂ)).eval (b i) =
      - (∑ j ∈ Finset.range (n * p + 1), ∑ m ∈ Finset.range D,
          ∑ n0 ∈ (Finset.range D).filter (fun n0 : ℕ => m + j < n0),
            ((coef j m n0 : ℚ) : ℂ) * (b i) ^ exp j m n0) := by
    dsimp [G]
    rw [Polynomial.map_neg, Polynomial.eval_neg]
    congr 1
    rw [Polynomial.map_sum]
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.map_sum]
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Polynomial.map_sum]
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro n0 hn
    simp [exp, coef]
  rw [hG]
  rw [neg_inj]
  -- STEP 1: per (j,m) rewrite Σ_k via hB
  have hA1 :
      (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          ∑ m ∈ Finset.range (Q.natDegree + 1),
            (((m + j).descFactorial j : ℂ) *
              (∑ n0 ∈ (Finset.range (Q.natDegree + 1)).filter (fun n0 : ℕ => m + j < n0),
                Q.coeff n0 * (b i) ^ (n0 - 1 - (m + j)))) *
              (∑ k : Fin n, ((β k : ℤ) : ℂ) * (b k) ^ m))
        = ∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
            ∑ m ∈ Finset.range (Q.natDegree + 1),
              (((m + j).descFactorial j : ℂ) *
                (∑ n0 ∈ (Finset.range (Q.natDegree + 1)).filter (fun n0 : ℕ => m + j < n0),
                  Q.coeff n0 * (b i) ^ (n0 - 1 - (m + j)))) *
                (B m : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply congrArg (fun z : ℂ => (ℓ₀ : ℂ) ^ j * z) ?_
      apply Finset.sum_congr rfl
      intro m hm
      rw [hB m]
  rw [hA1]
  -- STEP 2: expand to the triple sum
  have hA2 :
      (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          ∑ m ∈ Finset.range (Q.natDegree + 1),
            (((m + j).descFactorial j : ℂ) *
              (∑ n0 ∈ (Finset.range (Q.natDegree + 1)).filter (fun n0 : ℕ => m + j < n0),
                Q.coeff n0 * (b i) ^ (n0 - 1 - (m + j)))) *
              (B m : ℂ))
        = ∑ j ∈ Finset.range (n * p + 1), ∑ m ∈ Finset.range (Q.natDegree + 1),
            ∑ n0 ∈ (Finset.range (Q.natDegree + 1)).filter (fun n0 : ℕ => m + j < n0),
              (ℓ₀ : ℂ) ^ j * (((m + j).descFactorial j : ℂ) *
                (Q.coeff n0 * (b i) ^ (n0 - 1 - (m + j)))) * (B m : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n0 hn
      ac_rfl
  rw [hA2]
  -- STEP 3: Q.coeff ↦ (R n0 : ℂ)
  have hA3 :
      (∑ j ∈ Finset.range (n * p + 1), ∑ m ∈ Finset.range (Q.natDegree + 1),
          ∑ n0 ∈ (Finset.range (Q.natDegree + 1)).filter (fun n0 : ℕ => m + j < n0),
            (ℓ₀ : ℂ) ^ j * (((m + j).descFactorial j : ℂ) *
              (Q.coeff n0 * (b i) ^ (n0 - 1 - (m + j)))) * (B m : ℂ))
        = ∑ j ∈ Finset.range (n * p + 1), ∑ m ∈ Finset.range (Q.natDegree + 1),
            ∑ n0 ∈ (Finset.range (Q.natDegree + 1)).filter (fun n0 : ℕ => m + j < n0),
              (ℓ₀ : ℂ) ^ j * (((m + j).descFactorial j : ℂ) *
                ((R n0 : ℂ) * (b i) ^ (n0 - 1 - (m + j)))) * (B m : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n0 hn
      rw [hR n0]
  rw [hA3]
  -- STEP 4: termwise cast match with coef/exp
  have hA4 :
      (∑ j ∈ Finset.range (n * p + 1), ∑ m ∈ Finset.range (Q.natDegree + 1),
          ∑ n0 ∈ (Finset.range (Q.natDegree + 1)).filter (fun n0 : ℕ => m + j < n0),
            (ℓ₀ : ℂ) ^ j * (((m + j).descFactorial j : ℂ) *
              ((R n0 : ℂ) * (b i) ^ (n0 - 1 - (m + j)))) * (B m : ℂ))
        = ∑ j ∈ Finset.range (n * p + 1), ∑ m ∈ Finset.range (Q.natDegree + 1),
            ∑ n0 ∈ (Finset.range (Q.natDegree + 1)).filter (fun n0 : ℕ => m + j < n0),
              ((coef j m n0 : ℚ) : ℂ) * (b i) ^ exp j m n0 := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n0 hn
      -- termwise: per-term goal (after dsimp/norm_cast) is the AC equality of the
      -- cast product with the monomial; the ℚ-product single-cast on the coef side
      -- must be expanded by map_mul and the ℕ/ℚ cast-chains normalized:
      dsimp [coef, exp]
      norm_cast
      simp [map_mul]
      ring
  rw [hA4]


/-- **Rational product of `G(bₖ)` (module form).**  For a conjugate-closed
pairwise-distinct family of algebraic integers and `G ∈ ℚ[X]`, the product
`∏ₖ G(bₖ)` is rational (bridge to the Commons `ProdEvalConjClosed`). -/
lemma evalProd_rat {n : ℕ} (b : Fin n → ℂ) (G : ℚ[X])
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k))
    (hinj : Function.Injective b)
    (hclosed : conjClosedFamily b) :
    ∃ q : ℚ, (∏ i : Fin n, (G.map (algebraMap ℚ ℂ)).eval (b i)) = (q : ℂ) := by
  classical
  refine Commons.Polynomial.Prod.ProdEvalConjClosed b G hb hinj ?_
  intro k w hw
  have hbk : IsAlgebraic ℚ (b k) :=
    (isAlgebraic_iff_isIntegral).mpr (IsIntegral.tower_top (R := ℤ) (A := ℚ) (B := ℂ) (hb k))
  exact hclosed k w (conjRoots_of_aeval hbk hw)

/-- **The product `∏ᵢ Jᵢ` is rational** — the symmetric step's payoff.  With
`Jᵢ = G(bᵢ)` for one `G ∈ ℚ[t]` (`lemmaA_J_symmetric`), the product over
the conjugate-closed family is rational (`evalProd_rat`). -/
lemma lemmaA_J_prod_rat {n : ℕ} (b : Fin n → ℂ) (ℓ₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k))
    (hinj : Function.Injective b)
    (hclosed : conjClosedFamily b)
    (β : Fin n → ℤ)
    (hβc : ∀ k t : Fin n, b t ∈ conjRoots (b k) → β k = β t) :
    ∃ q : ℚ,
      (∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k)))) = (q : ℂ) := by
  classical
  obtain ⟨G, hG⟩ := lemmaA_J_symmetric b ℓ₀ hp hb hinj hclosed β hβc
  obtain ⟨q, hq⟩ := evalProd_rat b G hb hinj hclosed
  refine ⟨q, ?_⟩
  calc
    (∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
        (∑ k : Fin n, ((β k : ℤ) : ℂ) *
          ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k))))
        = ∏ i : Fin n, (G.map (algebraMap ℚ ℂ)).eval (b i) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hG i
    _ = (q : ℂ) := hq


/-! ## 14.  The `(p−1)!ⁿ | ∏ᵢ Jᵢ` divisibility and the lower bound (plan)

With the symmetric step (§13: `Jᵢ = G(bᵢ)`, `G ∈ ℚ[t]`) and the product
rationality (`lemmaA_J_prod_rat`), the lower bound of Lemma A needs the
**divisibility**: each `Jᵢ` is a `(p−1)!`-multiple of an algebraic integer.
Per factor (in the α-representation `bₖ = ℓ₀·αₖ` of §8/§10):

```
lemmaA_J_divisible_rep (α) (ℓ₀) (hp : 0 < p)
    (hb : ∀ k, IsIntegral ℤ ((ℓ₀ : ℂ) * α k)) (β) (i) :
  ∃ T : ℂ, IsIntegral ℤ T ∧
    − Σ_{j<np} (ℓ₀:ℂ)ʲ · (Σₖ βₖ·(deriv^[j] (scaledF (fun k => (ℓ₀:ℂ)·α k) (ℓ₀:ℂ) p i)).eval ((ℓ₀:ℂ)·α k))
      = (p−1)! · T
```

and the product form `∏ᵢ Jᵢ = (p−1)!ⁿ·T`, `T ∈ ℤ̄`.

Proof route and missing facts (to be supplied in this section):
1. **(translation identity)** the b-world `Jᵢ` above equals the α-world
   `−Σₖ βₖ·F(αₖ)` (`F = sumIDeriv (lemmaA_f α (ℓ₀:ℂ) p i)`): swap the
   `j`- and `k`-sums and apply `sumIDeriv_lemmaA_f_eval_range` (§7);
2. **per-factor divisibility**: `lemmaA_J_shape α (ℓ₀:ℂ) hp
   (isIntegral_natCast_complex ℓ₀) hb β i` gives
   `Jᵢ = (p−1)!·(−βᵢ·ℓᵖ·δᵢᵖ − p·Sᵢ)` with `Sᵢ ∈ ℤ̄`; the witness
   `Tᵢ := −βᵢ·(ℓ₀:ℂ)ᵖ·∏_{t≠i}(ℓ₀αᵢ−ℓ₀αₜ)ᵖ − p·Sᵢ` is integral
   (`βᵢ` integer-cast, `ℓ₀` nat-cast, `∏(ℓ₀αᵢ−ℓ₀αₜ)ᵖ` a product of
   integrals by `hb` via `IsIntegral.sub/pow/prod`);
3. **(product)**: `∏ᵢ Jᵢ = (p−1)!ⁿ·∏ᵢ Tᵢ` with `∏ᵢ Tᵢ ∈ ℤ̄`
   (`IsIntegral.prod` over `Fin n`);
4. **(lower bound)**: with `lemmaA_J_prod_rat` (`∏ᵢ Jᵢ ∈ ℚ`), the quotient
   `∏ᵢ Jᵢ/(p−1)!ⁿ` is a rational algebraic integer, hence an integer
   (`Commons.RingTheory.IsIntegral.isInt_of_rat`), and — given
   `∏ᵢ Jᵢ ≠ 0` (each `Jᵢ ≠ 0` by §10 `lemmaA_J_functional_ne_zero` /
   `lemmaA_J_ne_zero_cleared` for primes `p ∤ c`) — `|∏ᵢ Jᵢ| ≥ (p−1)!ⁿ`.

**Completed:** step 1 `lemmaA_J_translation` (scaled `Jᵢ` equals
`−Σₖ βₖ·F(αₖ)`); step 2 `lemmaA_J_divisible_rep` (per factor
`Jᵢ = (p−1)!·Tᵢ`, `Tᵢ ∈ ℤ̄`, witness `−βᵢℓ₀ᵖ∏_{t≠i}(ℓ₀αᵢ−ℓ₀αₜ)ᵖ − p·Sᵢ` via
`lemmaA_J_shape` and the translation identity); step 3
`lemmaA_J_prod_divisible` (`∏ᵢ Jᵢ = (p−1)!ⁿ·T`, `T = ∏ᵢ Tᵢ ∈ ℤ̄`).

Remaining step 4 (lower bound): with `∏ᵢ Jᵢ ∈ ℚ`
(`lemmaA_J_prod_rat`) the quotient `∏ᵢ Jᵢ/(p−1)!ⁿ` is a rational algebraic
integer, hence an integer (`Commons.RingTheory.IsIntegral.isInt_of_rat`);
given `∏ᵢ Jᵢ ≠ 0` (each `Jᵢ ≠ 0` by §10 for primes `p ∤ c`), this yields
`|∏ᵢ Jᵢ| ≥ (p−1)!ⁿ` — to be assembled with `lemmaA_J_prod_rat`,
`lemmaA_J_prod_divisible`, `lemmaA_J_ne_zero_cleared`, and the ℚ/ℂ cast
facts, then the analytic upper bound `|∏ᵢ Jᵢ| ≤ C^(n·p)`.
-/

/-- **Translation identity (§14, step 1).**  With `bₖ = ℓ₀·αₖ` the scaled
world `Jᵢ = −Σⱼ ℓ₀ʲ·(Σₖ βₖ·f̃ᵢ⁽ʲ⁾(bₖ))` equals the α-world object
`−Σₖ βₖ·F(αₖ)` (`F = sumIDeriv (fᵢ)`), by swapping the finite sums and
applying the §7 translation `sumIDeriv_lemmaA_f_eval_range`. -/
lemma lemmaA_J_translation {n : ℕ} (α : Fin n → ℂ) (ℓ₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (β : Fin n → ℤ) (i : Fin n) :
    - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
        (∑ k : Fin n, ((β k : ℤ) : ℂ) *
          ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k))) =
    - (∑ k : Fin n, ((β k : ℤ) : ℂ) *
        (sumIDeriv (lemmaA_f α (ℓ₀ : ℂ) p i)).eval (α k)) := by
  rw [neg_inj]
  calc
    (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
        (∑ k : Fin n, ((β k : ℤ) : ℂ) *
          ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))
        = ∑ j ∈ Finset.range (n * p + 1), ∑ k : Fin n,
            (ℓ₀ : ℂ) ^ j * (((β k : ℤ) : ℂ) *
              ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ j ∈ Finset.range (n * p + 1),
            (ℓ₀ : ℂ) ^ j * (((β k : ℤ) : ℂ) *
              ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)) := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ((β k : ℤ) : ℂ) *
            (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
              ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            calc
              (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j * (((β k : ℤ) : ℂ) *
                  ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))
                  = ∑ j ∈ Finset.range (n * p + 1), ((β k : ℤ) : ℂ) * ((ℓ₀ : ℂ) ^ j *
                      ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ac_rfl
              _ = ((β k : ℤ) : ℂ) * (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
                      ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)) := by
                      rw [← Finset.mul_sum]
    _ = ∑ k : Fin n, ((β k : ℤ) : ℂ) *
            (sumIDeriv (lemmaA_f α (ℓ₀ : ℂ) p i)).eval (α k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [← sumIDeriv_lemmaA_f_eval_range α (ℓ₀ : ℂ) hp i k]


/-- **Per-factor divisibility (§14, step 2).**  Each scaled `Jᵢ` is
`(p−1)!`-times an algebraic integer: via the translation identity
(`lemmaA_J_translation`) the b-world object is `−Σₖ βₖ·F(αₖ)`, and
`lemmaA_J_shape` factors that as `(p−1)!·Tᵢ` with the explicit integral
witness `Tᵢ = −βᵢ·(ℓ₀:ℂ)ᵖ·∏_{t≠i}(ℓ₀αᵢ−ℓ₀αₜ)ᵖ − p·Sᵢ`. -/
lemma lemmaA_J_divisible_rep {n : ℕ} (α : Fin n → ℂ) (ℓ₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (hb : ∀ k : Fin n, IsIntegral ℤ ((ℓ₀ : ℂ) * α k))
    (β : Fin n → ℤ) (i : Fin n) :
    ∃ T : ℂ, IsIntegral ℤ T ∧
      - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k))) =
        ((p - 1).factorial : ℂ) * T := by
  classical
  obtain ⟨S, hSint, hshape⟩ :=
    lemmaA_J_shape α (ℓ₀ : ℂ) hp (isIntegral_natCast_complex ℓ₀) hb β i
  refine ⟨-(β i : ℂ) * ((ℓ₀ : ℂ) ^ p) *
      (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, ((ℓ₀ : ℂ) * α i - (ℓ₀ : ℂ) * α t) ^ p) -
    (p : ℂ) * S, ?_, ?_⟩
  · have hprod : IsIntegral ℤ
        (∏ t ∈ (Finset.univ : Finset (Fin n)).erase i, ((ℓ₀ : ℂ) * α i - (ℓ₀ : ℂ) * α t) ^ p) := by
      exact IsIntegral.prod (fun t => ((ℓ₀ : ℂ) * α i - (ℓ₀ : ℂ) * α t) ^ p) (by
        intro t ht
        exact IsIntegral.pow (IsIntegral.sub (hb i) (hb t)) p)
    exact IsIntegral.sub
      (IsIntegral.mul
        (IsIntegral.mul (IsIntegral.neg (isIntegral_intCast (β i)))
          (IsIntegral.pow (isIntegral_natCast_complex ℓ₀) p)) hprod)
      (IsIntegral.mul (isIntegral_natCast_complex p) hSint)
  · rw [lemmaA_J_translation α ℓ₀ hp β i]
    exact hshape


/-- **Product divisibility (§14, step 3).**  Multiplying the per-factor
identities of `lemmaA_J_divisible_rep` gives `∏ᵢ Jᵢ = (p−1)!ⁿ·T` with
`T = ∏ᵢ Tᵢ ∈ ℤ̄`. -/
lemma lemmaA_J_prod_divisible {n : ℕ} (α : Fin n → ℂ) (ℓ₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (hb : ∀ k : Fin n, IsIntegral ℤ ((ℓ₀ : ℂ) * α k))
    (β : Fin n → ℤ) :
    ∃ T : ℂ, IsIntegral ℤ T ∧
      (∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))) =
        (((p - 1).factorial : ℂ) ^ n) * T := by
  classical
  let T0 : Fin n → ℂ := fun i => Classical.choose (lemmaA_J_divisible_rep α ℓ₀ hp hb β i)
  have hspec : ∀ i : Fin n,
      IsIntegral ℤ (T0 i) ∧
        - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
            (∑ k : Fin n, ((β k : ℤ) : ℂ) *
              ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k))) =
          ((p - 1).factorial : ℂ) * T0 i := by
    intro i
    exact (Classical.choose_spec (lemmaA_J_divisible_rep α ℓ₀ hp hb β i))
  refine ⟨∏ i : Fin n, T0 i, ?_, ?_⟩
  · exact IsIntegral.prod T0 (by intro i hi; exact (hspec i).1)
  · calc
      (∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k))))
          = ∏ i : Fin n, (((p - 1).factorial : ℂ) * T0 i) := by
              apply Finset.prod_congr rfl
              intro i hi
              exact (hspec i).2
      _ = (((p - 1).factorial : ℂ) ^ n) * (∏ i : Fin n, T0 i) := by
              rw [Finset.prod_mul_distrib]
              rw [Finset.prod_const]
              simp


/-! ### 14b.  The lower bound `(p−1)!ⁿ ≤ |∏ᵢ Jᵢ|` (step 4 — completed)

Step 4 of §14 (lower bound) is now complete:

* `lemmaA_J_prod_quotient_int` — the `ℚ ∩ ℤ̄ = ℤ` descent in the form
  needed here: `z = (q : ℂ)` rational, `z = (p−1)!ⁿ·T`, `T ∈ ℤ̄`
  ⟹ `T = (zz : ℂ)` for an integer `zz`
  (bridge of `Commons.RingTheory.IsIntegral.isInt_of_rat`);
* `nat_le_norm_int_mul` — `(m : ℝ) ≤ ‖(m : ℂ)·(zz : ℂ)‖` for `m : ℕ`,
  integer `zz ≠ 0` (the norm side of the divisibility);
* `lemmaA_J_prod_lower` — the product lower bound: for a cleared,
  conjugate-closed, pairwise-distinct exponent family with *nonzero*
  class-constant integer coefficients, there is a fixed integer `C ≠ 0`
  such that for every prime `p ∤ C`:

  `(p−1)!ⁿ ≤ ‖∏ᵢ Jᵢ‖`   (`Jᵢ = −Σⱼ ℓ₀ʲ·Σₖ βₖ·f̃ᵢ⁽ʲ⁾(bₖ)`, the §8/§10 object),
  assembling `lemmaA_J_ne_zero_cleared` (per-index `cᵢ`; `Jᵢ ≠ 0` for
  primes `p ∤ cᵢ`, transferred to the scaled form by
  `lemmaA_J_translation`), `lemmaA_J_prod_rat` (`∏Jᵢ ∈ ℚ`),
  `lemmaA_J_prod_divisible` (`∏Jᵢ = (p−1)!ⁿ·T`, `T ∈ ℤ̄`), the quotient
  descent, and the integer-norm bound.

**The arithmetic side of Lemma A is thereby complete.**  The remaining
milestones (per `Lindemann.lean` §11): the *analytic* side
(`|Jᵢ| ≤ Cᵖ` uniformly — the Hermite `P`-machinery applied to the family
`fᵢ`, exactly as `P_auxPoly_bound` in `Lindemann.lean` §5b), the prime
selection (`(p−1)!ⁿ > C^(n·p)` eventually), the Lemma A contradiction, the
class structure reduction (`β` constant on `conjRoots`-classes + relation
⟹ all `β = 0`), then Lemma B and the `Transcendental ℚ (cexp z)`
corollaries.  Note the lower-bound lemma requires *all* coefficients
nonzero; the reduction to the support subfamily (dropping the classes with
coefficient 0) happens when Lemma A is applied.
-/

/-- `(q : ℂ) / (m : ℂ) = (q / (m : ℚ) : ℂ)` — the `ℕ→ℚ→ℂ` cast chain of a
denominator collapses to the single `ℕ→ℂ` cast. -/
lemma rat_div_nat_cast (q : ℚ) (m : ℕ) : (q : ℂ) / (m : ℂ) = (q / (m : ℚ) : ℂ) := by
  rw [← Rat.cast_div]
  norm_num

/-- **Quotient is an integer (§14, step 4a).**  If `z = (q : ℂ)` is
rational and `z = (p−1)!ⁿ·T` with `T` an algebraic integer, then
`T = (zz : ℂ)` for an integer `zz` — the `ℚ ∩ ℤ̄ = ℤ` descent
(`Commons.RingTheory.IsIntegral.isInt_of_rat`). -/
lemma lemmaA_J_prod_quotient_int {n : ℕ} (p : ℕ) {z : ℂ} {q : ℚ}
    (hq : z = (q : ℂ)) {T : ℂ} (hTint : IsIntegral ℤ T)
    (hT : z = (((p - 1).factorial : ℂ) ^ n) * T) :
    ∃ zz : ℤ, (zz : ℂ) = T := by
  have hfac0 : ((p - 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (p - 1))
  have hfac0n : (((p - 1).factorial : ℂ) ^ n) ≠ 0 := pow_ne_zero n hfac0
  let m : ℕ := (p - 1).factorial ^ n
  have hTq : T = ((q : ℚ) / (m : ℚ) : ℂ) := by
    calc
      T = z / (((p - 1).factorial : ℂ) ^ n) := by
            calc
              T = (((p - 1).factorial : ℂ) ^ n * T) / (((p - 1).factorial : ℂ) ^ n) := by
                    field_simp [hfac0n]
              _ = z / (((p - 1).factorial : ℂ) ^ n) := by rw [hT]
      _ = (q : ℂ) / (((p - 1).factorial : ℂ) ^ n) := by rw [hq]
      _ = (q : ℂ) / (m : ℂ) := by
            rw [← Nat.cast_pow]
      _ = (q / (m : ℚ) : ℂ) := rat_div_nat_cast q m
  exact (Commons.RingTheory.IsIntegral.isInt_of_rat
    (by
      refine ⟨q / (m : ℚ), ?_⟩
      rw [Rat.cast_div]
      exact hTq.symm)
    hTint)

/-- `(m : ℝ) ≤ ‖(m : ℂ) * (zz : ℂ)‖` for `m : ℕ` and an integer `zz ≠ 0`:
the norm side of the divisibility lower bound. -/
lemma nat_le_norm_int_mul (m : ℕ) (zz : ℤ) (hzz : zz ≠ 0) (x : ℂ) (hx : x = (m : ℂ) * (zz : ℂ)) :
    (m : ℝ) ≤ ‖x‖ := by
  rw [hx]
  have hnz : (1 : ℝ) ≤ ‖(zz : ℂ)‖ := by
    rw [Complex.norm_intCast]
    have hzR : (1 : ℝ) ≤ |(zz : ℝ)| := by
      rw [← Int.cast_abs (R := ℝ)]
      rw [Int.abs_eq_natAbs]
      have h1 : (1 : ℕ) ≤ zz.natAbs := by
        have : 0 < zz.natAbs := Int.natAbs_pos.mpr hzz
        omega
      exact_mod_cast h1
    exact hzR
  calc
    (m : ℝ) = (m : ℝ) * 1 := by ring
    _ ≤ (m : ℝ) * ‖(zz : ℂ)‖ := by
          exact mul_le_mul_of_nonneg_left hnz (by exact_mod_cast (Nat.zero_le m))
    _ = ‖(m : ℂ) * (zz : ℂ)‖ := by
          rw [norm_mul]
          rw [Complex.norm_natCast]

/-- **The `(p−1)!ⁿ ≤ |∏ᵢ Jᵢ|` lower bound (§14, step 4).**  For a cleared
exponent family `α : Fin n → ℂ` (`ℓ₀·αₖ` algebraic integers), pairwise
distinct after clearing, conjugate-closed, with nonzero class-constant
integer coefficients `β`, there is a fixed integer `C ≠ 0` such that for
every prime `p ∤ C` the product of the `Jᵢ`'s (the §8/§10 objects, in the
scaled form of `lemmaA_J_prod_rat`/`lemmaA_J_prod_divisible`) satisfies
`(p−1)!ⁿ ≤ ‖∏ᵢ Jᵢ‖`. -/
lemma lemmaA_J_prod_lower {n : ℕ} (α : Fin n → ℂ) (ℓ₀ : ℕ) (hℓ0 : ℓ₀ ≠ 0)
    (hb : ∀ k : Fin n, IsIntegral ℤ ((ℓ₀ : ℂ) * α k))
    (β : Fin n → ℤ) (hβnz : ∀ k : Fin n, β k ≠ 0)
    (hinj : Function.Injective (fun k : Fin n => (ℓ₀ : ℂ) * α k))
    (hclosed : conjClosedFamily (fun k : Fin n => (ℓ₀ : ℂ) * α k))
    (hβc : ∀ k t : Fin n, (ℓ₀ : ℂ) * α t ∈ conjRoots ((ℓ₀ : ℂ) * α k) → β k = β t) :
    ∃ C : ℤ, C ≠ 0 ∧ ∀ p : ℕ, Nat.Prime p → ¬ (p : ℤ) ∣ C →
      (((p - 1).factorial ^ n : ℕ) : ℝ) ≤
        ‖∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
            (∑ k : Fin n, ((β k : ℤ) : ℂ) *
              ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))‖ := by
  classical
  let b : Fin n → ℂ := fun k => (ℓ₀ : ℂ) * α k
  have hJc : ∀ i : Fin n, ∃ c : ℤ, c ≠ 0 ∧ ∀ p : ℕ, Nat.Prime p → ¬ (p : ℤ) ∣ c →
      - (∑ k : Fin n, (β k : ℂ) * (sumIDeriv (lemmaA_f α (ℓ₀ : ℂ) p i)).eval (α k)) ≠ 0 := by
    intro i
    exact lemmaA_J_ne_zero_cleared α ℓ₀ hℓ0 hb β i (hβnz i) hinj
  let c : Fin n → ℤ := fun i => Classical.choose (hJc i)
  let C : ℤ := ∏ i : Fin n, c i
  have hC0 : C ≠ 0 := by
    dsimp [C]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact (Classical.choose_spec (hJc i)).1)
  refine ⟨C, hC0, ?_⟩
  intro p hp hpnd
  have hp0 : 0 < p := Nat.Prime.pos hp
  have hSJnz : ∀ i : Fin n,
      - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k))) ≠ 0 := by
    intro i
    have hnot : ¬ (p : ℤ) ∣ c i := by
      intro hpd
      have hcd : c i ∣ C := by
        dsimp [C]
        exact Finset.dvd_prod_of_mem (fun j : Fin n => c j) (Finset.mem_univ i)
      apply hpnd
      exact dvd_trans hpd hcd
    have hJ : - (∑ k : Fin n, (β k : ℂ) * (sumIDeriv (lemmaA_f α (ℓ₀ : ℂ) p i)).eval (α k)) ≠ 0 :=
      (Classical.choose_spec (hJc i)).2 p hp hnot
    have htr := lemmaA_J_translation α ℓ₀ hp0 β i
    have hSJ : - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k))) ≠ 0 := by
      rw [htr]
      exact hJ
    simpa [b] using hSJ
  have hprod0 : (∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
      (∑ k : Fin n, ((β k : ℤ) : ℂ) *
        ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k)))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact hSJnz i
  obtain ⟨q, hq⟩ := lemmaA_J_prod_rat b ℓ₀ hp0 hb hinj hclosed β hβc
  obtain ⟨T, hTint, hT⟩ := lemmaA_J_prod_divisible α ℓ₀ hp0 hb β
  let z : ℂ := (∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
      (∑ k : Fin n, ((β k : ℤ) : ℂ) *
        ((derivative^[j]) (scaledF b (ℓ₀ : ℂ) p i)).eval (b k))))
  have hq' : z = (q : ℂ) := by
    dsimp [z]
    simpa [b] using hq
  have hT' : z = (((p - 1).factorial : ℂ) ^ n) * T := by
    dsimp [z]
    simpa [b] using hT
  obtain ⟨zz, hzz⟩ := lemmaA_J_prod_quotient_int p hq' hTint hT'
  have hzz0 : zz ≠ 0 := by
    intro hz0
    have hz0' : z = 0 := by
      calc
        z = (((p - 1).factorial : ℂ) ^ n) * T := hT'
        _ = (((p - 1).factorial : ℂ) ^ n) * (zz : ℂ) := by rw [hzz]
        _ = 0 := by rw [hz0]; simp
    exact hprod0 (by simpa [z, b] using hz0')
  let m : ℕ := (p - 1).factorial ^ n
  have hm : (m : ℂ) = ((p - 1).factorial : ℂ) ^ n := by
    dsimp [m]
    rw [Nat.cast_pow]
  have hx : z = (m : ℂ) * (zz : ℂ) := by
    calc
      z = (((p - 1).factorial : ℂ) ^ n) * T := hT'
      _ = (((p - 1).factorial : ℂ) ^ n) * (zz : ℂ) := by rw [hzz]
      _ = (m : ℂ) * (zz : ℂ) := by rw [hm]
  have hbound : (m : ℝ) ≤ ‖z‖ := nat_le_norm_int_mul m zz hzz0 z hx
  dsimp [z] at hbound
  simpa [m, b] using hbound


/-! ## 15.  The analytic side: uniform `|Jᵢ| ≤ Cᵖ` bounds

The upper bound of Lemma A (Wikipedia): with all `‖αₖ‖ ≤ M`, the family
polynomials `fᵢ,p = lemmaA_f α (ℓ₀:ℂ) p i` satisfy, for every segment point
`y` with `‖y‖ ≤ M`, the uniform bound `‖fᵢ,p(y)‖ ≤ c₀ᵖ`
(`lemmaA_f_eval_norm_bound`, `c₀ = ((ℓ₀·A)ⁿ·A)`, `A = max (2M) 1`), so by
the Hermite analytic bound (`P_le_explicit`, `Hermite.lean §1`) each
`‖P(fᵢ,p)(αₖ)‖ ≤ C₁ᵖ` uniformly in `i,k`, and summing over `k`:

`lemmaA_P_uniform`: `∃ C ≥ 0`, `∀ i, p ≠ 0: ‖Σₖ βₖ·P(fᵢ,p)(αₖ)‖ ≤ Cᵖ`.

**Completed in this section:** `norm_sub_pow_le`, `ge_one_mul`,
`lemmaA_f_eval_norm_bound`, `lemmaA_P_uniform` (all proved).

Still to do (§16): the product upper bound `‖∏ᵢ Jᵢ‖ ≤ Dᵖ` (via the
relation `Jᵢ = Σₖ βₖ·P(fᵢ)` under `hrel`), and the Lemma A contradiction
(lower bound of §14b vs upper bound of §16, prime selection via
`pow_div_factorial_pred_eventually_lt`).
-/

lemma norm_sub_pow_le (x a : ℂ) {A : ℝ} (h : ‖x - a‖ ≤ A) (q : ℕ) : ‖(x - a) ^ q‖ ≤ A ^ q := by
  calc ‖(x - a) ^ q‖ = ‖x - a‖ ^ q := by rw [norm_pow]
       _ ≤ A ^ q := pow_le_pow_left₀ (norm_nonneg _) h q


lemma lemmaA_f_eval_norm_bound {n : ℕ} (α : Fin n → ℂ) (ℓ₀ : ℕ) (p : ℕ) (i : Fin n)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ k : Fin n, ‖α k‖ ≤ M) {y : ℂ} (hy : ‖y‖ ≤ M) :
    ‖(lemmaA_f α (ℓ₀ : ℂ) p i).eval y‖ ≤ (((((ℓ₀ : ℝ) * max (2 * M) 1) ^ n) * max (2 * M) 1) ^ p) := by
  classical
  let A : ℝ := max (2 * M) 1
  have hA1 : 1 ≤ A := le_max_of_le_right (le_rfl)
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hfac : ∀ t : Fin n, ‖y - α t‖ ≤ A := by
    intro t
    calc ‖y - α t‖ ≤ ‖y‖ + ‖α t‖ := norm_sub_le y (α t)
         _ ≤ M + M := add_le_add hy (hM t)
         _ = 2 * M := by ring
         _ ≤ A := by dsimp [A]; exact le_max_left (2 * M) 1
  have hpow_i : ‖(y - α i) ^ (p - 1)‖ ≤ A ^ p := by
    exact le_trans (norm_sub_pow_le y (α i) (hfac i) (p - 1))
      (pow_le_pow_right₀ hA1 (Nat.sub_le p 1))
  have hprod_le : ‖∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (y - α k) ^ p‖ ≤ A ^ (n * p) := by
    calc
      ‖∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (y - α k) ^ p‖
          = ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ‖(y - α k) ^ p‖ := by
              rw [norm_prod]
      _ = ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ‖y - α k‖ ^ p := by
              apply Finset.prod_congr rfl
              intro k hk
              rw [norm_pow]
      _ ≤ ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, A ^ p := by
              apply Finset.prod_le_prod₀
              · intro k hk; exact pow_nonneg (norm_nonneg _) p
              · intro k hk; exact pow_le_pow_left₀ (norm_nonneg _) (hfac k) p
      _ ≤ ∏ k : Fin n, A ^ p := by
              have hsplit := Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
                (fun k : Fin n => A ^ p) (Finset.mem_univ i)
              rw [← hsplit]
              exact le_mul_of_one_le_right
                (Finset.prod_nonneg (by intro k hk; exact pow_nonneg hA0 p))
                (one_le_pow₀ hA1)
      _ = A ^ (n * p) := by
              rw [Finset.prod_const]
              rw [← pow_mul]
              congr 1
              rw [mul_comm]
              simp
  have hℓnorm : ‖(ℓ₀ : ℂ) ^ (n * p)‖ = (ℓ₀ : ℝ) ^ (n * p) := by
    rw [norm_pow, Complex.norm_natCast]
  calc
    ‖(lemmaA_f α (ℓ₀ : ℂ) p i).eval y‖
        = ‖(ℓ₀ : ℂ) ^ (n * p)‖ * ‖(y - α i) ^ (p - 1)‖ *
            ‖∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (y - α k) ^ p‖ := by
            rw [show (lemmaA_f α (ℓ₀ : ℂ) p i).eval y =
                (ℓ₀ : ℂ) ^ (n * p) * ((y - α i) ^ (p - 1) *
                  (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (y - α k) ^ p)) by
              unfold lemmaA_f
              rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
                  Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod]
              simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
              ring]
            rw [norm_mul, norm_mul]
            ring
    _ ≤ ((ℓ₀ : ℝ) ^ (n * p)) * (A ^ p * A ^ (n * p)) := by
            rw [hℓnorm]
            have h1 : ‖(y - α i) ^ (p - 1)‖ * ‖∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (y - α k) ^ p‖ ≤
                A ^ p * A ^ (n * p) := by
              apply mul_le_mul hpow_i hprod_le
              · exact norm_nonneg _
              · exact pow_nonneg hA0 p
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (by positivity) (n * p))
    _ = (((ℓ₀ : ℝ) ^ (n * p)) * A ^ (n * p)) * A ^ p := by ring
    _ = (((ℓ₀ : ℝ) * A) ^ (n * p)) * A ^ p := by rw [mul_pow]
    _ = ((((ℓ₀ : ℝ) * A) ^ n) ^ p) * A ^ p := by
            rw [← pow_mul]
    _ = ((((ℓ₀ : ℝ) * A) ^ n) * A) ^ p := by rw [← mul_pow]
    _ = (((((ℓ₀ : ℝ) * max (2 * M) 1) ^ n) * max (2 * M) 1) ^ p) := by
            dsimp [A]


lemma ge_one_mul {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ x * y := by
  calc 1 ≤ x := hx
       _ ≤ x * y := le_mul_of_one_le_right (le_trans zero_le_one hx) hy


lemma lemmaA_P_uniform {n : ℕ} (α : Fin n → ℂ) (ℓ₀ : ℕ) (β : Fin n → ℤ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ k : Fin n, ‖α k‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin n) (p : ℕ), p ≠ 0 →
      ‖∑ k : Fin n, ((β k : ℤ) : ℂ) * P (lemmaA_f α (ℓ₀ : ℂ) p i) (α k)‖ ≤ C ^ p := by
  classical
  let A : ℝ := max (2 * M) 1
  let c0 : ℝ := (((ℓ₀ : ℝ) * A) ^ n) * A
  let EM : ℝ := max (Real.exp M) 1
  let SM : ℝ := max M 1
  let D0 : ℝ := max c0 1
  let C1 : ℝ := EM * (EM * D0 * SM)
  let Bsum : ℝ := ∑ k : Fin n, ‖((β k : ℤ) : ℂ)‖
  let C : ℝ := max 1 Bsum * C1
  have hc00 : 0 ≤ c0 := by dsimp [c0, A]; positivity
  have hEM1 : 1 ≤ EM := by dsimp [EM]; exact le_max_of_le_right (le_rfl)
  have hSM1 : 1 ≤ SM := by dsimp [SM]; exact le_max_of_le_right (le_rfl)
  have hD01 : 1 ≤ D0 := by dsimp [D0]; exact le_max_of_le_right (le_rfl)
  have hEM0 : 0 ≤ EM := le_trans zero_le_one hEM1
  have hSM0 : 0 ≤ SM := le_trans zero_le_one hSM1
  have hD00 : 0 ≤ D0 := le_trans zero_le_one hD01
  have hED1 : 1 ≤ EM * D0 * SM := by
    calc 1 ≤ EM * D0 := ge_one_mul hEM1 hD01
         _ ≤ (EM * D0) * SM := by exact le_mul_of_one_le_right (le_trans zero_le_one (ge_one_mul hEM1 hD01)) hSM1
         _ = EM * D0 * SM := by ring
  have hC11 : 1 ≤ C1 := by
    dsimp [C1]
    exact ge_one_mul hEM1 hED1
  have hC10 : 0 ≤ C1 := le_trans zero_le_one hC11
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) hC10
  have hP : ∀ (i : Fin n) (k : Fin n) (p : ℕ), p ≠ 0 →
      ‖P (lemmaA_f α (ℓ₀ : ℂ) p i) (α k)‖ ≤ C1 ^ p := by
    intro i k p hp0
    have hpt : ∀ q : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1,
        ‖(lemmaA_f α (ℓ₀ : ℂ) q i).eval (x • (α k))‖ ≤ c0 ^ q := by
      intro q x hx
      have hxk : ‖x • (α k)‖ ≤ M := by
        have hx0 : 0 ≤ x := hx.1.le
        have hx1 : x ≤ 1 := hx.2
        calc ‖x • (α k)‖ = x * ‖α k‖ := norm_smul_of_nonneg hx0 (α k)
             _ ≤ ‖α k‖ := by
                   exact (mul_le_mul_of_nonneg_right hx1 (norm_nonneg (α k))).trans (by rw [one_mul])
             _ ≤ M := hM k
      have hb := lemmaA_f_eval_norm_bound α ℓ₀ q i M hM0 hM hxk
      simpa [c0, A] using hb
    have hb0 := P_le_explicit (f := fun q : ℕ => lemmaA_f α (ℓ₀ : ℂ) q i) (s := α k) (c := c0) hpt p
    have hsM : ‖α k‖ ≤ M := hM k
    have hre : (α k).re ≤ M := le_trans (Complex.re_le_norm (α k)) hsM
    have hE1 : Real.exp (α k).re ≤ EM := by dsimp [EM]; exact le_max_of_le_left (Real.exp_le_exp.mpr hre)
    have hE2 : Real.exp ‖α k‖ ≤ EM := by dsimp [EM]; exact le_max_of_le_left (Real.exp_le_exp.mpr hsM)
    have hS : ‖α k‖ ≤ SM := by dsimp [SM]; exact le_max_of_le_left hsM
    have hD : |c0| ≤ D0 := by
      rw [abs_of_nonneg hc00]
      dsimp [D0]
      exact le_max_left c0 1
    have hDp : |c0| ^ p ≤ D0 ^ p := pow_le_pow_left₀ (abs_nonneg c0) hD p
    have hEpos : 0 ≤ Real.exp ‖α k‖ := (Real.exp_pos _).le
    have hT : Real.exp ‖α k‖ * |c0| ^ p * ‖α k‖ ≤ EM * D0 ^ p * SM := by
      calc
        Real.exp ‖α k‖ * |c0| ^ p * ‖α k‖
            ≤ (Real.exp ‖α k‖ * D0 ^ p) * ‖α k‖ := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hDp hEpos) (norm_nonneg _)
        _ ≤ (Real.exp ‖α k‖ * D0 ^ p) * SM := by
                exact mul_le_mul_of_nonneg_left hS (mul_nonneg hEpos (pow_nonneg hD00 p))
        _ ≤ (EM * D0 ^ p) * SM := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hE2 (pow_nonneg hD00 p)) hSM0
        _ = EM * D0 ^ p * SM := by ring
    have hT0 : 0 ≤ Real.exp ‖α k‖ * |c0| ^ p * ‖α k‖ := by
      exact mul_nonneg (mul_nonneg hEpos (pow_nonneg (abs_nonneg c0) p)) (norm_nonneg _)
    have hmain1 : Real.exp (α k).re * (Real.exp ‖α k‖ * |c0| ^ p * ‖α k‖) ≤ EM * (EM * D0 ^ p * SM) := by
      calc
        Real.exp (α k).re * (Real.exp ‖α k‖ * |c0| ^ p * ‖α k‖)
            ≤ EM * (Real.exp ‖α k‖ * |c0| ^ p * ‖α k‖) := by
                exact mul_le_mul_of_nonneg_right hE1 hT0
        _ ≤ EM * (EM * D0 ^ p * SM) := by
                exact mul_le_mul_of_nonneg_left hT hEM0
    have hG1 : 1 ≤ EM * EM * SM := by
      exact ge_one_mul (ge_one_mul hEM1 hEM1) hSM1
    have hGp : EM * EM * SM ≤ (EM * EM * SM) ^ p := le_self_pow₀ hG1 hp0
    have hstep : (EM * EM * SM) * D0 ^ p ≤ (EM * EM * SM) ^ p * D0 ^ p := by
      exact mul_le_mul_of_nonneg_right hGp (pow_nonneg hD00 p)
    have hmain2 : EM * (EM * D0 ^ p * SM) ≤ C1 ^ p := by
      dsimp [C1]
      calc
        EM * (EM * D0 ^ p * SM) = (EM * EM * SM) * D0 ^ p := by ring
        _ ≤ (EM * EM * SM) ^ p * D0 ^ p := hstep
        _ = (EM * (EM * D0 * SM)) ^ p := by
              rw [← mul_pow]
              ring
    calc
      ‖P (lemmaA_f α (ℓ₀ : ℂ) p i) (α k)‖
          ≤ Real.exp (α k).re * (Real.exp ‖α k‖ * |c0| ^ p * ‖α k‖) := hb0
      _ ≤ EM * (EM * D0 ^ p * SM) := hmain1
      _ ≤ C1 ^ p := hmain2
  refine ⟨C, hC0, ?_⟩
  intro i p hp0
  calc
    ‖∑ k : Fin n, ((β k : ℤ) : ℂ) * P (lemmaA_f α (ℓ₀ : ℂ) p i) (α k)‖
        ≤ ∑ k : Fin n, ‖((β k : ℤ) : ℂ) * P (lemmaA_f α (ℓ₀ : ℂ) p i) (α k)‖ := by
            simpa using (norm_sum_le (Finset.univ : Finset (Fin n))
              (fun k : Fin n => ((β k : ℤ) : ℂ) * P (lemmaA_f α (ℓ₀ : ℂ) p i) (α k)))
    _ = ∑ k : Fin n, ‖((β k : ℤ) : ℂ)‖ * ‖P (lemmaA_f α (ℓ₀ : ℂ) p i) (α k)‖ := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [norm_mul]
    _ ≤ ∑ k : Fin n, ‖((β k : ℤ) : ℂ)‖ * C1 ^ p := by
            apply Finset.sum_le_sum
            intro k hk
            exact mul_le_mul_of_nonneg_left (hP i k p hp0) (norm_nonneg _)
    _ = Bsum * C1 ^ p := by
            dsimp [Bsum]
            rw [Finset.sum_mul]
    _ ≤ C ^ p := by
            have hB1 : Bsum ≤ max 1 Bsum := le_max_right _ _
            have hBpow : max 1 Bsum ≤ (max 1 Bsum) ^ p :=
              le_self_pow₀ (le_max_left 1 Bsum) hp0
            dsimp [C]
            calc
              Bsum * C1 ^ p ≤ (max 1 Bsum) * C1 ^ p := by
                    exact mul_le_mul_of_nonneg_right hB1 (pow_nonneg hC10 p)
              _ ≤ (max 1 Bsum) ^ p * C1 ^ p := by
                    exact mul_le_mul_of_nonneg_right hBpow (pow_nonneg hC10 p)
              _ = ((max 1 Bsum) * C1) ^ p := by rw [← mul_pow]



/-! ### 16.  The Lemma A contradiction (product upper bound + prime selection)

The analytic side (§15) bounds each `Jᵢ = Σₖ βₖ·P(fᵢ)(αₖ) ≤ Cᵖ`; under the
exponential relation `hrel`, `Jᵢ` equals the scaled arithmetic object of
§14 (`lemmaA_J_translation` + `lemmaA_J_eq`), so the product `∏ᵢ Jᵢ`
satisfies `‖∏ᵢ Jᵢ‖ ≤ Dᵖ` uniformly (`lemmaA_J_prod_upper`).

**Lemma A (orbit relations — contradiction form)**: for a cleared exponent
family (`ℓ₀·αₖ` algebraic integers), pairwise distinct after clearing,
conjugate-closed, with *nonzero* integer coefficients constant on
`conjRoots`-classes and `Σₖ βₖ·e^{αₖ} = 0`, contradiction
(`lemmaA_orbit_contradiction`): the §14b lower bound gives a fixed
`C₁ ≠ 0` with `(p−1)!ⁿ ≤ ‖∏ᵢ Jᵢ‖` for every prime `p ∤ C₁`, while the upper
bound gives `‖∏ᵢ Jᵢ‖ ≤ Dᵖ`; choosing a prime `p > C₁.natAbs` large enough
that `Dᵖ < (p−1)!` (`pow_div_factorial_pred_eventually_lt`,
`Nat.exists_infinite_primes`) makes `(p−1)!ⁿ ≤ Dᵖ < (p−1)!ⁿ`
(`n ≥ 1`, `(p−1)! ≥ 1`) — contradiction.  (`natPrime_not_dvd_int_of_lt`
is the prime-avoidance input to the lower bound.)

The *reduction* of the general Lemma A statement (relation with
class-constant coefficients, some nonzero ⟹ all zero) to this contradiction
form — dropping the zero-coefficient classes and re-indexing the remaining
conjugate-closed subfamily — is the §17 step (Lemma B / Lindemann
applications).
-/

/-- A prime exceeding `|C|` cannot divide the nonzero integer `C`. -/
lemma natPrime_not_dvd_int_of_lt {p : ℕ} (hp : Nat.Prime p) {C : ℤ} (hC0 : C ≠ 0)
    (hlt : C.natAbs < p) : ¬ (p : ℤ) ∣ C := by
  intro h
  rcases h with ⟨k, hk⟩
  have hk0 : k ≠ 0 := by
    intro hk0
    subst k
    apply hC0
    simpa using hk
  have h2 : ((p : ℤ) * k).natAbs = p * k.natAbs := by
    rw [Int.natAbs_mul]
    rw [Int.natAbs_natCast]
  have hk1 : 1 ≤ k.natAbs := by
    have : 0 < k.natAbs := Int.natAbs_pos.mpr hk0
    omega
  have : p ≤ C.natAbs := by
    calc p ≤ ((p : ℤ) * k).natAbs := by
               rw [h2]
               nlinarith
         _ = C.natAbs := by rw [hk]
  omega

/-- **Product upper bound (§16).**  Under the exponential relation, the
product of the scaled `Jᵢ`'s satisfies `‖∏ᵢ Jᵢ‖ ≤ Dᵖ` uniformly: each
`Jᵢ` equals `Σₖ βₖ·P(fᵢ)(αₖ)` (relation + translation) and `lemmaA_P_uniform`
bounds those by `Cᵖ`; `D := (max 1 C)ⁿ`. -/
lemma lemmaA_J_prod_upper {n : ℕ} (α : Fin n → ℂ) (ℓ₀ : ℕ) (β : Fin n → ℤ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ k : Fin n, ‖α k‖ ≤ M)
    (hrel : (∑ k : Fin n, (β k : ℂ) * cexp (α k)) = 0) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p : ℕ, p ≠ 0 →
      ‖∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))‖ ≤ D ^ p := by
  classical
  obtain ⟨C, hC0, hC⟩ := lemmaA_P_uniform α ℓ₀ β M hM0 hM
  let Cu : ℝ := max 1 C
  have hCu1 : 1 ≤ Cu := le_max_left 1 C
  have hCu0 : 0 ≤ Cu := le_trans zero_le_one hCu1
  have hCle : C ≤ Cu := by
    dsimp [Cu]
    exact le_max_right 1 C
  let D : ℝ := Cu ^ n
  have hD1 : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ hCu1
  refine ⟨D, hD1, ?_⟩
  intro p hp0
  have hp0p : 0 < p := Nat.pos_of_ne_zero hp0
  have hSJ : ∀ i : Fin n,
      - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k))) =
        (∑ k : Fin n, ((β k : ℤ) : ℂ) * P (lemmaA_f α (ℓ₀ : ℂ) p i) (α k)) := by
    intro i
    have htr := lemmaA_J_translation α ℓ₀ hp0p β i
    have heq := lemmaA_J_eq α (ℓ₀ : ℂ) (p := p) i β hrel
    exact htr.trans heq.symm
  calc
    ‖∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))‖
        = ∏ i : Fin n, ‖- (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
            (∑ k : Fin n, ((β k : ℤ) : ℂ) *
              ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))‖ := by
            simpa using (norm_prod (Finset.univ : Finset (Fin n))
              (fun i : Fin n => - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
                (∑ k : Fin n, ((β k : ℤ) : ℂ) *
                  ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))))
    _ ≤ ∏ i : Fin n, Cu ^ p := by
            apply Finset.prod_le_prod₀
            · intro i hi
              positivity
            · intro i hi
              have h1 : ‖- (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
                    (∑ k : Fin n, ((β k : ℤ) : ℂ) *
                      ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))‖
                    ≤ C ^ p := by
                  calc
                    ‖- (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
                          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
                            ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))‖
                        = ‖∑ k : Fin n, ((β k : ℤ) : ℂ) * P (lemmaA_f α (ℓ₀ : ℂ) p i) (α k)‖ := by
                            exact congrArg norm (hSJ i)
                    _ ≤ C ^ p := hC i p hp0
              exact h1.trans (pow_le_pow_left₀ hC0 hCle p)
    _ = (Cu ^ p) ^ n := by
            rw [Finset.prod_const]
            simp
    _ = Cu ^ (n * p) := by
            rw [← pow_mul]
            congr 1
            rw [mul_comm]
    _ = (Cu ^ n) ^ p := by rw [pow_mul]
    _ = D ^ p := by
            dsimp [D]

/-- **Lemma A (contradiction form).**  For a cleared exponent family
(`ℓ₀·αₖ` algebraic integers), pairwise distinct after clearing,
conjugate-closed, with nonzero integer coefficients constant on
`conjRoots`-classes, the exponential relation `Σₖ βₖ·e^{αₖ} = 0` is
impossible.  (Requires `0 < n`: the family is nonempty.) -/
lemma lemmaA_orbit_contradiction {n : ℕ} (hn : 0 < n) (α : Fin n → ℂ) (ℓ₀ : ℕ) (hℓ0 : ℓ₀ ≠ 0)
    (hb : ∀ k : Fin n, IsIntegral ℤ ((ℓ₀ : ℂ) * α k))
    (β : Fin n → ℤ) (hβnz : ∀ k : Fin n, β k ≠ 0)
    (hinj : Function.Injective (fun k : Fin n => (ℓ₀ : ℂ) * α k))
    (hclosed : conjClosedFamily (fun k : Fin n => (ℓ₀ : ℂ) * α k))
    (hβc : ∀ k t : Fin n, (ℓ₀ : ℂ) * α t ∈ conjRoots ((ℓ₀ : ℂ) * α k) → β k = β t)
    (hrel : (∑ k : Fin n, (β k : ℂ) * cexp (α k)) = 0) : False := by
  classical
  let M : ℝ := ∑ k : Fin n, ‖α k‖
  have hM0 : 0 ≤ M := by
    dsimp [M]
    simpa using (Finset.sum_nonneg (s := (Finset.univ : Finset (Fin n))) (f := fun t : Fin n => ‖α t‖)
      (by intro t ht; exact norm_nonneg _))
  have hM : ∀ k : Fin n, ‖α k‖ ≤ M := by
    intro k
    dsimp [M]
    simpa using (Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun t : Fin n => ‖α t‖) (a := k)
      (by intro t ht; exact norm_nonneg _) (Finset.mem_univ k))
  obtain ⟨C1, hC10, hlow⟩ := lemmaA_J_prod_lower α ℓ₀ hℓ0 hb β hβnz hinj hclosed hβc
  obtain ⟨D, hD1, hup⟩ := lemmaA_J_prod_upper α ℓ₀ β M hM0 hM hrel
  obtain ⟨P0, hP0⟩ := Filter.mem_atTop_sets.mp (pow_div_factorial_pred_eventually_lt D)
  let Cbig : ℕ := max P0 (C1.natAbs + 1)
  obtain ⟨p, hpC, hpp⟩ := Nat.exists_infinite_primes Cbig
  have hpP0 : P0 ≤ p := by
    dsimp [Cbig] at hpC
    omega
  have hDfac : D ^ p / ((p - 1).factorial : ℝ) < 1 := hP0 p hpP0
  have hpabs : C1.natAbs < p := by
    dsimp [Cbig] at hpC
    omega
  have hnd : ¬ (p : ℤ) ∣ C1 := natPrime_not_dvd_int_of_lt hpp hC10 hpabs
  have hfac_pos : 0 < ((p - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_pos (p - 1))
  have hfac_ge1 : 1 ≤ ((p - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (p - 1)))
  have hDltfac : D ^ p < ((p - 1).factorial : ℝ) := by
    have h1 : D ^ p < 1 * ((p - 1).factorial : ℝ) := by
      exact (div_lt_iff₀ hfac_pos).1 hDfac
    simpa using h1
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hfacn_ge : ((p - 1).factorial : ℝ) ≤ ((p - 1).factorial : ℝ) ^ n :=
    le_self_pow₀ hfac_ge1 hn0
  have hlow_p : ((((p - 1).factorial ^ n : ℕ) : ℝ)) ≤
        ‖∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
            (∑ k : Fin n, ((β k : ℤ) : ℂ) *
              ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))‖ :=
    hlow p hpp hnd
  have hup_p : ‖∏ i : Fin n, - (∑ j ∈ Finset.range (n * p + 1), (ℓ₀ : ℂ) ^ j *
          (∑ k : Fin n, ((β k : ℤ) : ℂ) *
            ((derivative^[j]) (scaledF (fun k : Fin n => (ℓ₀ : ℂ) * α k) (ℓ₀ : ℂ) p i)).eval ((ℓ₀ : ℂ) * α k)))‖ ≤ D ^ p :=
    hup p hpp.ne_zero
  have h1 : ((((p - 1).factorial ^ n : ℕ) : ℝ)) ≤ D ^ p := le_trans hlow_p hup_p
  have h2 : D ^ p < ((((p - 1).factorial ^ n : ℕ) : ℝ)) := by
    rw [Nat.cast_pow]
    exact lt_of_lt_of_le hDltfac hfacn_ge
  exact (not_lt_of_ge h1) h2

end Submission.Transcendence
