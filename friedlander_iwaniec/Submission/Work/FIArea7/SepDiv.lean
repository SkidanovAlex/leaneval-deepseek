/-
# `Submission.Work.FIArea7.SepDiv` — the *FI* §24 separation divisor vocabulary

Friedlander–Iwaniec §24 (Lemma 24.1, Proposition 24.2, identity (24.13)) split a sum over
squarefree numbers `ℓ ⩽ x` into a double sum over `m, n ⩽ √x` and a *small* "separation"
divisor `d ⩽ D`.  Fix `r ⩾ 2` and enumerate the prime factors of `ℓ` in decreasing order,
`ℓ = p₁p₂…p_k` with `p₁ > p₂ > … > p_k`.  Then (24.2), (24.4), (24.5) define

  `d = (p₁…p_r)(p_{2r}p_{3r}…)`,   `m = (p_{r+1}…p_{2r-1})(p_{3r+1}…p_{4r-1})…`,
  `n = (p_{2r+1}…p_{3r-1})(p_{4r+1}…p_{5r-1})…`,

and `ℓ = dmn`.  The three index sets are interleaved blocks: writing `j = i + 1` (1-based
position in the decreasing list) and `j = q r + s` with `0 ≤ s < r`,

* `d` keeps `s = 0`, `q ⩾ 2`, and the whole first block `j ⩽ r` (`q = 0`, or `q = 1, s = 0`);
* `m` keeps `1 ≤ s ≤ r-1` with `q` odd (`q = 1, 3, 5, …`);
* `n` keeps `1 ≤ s ≤ r-1` with `q` even and `q ⩾ 2` (`q = 2, 4, …`).

This file only *sets up the vocabulary*; the theorems about it are proved elsewhere.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

/-- A strictly decreasing list of primes of length `k` whose product is `l`.  (Such a list is
unique when it exists, so this really is "the" decreasing enumeration of the prime factors.) -/
def IsPrimeList (l k : ℕ) (p : Fin k → ℕ) : Prop :=
  StrictAnti p ∧ (∀ i, (p i).Prime) ∧ l = ∏ i, p i

/-- The positions (0-based) of the primes of the *separation divisor* `d` in the decreasing
enumeration: `1 ⩽ j ⩽ r` or `j = 2r, 3r, 4r, …` (1-based `j = i + 1`). -/
def dIdx (r k : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k => i.val < r ∨ ((i.val + 1) % r = 0 ∧ 2 * r ≤ i.val + 1))

/-- The positions (0-based) of the primes of `m` (FI (24.4)): `j = q r + s` with `1 ≤ s ≤ r-1`
and `q` odd. -/
def mIdx (r k : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k => 0 < (i.val + 1) % r ∧ ((i.val + 1) / r) % 2 = 1)

/-- The positions (0-based) of the primes of `n` (FI (24.5)): `j = q r + s` with `1 ≤ s ≤ r-1`
and `q` even, `q ⩾ 2`. -/
def nIdx (r k : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k =>
    0 < (i.val + 1) % r ∧ ((i.val + 1) / r) % 2 = 0 ∧ 0 < (i.val + 1) / r)

/-- **The separation triple of *FI* §24.**  `(d, m, n)` is obtained from the decreasing
enumeration `p` of the prime factors of `l = d·m·n` by the interleaved block pattern (24.2),
(24.4), (24.5). -/
def IsSepPair (r d m n : ℕ) : Prop :=
  ∃ (k : ℕ) (p : Fin k → ℕ), IsPrimeList (d * m * n) k p ∧
    d = ∏ i ∈ dIdx r k, p i ∧ m = ∏ i ∈ mIdx r k, p i ∧ n = ∏ i ∈ nIdx r k, p i

/-- **The separation divisor of `l`** (FI (24.2)): `d` is the `d`-component of the separation
triple of `l`. -/
def IsSepDiv (r l d : ℕ) : Prop := ∃ m n, IsSepPair r d m n ∧ d * m * n = l

noncomputable section

open Classical

/-- The left-hand side of *FI* (24.11): the sum of `f` over squarefree `ℓ ⩽ x` all of whose
prime factors are `⩽ z` (i.e. `ℓ ∣ P(z)`). -/
def sepSumLHS (x z : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ l ∈ (Finset.Icc 1 x).filter (fun l => Squarefree l ∧ ∀ p, p.Prime → p ∣ l → p ≤ z), f l

/-- The right-hand side of *FI* (24.11): the double sum over `m, n ⩽ x` of the separation-triple
terms `f(d·m·n)`, restricted to triples whose product is again `∣ P(z)`. -/
def sepPairSum (r D x z : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D, ∑ m ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
    (if IsSepPair r d m n ∧ (∀ p, p.Prime → p ∣ d * m * n → p ≤ z) then f (d * m * n) else 0)


/-- The sum over *all* squarefree `ℓ ⩽ X` — the left-hand side of *FI* (24.12). -/
def sqfreeSum (X : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ l ∈ (Finset.Icc 1 X).filter (fun l => Squarefree l), f l

/-- The inner sum of *FI* (24.12): for a prime `p > z`, the sum over `q` with `pq` squarefree and
`pq ⩽ X`, weighted by the inverse of `ν(pq,z) = #{r prime : z < r, r ∣ pq}`. -/
def peelInner (X z : ℕ) (f : ℕ → ℂ) (p : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 X,
    (if Squarefree (p * q) ∧ p * q ≤ X then
      f (p * q) / ((((Finset.Icc 1 X).filter
        (fun r => r.Prime ∧ z < r ∧ r ∣ p * q)).card : ℕ) : ℂ)
     else 0)

/-- The prime sum of the right-hand side of *FI* (24.12). -/
def peelSum (X z : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ z < p), peelInner X z f p

end

end Work.FIArea7
