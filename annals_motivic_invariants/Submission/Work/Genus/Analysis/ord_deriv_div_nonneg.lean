import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.ord_pow
import Submission.Work.Genus.Order.ord_div_rat
import Submission.Work.Genus.Order.ord_C_mul
import Submission.Work.Genus.Order.min_ord_le_ord_add
import Submission.Work.Genus.Order.ord_add_eq_of_lt
import Submission.Work.Genus.Order.ord_aeval_of_neg
import Submission.Work.Genus.Order.ord_aeval_nonneg
import Submission.Work.Genus.Order.ord_deriv_ge
import Submission.Work.Genus.Order.ord_deriv_nonneg
import Submission.Work.Genus.Deriv.deriv_aeval
import Submission.Work.Genus.Deriv.deriv_mul
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Regularity of the pulled-back invariant differential at a finite place of `ℙ¹`

The genus / Riemann–Hurwitz chapter attaches to a Weierstrass curve `E : v² = A(u)` (here `A` is a
squarefree cubic) the invariant differential `ω = du / v`, whose pullback along a hypothetical
non-constant `x : ℙ¹ → E` is the rational differential `(x' / w) dt` on `ℙ¹ = RatFunc F`, where
`w` is the `v`-coordinate of the image of the generic point (`A(x) = w²`).

This file proves that this pullback has **no pole at any finite place**: for every irreducible
`π ∈ F[X]`, `0 ≤ ord π (deriv x / w)`.  Together with the companion statement at infinity
(`Work.Genus.Analysis.two_le_ordInf_deriv_div`, `2 ≤ ordInf (deriv x / w)`) it shows that
`(x'/w) dt` is a regular differential with a zero of order at least `2` at infinity — which forces
`x` to be constant, since a non-zero rational differential on `ℙ¹` has divisor of degree `-2`.

The proof splits on the place of `x` (`Work.Genus.Order.ord_aeval_of_neg`, `ord_deriv_ge`,
`ord_div_rat` in the pole case) and, when `x` is regular at `π` and `w` vanishes there, uses the
Bézout relation `u * A + v * A' = 1` from `IsCoprime A A'` to bound `ord π (A'(x)) ≤ 0`; the chain
rule `A'(x) * x' = 2 * w * w'` then transfers this bound to `deriv x`.
-/

namespace Work.Genus.Analysis

open Polynomial

private theorem deriv_zero_ratFunc {F : Type*} [Field F] : Work.Genus.deriv (0 : RatFunc F) = 0 := by
  simp [Work.Genus.deriv]

private theorem ord_two_mul_deriv {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {π : Polynomial F}
    (hπ : Irreducible π) {w : RatFunc F} (hw : w ≠ 0) (hdw : Work.Genus.deriv w ≠ 0) :
    Work.Genus.ord π (2 * w * Work.Genus.deriv w)
      = Work.Genus.ord π w + Work.Genus.ord π (Work.Genus.deriv w) := by
  have hcast : (2 : RatFunc F) * w * Work.Genus.deriv w
      = algebraMap F (RatFunc F) (2 : F) * (w * Work.Genus.deriv w) := by
    have h2c : (2 : RatFunc F) = algebraMap F (RatFunc F) (2 : F) :=
      (map_ofNat (algebraMap F (RatFunc F)) 2).symm
    rw [h2c]; ring
  rw [hcast, Work.Genus.Order.ord_C_mul h2 (w * Work.Genus.deriv w),
    Work.Genus.Order.ord_mul hπ hw hdw]

/-- **The Bézout consequence at a place where `x` is regular and `w` vanishes.**
From `IsCoprime A A'` take `u * A + v * A' = 1` and evaluate at `x`: with `A(x) = w²` this is
`u(x) * w² + v(x) * A'(x) = 1`.  Since `ord π (u(x)) ≥ 0` and `ord π (w²) = 2 * ord π w > 0`
(`ord_aeval_nonneg`, `ord_pow`), the summand `u(x) * w²` has strictly positive order; the
non-archimedean inequality (`min_ord_le_ord_add`) then bounds `ord π (v(x) * A'(x)) ≤ 0`, and
`ord π (v(x)) ≥ 0` gives `ord π (A'(x)) ≤ 0`.  Finally `A'(x) = 0` is impossible: it would force
`u(x) * w² = 1`, an element of order `0` but with order `≥ 2 * ord π w > 0`.

(The same statement is available as the standalone lemma
`Work.Genus.Analysis.aeval_derivative_ne_zero_and_ord_nonpos`; it is kept private here so that
this module stays self-contained.) -/
private theorem aeval_derivative_ne_zero_and_ord_nonpos_aux {F : Type*} [Field F] {A : Polynomial F}
    (hsq : IsCoprime A (Polynomial.derivative A)) {x w : RatFunc F} (hw : w ≠ 0)
    (heq : Polynomial.aeval x A = w ^ 2) {π : Polynomial F} (hπ : Irreducible π)
    (hx : 0 ≤ Work.Genus.ord π x) (he : 0 < Work.Genus.ord π w) :
    Polynomial.aeval x (Polynomial.derivative A) ≠ 0 ∧
      Work.Genus.ord π (Polynomial.aeval x (Polynomial.derivative A)) ≤ 0 := by
  obtain ⟨u, v, huv⟩ := hsq
  have hbez : Polynomial.aeval x u * w ^ 2
      + Polynomial.aeval x v * Polynomial.aeval x (Polynomial.derivative A) = 1 := by
    have h := congrArg (Polynomial.aeval x) huv
    simpa [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_one, heq] using h
  set U := Polynomial.aeval x u with hU
  set V := Polynomial.aeval x v with hV
  set B := Polynomial.aeval x (Polynomial.derivative A) with hB
  have hUnn : 0 ≤ Work.Genus.ord π U := Work.Genus.Order.ord_aeval_nonneg hπ hx
  have hVnn : 0 ≤ Work.Genus.ord π V := Work.Genus.Order.ord_aeval_nonneg hπ hx
  have hw2 : Work.Genus.ord π (w ^ 2) = 2 * Work.Genus.ord π w := by
    rw [Work.Genus.Order.ord_pow hπ hw 2]; norm_num
  have hw2pos : 0 < Work.Genus.ord π (w ^ 2) := by rw [hw2]; linarith
  have h1 : Work.Genus.ord π 1 = 0 := Work.Genus.Order.ord_one π
  rcases eq_or_ne U 0 with hU0 | hUne
  · have hVB : V * B = 1 := by rw [hU0, zero_mul, zero_add] at hbez; exact hbez
    have hVne : V ≠ 0 := fun h => one_ne_zero (by rw [← hVB, h, zero_mul])
    have hBne : B ≠ 0 := fun h => one_ne_zero (by rw [← hVB, h, mul_zero])
    refine ⟨hBne, ?_⟩
    have hord : Work.Genus.ord π (V * B) = Work.Genus.ord π V + Work.Genus.ord π B :=
      Work.Genus.Order.ord_mul hπ hVne hBne
    rw [hVB, h1] at hord
    omega
  · have hUw2 : Work.Genus.ord π (U * w ^ 2) = Work.Genus.ord π U + Work.Genus.ord π (w ^ 2) :=
      Work.Genus.Order.ord_mul hπ hUne (pow_ne_zero 2 hw)
    have hUw2pos : 0 < Work.Genus.ord π (U * w ^ 2) := by rw [hUw2]; linarith
    have hUw2ne : U * w ^ 2 ≠ 0 := mul_ne_zero hUne (pow_ne_zero 2 hw)
    constructor
    · intro hB0
      have hcontra : U * w ^ 2 = 1 := by rw [hB0, mul_zero, add_zero] at hbez; exact hbez
      have : Work.Genus.ord π (U * w ^ 2) = 0 := by rw [hcontra, h1]
      omega
    · by_contra hcon
      push Not at hcon
      have hBne : B ≠ 0 := fun h => by
        have hcontra : U * w ^ 2 = 1 := by rw [h, mul_zero, add_zero] at hbez; exact hbez
        have : Work.Genus.ord π (U * w ^ 2) = 0 := by rw [hcontra, h1]
        omega
      have hVne : V ≠ 0 := fun h => by
        have hcontra : U * w ^ 2 = 1 := by rw [h, zero_mul, add_zero] at hbez; exact hbez
        have : Work.Genus.ord π (U * w ^ 2) = 0 := by rw [hcontra, h1]
        omega
      have hVBpos : 0 < Work.Genus.ord π (V * B) := by
        rw [Work.Genus.Order.ord_mul hπ hVne hBne]; linarith
      have hsumne : U * w ^ 2 + V * B ≠ 0 := by rw [hbez]; exact one_ne_zero
      have hmin := Work.Genus.Order.min_ord_le_ord_add (π := π) hπ hUw2ne
        (mul_ne_zero hVne hBne) hsumne
      rw [hbez, h1] at hmin
      have : 0 < min (Work.Genus.ord π (U * w ^ 2)) (Work.Genus.ord π (V * B)) :=
        lt_min hUw2pos hVBpos
      omega

/-- **The pole case.**  If `x` has a pole of order `-m > 0` at the place of `π`, then
`ord π (A(x)) = 3 * ord π x` (`ord_aeval_of_neg`, `A.natDegree = 3`) while `ord π (A(x)) = 2 * e`
with `e = ord π w` (`ord_pow`), so `2 * e = 3 * ord π x` is negative; combining `ord_deriv_ge`
(`ord π (deriv x) ≥ ord π x - 1`) with `ord_div_rat` and `2 * (ord π (deriv x) - e) ≥ m - 2 ≥ 0`
gives `0 ≤ ord π (deriv x / w)`.

(The same statement is available as the standalone lemma
`Work.Genus.Analysis.ord_deriv_div_nonneg_of_ord_neg`.) -/
private theorem ord_deriv_div_nonneg_of_ord_neg_aux {F : Type*} [Field F] {A : Polynomial F}
    (hA : A.natDegree = 3) {x w : RatFunc F} (hw : w ≠ 0)
    (hx' : Work.Genus.deriv x ≠ 0) (heq : Polynomial.aeval x A = w ^ 2)
    {π : Polynomial F} (hπ : Irreducible π) (hneg : Work.Genus.ord π x < 0) :
    0 ≤ Work.Genus.ord π (Work.Genus.deriv x / w) := by
  have hx0 : x ≠ 0 := fun h => hx' (by rw [h]; exact deriv_zero_ratFunc)
  have hApos : 0 < A.natDegree := by rw [hA]; norm_num
  have h1 : Work.Genus.ord π (Polynomial.aeval x A) = 3 * Work.Genus.ord π x := by
    rw [Work.Genus.Order.ord_aeval_of_neg hπ hApos hx0 hneg, hA]; norm_num
  have h2 : Work.Genus.ord π (w ^ 2) = 2 * Work.Genus.ord π w := by
    rw [Work.Genus.Order.ord_pow hπ hw 2]; norm_num
  have h3 : 2 * Work.Genus.ord π w = 3 * Work.Genus.ord π x := by
    have he : Work.Genus.ord π (Polynomial.aeval x A) = Work.Genus.ord π (w ^ 2) := by rw [heq]
    rw [h1, h2] at he
    linarith
  have h4 : Work.Genus.ord π x - 1 ≤ Work.Genus.ord π (Work.Genus.deriv x) :=
    Work.Genus.Order.ord_deriv_ge hπ hx0 hx'
  rw [Work.Genus.Order.ord_div_rat hπ hx' hw]
  omega

/-- **Regularity of the pulled-back invariant differential at a finite place.**  Let `A` be a
squarefree cubic (`A.natDegree = 3`, `IsCoprime A A'`), `w ≠ 0` and `A(x) = w ^ 2` in `F(t)`, in
characteristic `≠ 2`.  If `x` is *not* constant (`deriv x ≠ 0`) then `deriv x / w` has no pole at
the place of any irreducible `π`.

Route: write `e = ord π w` and split on `ord π x`.
* `ord π x = -m < 0`: then `ord π (A(x)) = 3 * (-m)` (`Work.Genus.Order.ord_aeval_of_neg`, since
  `A.natDegree = 3`) so `2 * e = -3m` (`Work.Genus.Order.ord_pow`) and
  `ord π (deriv x) ≥ -m - 1` (`Work.Genus.Order.ord_deriv_ge`); hence
  `ord π (deriv x / w) ≥ m/2 - 1 ≥ 0` (`Work.Genus.Order.ord_div_rat`).
* `ord π x ≥ 0`: then `e ≥ 0` (`Work.Genus.Order.ord_aeval_nonneg`).
  - `e = 0`: `ord π (deriv x / w) = ord π (deriv x) ≥ 0` (`Work.Genus.Order.ord_deriv_nonneg`).
  - `e > 0`: from `IsCoprime A A'` get `u * A + v * A' = 1` and substitute `x`; with `A(x) = w²`
    this gives `u(x) * w ^ 2 + v(x) * A'(x) = 1`, and `ord π (u(x) * w ^ 2) ≥ 2e > 0` while
    `ord π (u(x)) ≥ 0`, so `ord π (v(x) * A'(x)) = 0` and `ord π (A'(x)) = -ord π (v(x)) ≤ 0`.
    Then `A'(x) * deriv x = 2 * w * deriv w` (`deriv_aeval` for `A(x) = w²` + `deriv_mul`), so
    `ord π (deriv x) ≥ (e + (e - 1)) - 0 ≥ e` (`ord π (deriv w) ≥ e - 1`), whence
    `ord π (deriv x / w) ≥ 0`.  (`A'(x) ≠ 0` and `deriv w ≠ 0` follow: else `u(x) * w ^ 2 = 1`
    while `ord π (u(x) * w ^ 2) ≥ 2e > 0`.) -/
theorem ord_deriv_div_nonneg {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {A : Polynomial F}
    (hA : A.natDegree = 3) (hsq : IsCoprime A (Polynomial.derivative A)) {x w : RatFunc F}
    (hw : w ≠ 0) (hx' : Work.Genus.deriv x ≠ 0) (heq : Polynomial.aeval x A = w ^ 2)
    (π : Polynomial F) (hπ : Irreducible π) :
    0 ≤ Work.Genus.ord π (Work.Genus.deriv x / w) := by
  have hx0 : x ≠ 0 := fun h => hx' (by rw [h]; exact deriv_zero_ratFunc)
  have hordpow : Work.Genus.ord π (w ^ 2) = 2 * Work.Genus.ord π w := by
    rw [Work.Genus.Order.ord_pow hπ hw 2]; norm_num
  have hAord : Work.Genus.ord π (Polynomial.aeval x A) = 2 * Work.Genus.ord π w := by
    rw [heq, hordpow]
  have hdiv : Work.Genus.ord π (Work.Genus.deriv x / w)
      = Work.Genus.ord π (Work.Genus.deriv x) - Work.Genus.ord π w :=
    Work.Genus.Order.ord_div_rat hπ hx' hw
  rcases lt_or_ge (Work.Genus.ord π x) 0 with hneg | hnonneg
  · exact ord_deriv_div_nonneg_of_ord_neg_aux hA hw hx' heq hπ hneg
  · have hAnn : 0 ≤ Work.Genus.ord π (Polynomial.aeval x A) :=
      Work.Genus.Order.ord_aeval_nonneg hπ hnonneg
    have henn : 0 ≤ Work.Genus.ord π w := by
      have := hAnn; rw [hAord] at this; omega
    rcases eq_or_lt_of_le henn with h0 | hpos
    · rw [hdiv]
      have hw0 : Work.Genus.ord π w = 0 := h0.symm
      rw [hw0, sub_zero]
      exact Work.Genus.Order.ord_deriv_nonneg hπ hx0 hx' hnonneg
    · obtain ⟨hBne, hBle⟩ := aeval_derivative_ne_zero_and_ord_nonpos_aux hsq hw heq hπ hnonneg hpos
      have hchain : Polynomial.aeval x (Polynomial.derivative A) * Work.Genus.deriv x
          = 2 * w * Work.Genus.deriv w := by
        have h1 := Work.Genus.Deriv.deriv_aeval (A := A) (x := x)
        rw [heq] at h1
        rw [← h1, pow_two, Work.Genus.Deriv.deriv_mul]
        first | refl_ring1 | ring
      have hdw : Work.Genus.deriv w ≠ 0 := by
        intro hd0
        rw [hd0, mul_zero] at hchain
        rcases mul_eq_zero.mp hchain with h | h
        · exact hBne h
        · exact hx' h
      have h1 : Work.Genus.ord π (Polynomial.aeval x (Polynomial.derivative A)
            * Work.Genus.deriv x)
          = Work.Genus.ord π (Polynomial.aeval x (Polynomial.derivative A))
            + Work.Genus.ord π (Work.Genus.deriv x) :=
        Work.Genus.Order.ord_mul hπ hBne hx'
      have h2' : Work.Genus.ord π (2 * w * Work.Genus.deriv w)
          = Work.Genus.ord π w + Work.Genus.ord π (Work.Genus.deriv w) :=
        ord_two_mul_deriv h2 hπ hw hdw
      have h3 : Work.Genus.ord π w - 1 ≤ Work.Genus.ord π (Work.Genus.deriv w) :=
        Work.Genus.Order.ord_deriv_ge hπ hw hdw
      have hsum : Work.Genus.ord π (Polynomial.aeval x (Polynomial.derivative A))
            + Work.Genus.ord π (Work.Genus.deriv x)
          = Work.Genus.ord π w + Work.Genus.ord π (Work.Genus.deriv w) := by
        rw [← h1, hchain, h2']
      rw [hdiv]
      omega


end Work.Genus.Analysis
