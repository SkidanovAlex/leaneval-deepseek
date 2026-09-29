import Mathlib
import Submission.Commons.Algebra.Polynomial.exists_eq_C_mul_of_derivative_mul_eq
import Submission.Commons.RingTheory.Derivation.map_div
import Submission.Commons.RingTheory.Derivation.aeval_derivative
import Submission.Commons.FieldTheory.Transcendental.aeval_eq_zero_iff

/-!
# Kolchin's lemma: no new constants

Let `K ⊆ L` be fields, `D` a `K`-derivation of `L` (so `D (algebraMap K L c) = 0` for every
`c : K`), and `x ∈ L` an element **transcendental** over `K` whose derivative `D x` is the image of
a *nonzero* constant `a : K`.

**Kolchin's lemma** says that then `x` introduces no new constants: if a rational function of `x`
over `K`, written `P(x)/Q(x)`, has vanishing derivative, it is already a constant, i.e.
`P(x) = c·Q(x)` for some `c : K`.

The proof is the classical degree argument in disguise.  By the chain rule for a derivation applied
to a polynomial (`Commons.RingTheory.Derivation.aeval_derivative`) we have
`D (P(x)) = a·P'(x)`, and the quotient rule
(`Commons.RingTheory.Derivation.map_div`) turns `D (P(x)/Q(x)) = 0` into
`a·(P'(x)·Q(x) − P(x)·Q'(x)) = 0`; since `a ≠ 0` and `x` is transcendental, this is the *polynomial*
identity `P'·Q = P·Q'`, and
`Commons.Algebra.Polynomial.exists_eq_C_mul_of_derivative_mul_eq` finishes.

This is the "constant-coefficient" case of Kolchin's theorem; the general case (coefficients in a
nonconstant differential field) is the first step of the usual inductive proof that the logarithms
of multiplicatively independent functions are algebraically independent.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

/-- **Kolchin's lemma, constant-coefficient case.**  If `x` is transcendental over `K`,
`D` is a `K`-derivation of `L` with `D x = a` for a nonzero `a : K`, and `P(x)/Q(x)` (with
`Q ≠ 0`) has vanishing derivative, then `P(x)/Q(x)` is a constant. -/
theorem exists_const_of_deriv_div_aeval_eq_zero {K L : Type*} [Field K] [CharZero K]
    [Field L] [Algebra K L]
    (D : Derivation K L L) (x : L) (hx : Transcendental K x) (a : K) (ha : a ≠ 0)
    (hDa : D x = algebraMap K L a) {P Q : Polynomial K} (hQ : Q ≠ 0)
    (h : D ((Polynomial.aeval x) P / (Polynomial.aeval x) Q) = 0) :
    ∃ c : K, (Polynomial.aeval x) P = algebraMap K L c * (Polynomial.aeval x) Q := by
  have hQx : (Polynomial.aeval x) Q ≠ 0 := fun h0 =>
    hQ ((Commons.FieldTheory.Transcendental.aeval_eq_zero_iff hx Q).mp h0)
  have haL : algebraMap K L a ≠ 0 := fun h0 =>
    ha ((algebraMap K L).injective (by rw [h0, map_zero]))
  have hPx : D ((Polynomial.aeval x) P)
      = algebraMap K L a * (Polynomial.aeval x) (Polynomial.derivative P) :=
    Commons.RingTheory.Derivation.aeval_derivative D x a hDa P
  have hQx' : D ((Polynomial.aeval x) Q)
      = algebraMap K L a * (Polynomial.aeval x) (Polynomial.derivative Q) :=
    Commons.RingTheory.Derivation.aeval_derivative D x a hDa Q
  have h2 : D ((Polynomial.aeval x) P / (Polynomial.aeval x) Q) * ((Polynomial.aeval x) Q) ^ 2 = 0 := by
    rw [h, zero_mul]
  -- the quotient rule turns the hypothesis into `a·(P'(x)·Q(x) − P(x)·Q'(x)) = 0`
  have h3 : D ((Polynomial.aeval x) P) * (Polynomial.aeval x) Q
      - (Polynomial.aeval x) P * D ((Polynomial.aeval x) Q) = 0 := by
    have hm := Commons.RingTheory.Derivation.map_div D ((Polynomial.aeval x) P)
      ((Polynomial.aeval x) Q) hQx
    rw [hm, div_mul_cancel₀ _ (pow_ne_zero 2 hQx)] at h2
    exact h2
  have hkey : algebraMap K L a
      * ((Polynomial.aeval x) (Polynomial.derivative P) * (Polynomial.aeval x) Q
        - (Polynomial.aeval x) P * (Polynomial.aeval x) (Polynomial.derivative Q)) = 0 := by
    rw [hPx, hQx'] at h3
    linear_combination h3
  have hzero : (Polynomial.aeval x) (Polynomial.derivative P) * (Polynomial.aeval x) Q
      - (Polynomial.aeval x) P * (Polynomial.aeval x) (Polynomial.derivative Q) = 0 :=
    (mul_eq_zero.mp hkey).resolve_left haL
  have haeval : (Polynomial.aeval x)
      (Polynomial.derivative P * Q - P * Polynomial.derivative Q) = 0 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_mul]
    exact hzero
  have hpoly : Polynomial.derivative P * Q - P * Polynomial.derivative Q = 0 :=
    (transcendental_iff.mp hx) _ haeval
  obtain ⟨c, hc⟩ :=
    Commons.Algebra.Polynomial.exists_eq_C_mul_of_derivative_mul_eq hQ (sub_eq_zero.mp hpoly)
  exact ⟨c, by rw [hc, Polynomial.aeval_mul, Polynomial.aeval_C]⟩

end Submission.CDT
