import Mathlib
import Submission.CDT.RatFuncConstants
import Submission.CDT.KolchinHeart
import Submission.CDT.LogMultiplicative
import Submission.CDT.LogTranscendence
import Submission.Commons.FieldTheory.Transcendental.aeval_eq_zero_iff

/-!
# Kolchin's lemma: no new constants for `K(X)(x)` with `x'` not a derivative

`Submission.CDT.DifferentialConstants` proves the *constant-coefficient* case of Kolchin's lemma:
if `D` is a `K`-derivation of an extension and `x` has `D x = a` for a nonzero constant `a`, then a
rational function of `x` with vanishing derivative is a constant.  Here the coefficients are no
longer constants: `x` is transcendental over `R = K(Y) = K(X)` and `x' = a` with `a ∈ R` **not a
derivative in `R`**; then again every rational function of `x` with vanishing derivative is a
constant — but now a constant of `K` and not merely of `K(Y)`, because the constants of `K(Y)` are
`K` (`exists_const_of_dRat_eq_zero`).

The algebraic content is `Submission.CDT.KolchinHeart.exists_algebraMap_C_mul_of_relation`, applied
to the polynomial identity obtained from the chain rule
`Differential.deriv_aeval_eq` and the quotient rule.
-/

open scoped Differential

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {L : Type*} [Field L] [Algebra (RatFunc K) L] [Differential (RatFunc K)]
  [Differential L] [DifferentialAlgebra (RatFunc K) L]

/-- **Kolchin's lemma.**  Let `L` be a differential field extension of `K(X)`, let `x ∈ L` be
transcendental over `K(X)` with `x' = a` where `a ∈ K(X)` is *not* the derivative of any element of
`K(X)`.  Then a rational function `P(x)/Q(x)` of `x` (`Q ≠ 0`) with vanishing derivative is a
constant of `K`: it is the image of an element of `K`.

(Without the hypothesis that `a` is not a derivative the statement fails: if `a = b'` then
`x - b` is a new constant.) -/
theorem kolchin_no_new_constants
    (hderiv : ∀ r : RatFunc K, r′ = dRat r)
    {x : L} (hx : Transcendental (RatFunc K) x) {a : RatFunc K}
    (ha : ∀ b : RatFunc K, dRat b ≠ a)
    (hx' : x′ = algebraMap (RatFunc K) L a)
    {P Q : Polynomial (RatFunc K)} (hQ : Q ≠ 0)
    (h : Differential.deriv ((Polynomial.aeval x) P / (Polynomial.aeval x) Q) = 0) :
    ∃ c : K, (Polynomial.aeval x) P / (Polynomial.aeval x) Q
      = algebraMap (RatFunc K) L (algebraMap K (RatFunc K) c) := by
  have hQx : (Polynomial.aeval x) Q ≠ 0 := fun h0 =>
    hQ ((Commons.FieldTheory.Transcendental.aeval_eq_zero_iff hx Q).mp h0)
  -- the numerator of the quotient rule vanishes
  have hnum : Differential.deriv ((Polynomial.aeval x) P) * (Polynomial.aeval x) Q
      - (Polynomial.aeval x) P * Differential.deriv ((Polynomial.aeval x) Q) = 0 := by
    have hquot := map_div' (Differential.deriv : Derivation ℤ L L)
      ((Polynomial.aeval x) P) ((Polynomial.aeval x) Q) hQx
    have h2 : (Differential.deriv ((Polynomial.aeval x) P) * (Polynomial.aeval x) Q
        - (Polynomial.aeval x) P * Differential.deriv ((Polynomial.aeval x) Q))
        / ((Polynomial.aeval x) Q) ^ 2 = 0 := by
      rw [← hquot]
      exact h
    rcases div_eq_zero_iff.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 (pow_ne_zero 2 hQx)
  -- the chain rule
  have hchainP : Differential.deriv ((Polynomial.aeval x) P)
      = (Polynomial.aeval x) (Differential.mapCoeffs P)
        + (Polynomial.aeval x) P.derivative * algebraMap (RatFunc K) L a := by
    rw [Differential.deriv_aeval_eq x P, hx']
  have hchainQ : Differential.deriv ((Polynomial.aeval x) Q)
      = (Polynomial.aeval x) (Differential.mapCoeffs Q)
        + (Polynomial.aeval x) Q.derivative * algebraMap (RatFunc K) L a := by
    rw [Differential.deriv_aeval_eq x Q, hx']
  -- the polynomial identity
  have hval : (Polynomial.aeval x) (Differential.mapCoeffs P * Q
      - P * Differential.mapCoeffs Q
      + Polynomial.C a * (P.derivative * Q - P * Q.derivative))
      = (Polynomial.aeval x) (Differential.mapCoeffs P) * (Polynomial.aeval x) Q
        - (Polynomial.aeval x) P * (Polynomial.aeval x) (Differential.mapCoeffs Q)
        + algebraMap (RatFunc K) L a
          * ((Polynomial.aeval x) P.derivative * (Polynomial.aeval x) Q
            - (Polynomial.aeval x) P * (Polynomial.aeval x) Q.derivative) := by
    simp only [Polynomial.aeval_add, Polynomial.aeval_sub, Polynomial.aeval_mul,
      Polynomial.aeval_C]
  have hkey : (Polynomial.aeval x) (Differential.mapCoeffs P * Q
      - P * Differential.mapCoeffs Q
      + Polynomial.C a * (P.derivative * Q - P * Q.derivative)) = 0 := by
    rw [hval]
    rw [hchainP, hchainQ] at hnum
    linear_combination (norm := ring_nf) hnum
  have hrel : Differential.mapCoeffs P * Q - P * Differential.mapCoeffs Q
      + Polynomial.C a * (P.derivative * Q - P * Q.derivative) = 0 :=
    (Commons.FieldTheory.Transcendental.aeval_eq_zero_iff hx _).mp hkey
  -- the constants of `K(X)` are the elements of `K`
  have hconst : ∀ r : RatFunc K, r′ = 0 → ∃ c : K, r = algebraMap K (RatFunc K) c := by
    intro r hr
    exact exists_const_of_dRat_eq_zero (by rwa [hderiv] at hr)
  have hconst' : ∀ c : K, (algebraMap K (RatFunc K) c)′ = 0 := by
    intro c
    rw [hderiv, dRat_const]
  obtain ⟨c, hc⟩ := exists_algebraMap_C_mul_of_relation (R := RatFunc K) (K := K)
    hconst hconst' hQ (fun b hb => ha b (by rwa [hderiv] at hb)) hrel
  refine ⟨c, ?_⟩
  rw [hc, Polynomial.aeval_mul, Polynomial.aeval_C]
  field_simp

variable [IsAlgClosed K] in
/-- **Kolchin's lemma for logarithms.**  If `u` is a logarithm in the function-field sense,
`u' = (dRat f)/f` for a nonconstant `f ∈ K(X)`, then the constants of `K(X)(u)` are the constants
of `K`: a rational function of `u` with vanishing derivative is an element of `K`.

This is the form of Kolchin's lemma used in the inductive proof that the logarithms of
multiplicatively independent functions are algebraically independent: the logarithmic derivative
`(dRat f)/f` is never a derivative in `K(X)` (`not_exists_dRat_eq_dRat_div`). -/
theorem exists_const_of_deriv_eq_zero_of_logDeriv
    (hderiv : ∀ r : RatFunc K, r′ = dRat r)
    {f : RatFunc K} (hf : dRat f ≠ 0)
    {x : L} (hx : Transcendental (RatFunc K) x)
    (hx' : x′ = algebraMap (RatFunc K) L (dRat f / f))
    {P Q : Polynomial (RatFunc K)} (hQ : Q ≠ 0)
    (h : Differential.deriv ((Polynomial.aeval x) P / (Polynomial.aeval x) Q) = 0) :
    ∃ c : K, (Polynomial.aeval x) P / (Polynomial.aeval x) Q
      = algebraMap (RatFunc K) L (algebraMap K (RatFunc K) c) :=
  kolchin_no_new_constants hderiv hx (fun b => not_exists_dRat_eq_dRat_div f hf b) hx' hQ h

end Submission.CDT
