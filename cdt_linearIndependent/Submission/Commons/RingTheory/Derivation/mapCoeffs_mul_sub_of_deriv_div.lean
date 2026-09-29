import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Algebraic.Defs

/-!
# The derivative of a rational function of a transcendental element

Let `R` be a differential field, `S` a differential `R`-algebra which is a field, and `u : S` a
transcendental element of `S` whose derivative is the image of a constant `a : R`
(`u′ = algebraMap R S a`).  For nonzero `Q : R[X]` and `P : R[X]`, the logarithmic derivative
of `P(u)/Q(u)` -- when it happens to be a constant `ρ : R` -- is controlled by the polynomial
identity

`mapCoeffs P * Q - P * mapCoeffs Q + C a * (P′ * Q - P * Q′) = C ρ * Q²`.

Here `mapCoeffs` differentiates the coefficients of a polynomial and `P′` is the formal
derivative.  The identity is the quotient rule combined with the chain rule
`(P(u))′ = (mapCoeffs P)(u) + a · P′(u)`, after which the transcendental element `u` may be
cancelled from the resulting polynomial identity.
-/

open Polynomial

namespace Commons.RingTheory.Derivation

theorem mapCoeffs_mul_sub_of_deriv_div {R S : Type*} [Field R] [Differential R] [Field S] [Algebra R S] [Differential S] [DifferentialAlgebra R S] {u : S} (hu : Transcendental R u) {a : R} (ha : Differential.deriv u = algebraMap R S a) {P Q : Polynomial R} (hQ : Q ≠ 0) {ρ : R} (hv : Differential.deriv ((Polynomial.aeval u) P / (Polynomial.aeval u) Q) = algebraMap R S ρ) : Differential.mapCoeffs P * Q - P * Differential.mapCoeffs Q + Polynomial.C a * (Polynomial.derivative P * Q - P * Polynomial.derivative Q) = Polynomial.C ρ * (Q * Q) := by
  -- `u` transcendental: a polynomial vanishing at `u` is zero, and `Q(u) ≠ 0`.
  have hu' : ∀ p : Polynomial R, (Polynomial.aeval u) p = 0 → p = 0 := transcendental_iff.mp hu
  have hB : (Polynomial.aeval u) Q ≠ 0 := fun h => hQ (hu' Q h)
  -- Chain rule: `(p(u))′ = (mapCoeffs p)(u) + p′(u) · a`.
  have hchain : ∀ p : Polynomial R,
      Differential.deriv ((Polynomial.aeval u) p)
        = (Polynomial.aeval u) (Differential.mapCoeffs p)
          + (Polynomial.aeval u) (Polynomial.derivative p) * algebraMap R S a := by
    intro p
    rw [Differential.deriv_aeval_eq, ha]
  -- Quotient rule for `P(u) / Q(u)`.
  have hquot := Derivation.leibniz_div (D := Differential.deriv)
      (a := (Polynomial.aeval u) P) (b := (Polynomial.aeval u) Q)
  rw [hv] at hquot
  simp only [smul_eq_mul] at hquot
  -- Expand the numerator of the quotient rule using the chain rule.
  have hT : Differential.deriv ((Polynomial.aeval u) P) * (Polynomial.aeval u) Q
      - (Polynomial.aeval u) P * Differential.deriv ((Polynomial.aeval u) Q)
      = (Polynomial.aeval u) (Differential.mapCoeffs P) * (Polynomial.aeval u) Q
        - (Polynomial.aeval u) P * (Polynomial.aeval u) (Differential.mapCoeffs Q)
        + algebraMap R S a * ((Polynomial.aeval u) (Polynomial.derivative P) * (Polynomial.aeval u) Q
          - (Polynomial.aeval u) P * (Polynomial.aeval u) (Polynomial.derivative Q)) := by
    rw [hchain P, hchain Q]
    ring
  -- The corresponding identity evaluated at `u`.
  have hS : (Polynomial.aeval u) (Differential.mapCoeffs P) * (Polynomial.aeval u) Q
      - (Polynomial.aeval u) P * (Polynomial.aeval u) (Differential.mapCoeffs Q)
      + algebraMap R S a * ((Polynomial.aeval u) (Polynomial.derivative P) * (Polynomial.aeval u) Q
        - (Polynomial.aeval u) P * (Polynomial.aeval u) (Polynomial.derivative Q))
      = algebraMap R S ρ * ((Polynomial.aeval u) Q * (Polynomial.aeval u) Q) := by
    rw [← hT, hquot]
    field_simp
  -- Hence the polynomial difference vanishes at `u`.
  have hF : (Polynomial.aeval u)
      (Differential.mapCoeffs P * Q - P * Differential.mapCoeffs Q
        + Polynomial.C a * (Polynomial.derivative P * Q - P * Polynomial.derivative Q)
        - Polynomial.C ρ * (Q * Q)) = 0 := by
    have h2 : (Polynomial.aeval u)
          (Differential.mapCoeffs P * Q - P * Differential.mapCoeffs Q
            + Polynomial.C a * (Polynomial.derivative P * Q - P * Polynomial.derivative Q))
        = (Polynomial.aeval u) (Polynomial.C ρ * (Q * Q)) := by
      simp only [map_sub, map_add, map_mul, Polynomial.aeval_C]
      exact hS
    rw [map_sub, h2, sub_self]
  -- Cancellation of the transcendental element.
  have hzero : Differential.mapCoeffs P * Q - P * Differential.mapCoeffs Q
        + Polynomial.C a * (Polynomial.derivative P * Q - P * Polynomial.derivative Q)
        - Polynomial.C ρ * (Q * Q) = 0 := hu' _ hF
  exact sub_eq_zero.mp hzero

end Commons.RingTheory.Derivation
