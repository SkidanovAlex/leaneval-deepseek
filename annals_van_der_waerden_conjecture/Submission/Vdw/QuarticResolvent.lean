import Mathlib

open Polynomial

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The cubic resolvent of a monic quartic

This module starts the `n = 4` *imprimitive* chapter of the proof of
`theorem_1`, following S. Chow and R. Dietmann, *Enumerative Galois theory for
cubics and quartics*, Adv. Math. **372** (2020) 107282.

For a monic quartic `f(X) = X^4 + a X^3 + b X^2 + c X + d` the **cubic
resolvent** is

  `r(X) = X^3 - b X^2 + (a c - 4 d) X - (a^2 d - 4 b d + c^2)`.

Its roots (in a splitting field) are `α_i α_j + α_k α_l`, one for each of the
three pairings of the four roots of `f`; consequently an irreducible quartic
has imprimitive Galois group exactly when `r` has a rational root (Kappe–Warren
criterion), and that rational root is an integer because `r` is monic.

The key computational input for the Chow–Dietmann count of imprimitive
quartics is the **"remarkable symmetry"** identity

  `4 * r(x) = (x^2 - 4 d) * (a^2 - 4 (b - x)) - (x a - 2 c)^2`,

which, together with the `(A, B, p, q)` description of `f` by its two
(conjugate) quadratic factors over a quadratic field, shows that `β := p + q`
(the "resolvent root" attached to that factorization) is a root of `r`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only (pure algebra).
-/

namespace Submission.Vdw

noncomputable section

/-- The cubic resolvent of the monic quartic `X ^ 4 + a * X ^ 3 + b * X ^ 2 + c * X + d`,
over an arbitrary commutative ring. -/
def resolventCubic {R : Type*} [CommRing R] (a b c d : R) : R[X] :=
  X ^ 3 - C b * X ^ 2 + C (a * c - 4 * d) * X - C (a ^ 2 * d - 4 * b * d + c ^ 2)

@[simp]
theorem resolventCubic_def {R : Type*} [CommRing R] (a b c d : R) :
    resolventCubic a b c d
      = X ^ 3 - C b * X ^ 2 + C (a * c - 4 * d) * X - C (a ^ 2 * d - 4 * b * d + c ^ 2) :=
  rfl

/-- The resolvent commutes with coefficient change of rings. -/
theorem resolventCubic_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b c d : R) :
    (resolventCubic a b c d).map f = resolventCubic (f a) (f b) (f c) (f d) := by
  rw [show resolventCubic a b c d
        = X ^ 3 - C b * X ^ 2 + C (a * c - 4 * d) * X - C (a ^ 2 * d - 4 * b * d + c ^ 2)
      from rfl,
      show resolventCubic (f a) (f b) (f c) (f d)
        = X ^ 3 - C (f b) * X ^ 2 + C (f a * f c - 4 * f d) * X
            - C (f a ^ 2 * f d - 4 * f b * f d + f c ^ 2) from rfl]
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    map_C, map_X]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]

/-- **The "remarkable symmetry" identity** (Chow–Dietmann, §"A remarkable
symmetry"): four times the resolvent at `x` is a difference of two squares. -/
theorem four_mul_resolventCubic_eval {R : Type*} [CommRing R] (a b c d x : R) :
    4 * (resolventCubic a b c d).eval x
      = (x ^ 2 - 4 * d) * (a ^ 2 - 4 * (b - x)) - (x * a - 2 * c) ^ 2 := by
  simp only [resolventCubic, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- **The symmetry equation at a root.**  Over `ℚ`, a root of the resolvent
satisfies the Chow–Dietmann symmetry equation. -/
theorem symm_equation_of_resolvent_root (a b c d x : ℚ)
    (h : (resolventCubic a b c d).eval x = 0) :
    (x ^ 2 - 4 * d) * (a ^ 2 - 4 * (b - x)) = (x * a - 2 * c) ^ 2 := by
  have h4 := four_mul_resolventCubic_eval a b c d x
  rw [h, mul_zero] at h4
  linarith [h4]

/-- Over `ℚ`, the symmetry equation is *equivalent* to being a root of the
resolvent. -/
theorem resolvent_root_iff_symm_equation (a b c d x : ℚ) :
    (resolventCubic a b c d).eval x = 0 ↔
      (x ^ 2 - 4 * d) * (a ^ 2 - 4 * (b - x)) = (x * a - 2 * c) ^ 2 := by
  have h4 := four_mul_resolventCubic_eval a b c d x
  constructor
  · intro h; rw [h, mul_zero] at h4; linarith [h4]
  · intro h; rw [h, sub_self] at h4; linarith [h4]

/-- **The resolvent root attached to a factorization into two quadratics.**

If `f` factors as `(X^2 - A X + p) (X^2 - B X + q)`, then the symmetric data
`a = -(A+B)`, `b = p + q + A B`, `c = -(p B + q A)`, `d = p q` are the
coefficients of `f`, and `β = p + q` is a root of the resolvent of `f`.  This is
the direction needed for the imprimitive count: it turns a conjugate pair of
quadratic factors over a quadratic field into an integral point of the
resolvent equation. -/
theorem resolventCubic_eval_pairing {R : Type*} [CommRing R] (A B p q : R) :
    (resolventCubic (-(A + B)) (p + q + A * B) (-(p * B + q * A)) (p * q)).eval (p + q)
      = 0 := by
  simp only [resolventCubic, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- `aeval` of the integer resolvent at a rational point is the rational
resolvent evaluated there (the `ℤ → ℚ` coefficient bridge). -/
theorem aeval_resolventCubic_eq (a b c d : ℤ) (x : ℚ) :
    Polynomial.aeval x (resolventCubic a b c d)
      = (resolventCubic (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ)).eval x := by
  have hmap : (resolventCubic a b c d).map (algebraMap ℤ ℚ)
      = (resolventCubic (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ)) :=
    resolventCubic_map (algebraMap ℤ ℚ) a b c d
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hmap]

/-- Evaluating the rational resolvent at the image of an integer is the cast of
the integer evaluation. -/
theorem eval_resolventCubic_intCast (a b c d : ℤ) (z : ℤ) :
    (resolventCubic (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ)).eval (z : ℚ)
      = (((resolventCubic a b c d).eval z : ℤ) : ℚ) := by
  have hmap : (resolventCubic a b c d).map (algebraMap ℤ ℚ)
      = (resolventCubic (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ)) :=
    resolventCubic_map (algebraMap ℤ ℚ) a b c d
  conv_lhs => rw [show (resolventCubic (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ))
      = (resolventCubic a b c d).map (algebraMap ℤ ℚ) from hmap.symm]
  exact Polynomial.eval_map_apply (p := resolventCubic a b c d) (f := algebraMap ℤ ℚ) (x := z)

/-- A rational number that is integral over `ℤ` is an integer. -/
theorem exists_int_of_isIntegral_rat {x : ℚ} (hx : IsIntegral ℤ x) :
    ∃ z : ℤ, (z : ℚ) = x :=
  IsIntegrallyClosed.isIntegral_iff.mp hx

end

end Submission.Vdw
