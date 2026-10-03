/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The analytic core: basic ring theory of `*`-regular rings

This file sets up the ring-theoretic vocabulary of
Jaikin-Zapirain–López-Álvarez, *The Atiyah conjecture for locally indicable groups*
(arXiv:1810.12135, §3.1), which is the algebraic shadow of the group von Neumann
algebra `N(G)` and of the algebra `U(G)` of affiliated operators.

Main definitions (namespace `Work.ORVonNeumann`):

* `IsVonNeumannRegularElem`, `VonNeumannRegular` — von Neumann regularity;
* `IsProperStar` — an involution with `x * x⋆ = 0 → x = 0`;
* `IsStarRegularRing` — JZLA's `*`-regular ring: regular + proper involution;
* `RelativeInverse x` — the relative inverse `x^{[-1]}` of `x`;
* `HasRelativeInverse`;
* `StarRegularRing` — the bundled form (relative inverses as data);
* `IsPositiveDefinite` — `Matₙ(U)` is `*`-regular for all `n`.
-/
import Mathlib

set_option autoImplicit false

universe u v w

namespace Work.ORVonNeumann

/-- An element `x` of a multiplicative structure is von Neumann regular if there is `y`
with `x * y * x = x`. -/
def IsVonNeumannRegularElem {R : Type*} [Mul R] (x : R) : Prop := ∃ y : R, x * y * x = x

/-- A multiplicative structure in which every element is von Neumann regular. -/
def VonNeumannRegular (R : Type*) [Mul R] : Prop := ∀ x : R, IsVonNeumannRegularElem x

/-- An involution `⋆` on a multiplicative structure with zero is *proper* if `x * x⋆ = 0`
forces `x = 0`. -/
def IsProperStar (R : Type*) [Mul R] [Zero R] [Star R] : Prop := ∀ x : R, x * star x = 0 → x = 0

/-- The left-handed form of `IsProperStar`: `x⋆ * x = 0 → x = 0`. -/
def IsProperStarLeft (R : Type*) [Mul R] [Zero R] [Star R] : Prop :=
  ∀ x : R, star x * x = 0 → x = 0

/-- Jaikin-Zapirain–López-Álvarez's notion of a `*`-regular ring: a von Neumann regular
ring equipped with a proper involution. -/
def IsStarRegularRing (R : Type*) [Mul R] [Zero R] [Star R] : Prop :=
  VonNeumannRegular R ∧ IsProperStar R

section ProperStar

variable {R : Type*} [Ring R] [StarRing R]

theorem isProperStar_iff_isProperStarLeft : IsProperStar R ↔ IsProperStarLeft R := by
  constructor
  · intro h x hx
    have h1 : star x = 0 := h (star x) (by simpa using hx)
    simpa using congrArg star h1
  · intro h x hx
    have h1 : star x = 0 := h (star x) (by simpa using hx)
    simpa using congrArg star h1

theorem IsProperStar.iff (h : IsProperStar R) {x : R} : x * star x = 0 ↔ x = 0 :=
  ⟨h x, fun hx => by rw [hx, star_zero, mul_zero]⟩

end ProperStar

section StarRegular

variable {R : Type*} [Mul R] [Zero R] [Star R]

theorem IsStarRegularRing.isProperStar (h : IsStarRegularRing R) : IsProperStar R := h.2

theorem IsStarRegularRing.regular (h : IsStarRegularRing R) : VonNeumannRegular R := h.1

end StarRegular

/-! ### A warning about direct finiteness

`*`-regularity does **not** imply direct finiteness (`a * b = 1 → b * a = 1`): whether every
`*`-regular ring is directly finite is a well-known open problem of Handelman (see
K. R. Goodearl, *Von Neumann Regular Rings*, Problem 48, and C. Herrmann, *Direct finiteness
of representable regular `*`-rings*, Algebra Universalis 80 (2019)).  The only general
statements available are Ara–Menal's `*`-finiteness: `r * r⋆ = 1 → r⋆ * r = 1`.

For the group von Neumann algebra `N(G)` direct finiteness *is* a theorem (it is a finite
von Neumann algebra), and it is recorded as a field of `GroupVonNeumannAlgebra`, not derived
from `*`-regularity. -/

/-- The relative inverse of an element `x` of a `*`-ring: the (unique, when it exists)
element `x^{[-1]}` with `x x^{[-1]} x = x`, `x^{[-1]} x x^{[-1]} = x^{[-1]}` and with
both `x x^{[-1]}` and `x^{[-1]} x` self-adjoint idempotents. -/
structure RelativeInverse {R : Type*} [Mul R] [Star R] (x : R) where
  /-- the relative inverse -/
  inv : R
  mul_inv_mul : x * inv * x = x
  inv_mul_inv : inv * x * inv = inv
  isStarProjection_mul : IsStarProjection (x * inv)
  isStarProjection_inv_mul : IsStarProjection (inv * x)

/-- Every element has a relative inverse.  By the theorem of Berberian this is equivalent
to `IsStarRegularRing`; the implication `HasRelativeInverse → IsStarRegularRing` is
elementary, while the converse is a theorem. -/
def HasRelativeInverse (R : Type*) [Mul R] [Star R] : Prop := ∀ x : R, Nonempty (RelativeInverse x)

section RelInv

variable {R : Type*} [Ring R] [StarRing R]

theorem HasRelativeInverse.isProperStar (h : HasRelativeInverse R) : IsProperStar R := by
  intro x hx
  obtain ⟨y, hy1, _hy2, _hy3, hy4⟩ := h x
  have hyx : y * x = star x * star y :=
    calc y * x = star (y * x) := hy4.isSelfAdjoint.symm
      _ = star x * star y := star_mul y x
  calc x = x * y * x := hy1.symm
    _ = x * (y * x) := by rw [mul_assoc]
    _ = x * (star x * star y) := by rw [hyx]
    _ = x * star x * star y := by rw [mul_assoc]
    _ = 0 := by rw [hx, zero_mul]

theorem HasRelativeInverse.isStarRegularRing (h : HasRelativeInverse R) : IsStarRegularRing R :=
  ⟨fun x => by obtain ⟨y, hy1, _⟩ := h x; exact ⟨y, hy1⟩, h.isProperStar⟩

end RelInv

/-- A `*`-regular ring in *bundled* form: the ring together with the data of the relative
inverse of every element.  By Berberian's theorem this is equivalent to
`IsStarRegularRing`, and it is the form in which the analytic examples (`Matₙ`, group von
Neumann algebras, the algebra of affiliated operators) are naturally presented. -/
structure StarRegularRing (R : Type*) [Ring R] [StarRing R] where
  /-- every element has a relative inverse -/
  relInv : R → R
  relInv_mul_inv_mul : ∀ x : R, x * relInv x * x = x
  relInv_inv_mul_inv : ∀ x : R, relInv x * x * relInv x = relInv x
  isStarProjection_mul : ∀ x : R, IsStarProjection (x * relInv x)
  isStarProjection_inv_mul : ∀ x : R, IsStarProjection (relInv x * x)

namespace StarRegularRing

variable {R : Type*} [Ring R] [StarRing R]

/-- The relative inverse, packaged. -/
def relativeInverse (S : StarRegularRing R) (x : R) : RelativeInverse x where
  inv := S.relInv x
  mul_inv_mul := S.relInv_mul_inv_mul x
  inv_mul_inv := S.relInv_inv_mul_inv x
  isStarProjection_mul := S.isStarProjection_mul x
  isStarProjection_inv_mul := S.isStarProjection_inv_mul x

theorem hasRelativeInverse (S : StarRegularRing R) : HasRelativeInverse R :=
  fun x => ⟨S.relativeInverse x⟩

theorem isStarRegularRing (S : StarRegularRing R) : IsStarRegularRing R :=
  S.hasRelativeInverse.isStarRegularRing

end StarRegularRing

/-- The "no non-trivial sums of squares" condition: `∑ i, x i * (x i)⋆ = 0` forces all
`x i = 0`.  This is the operational form of positive definiteness: it is exactly what makes
the conjugate-transpose involution on `Matₙ(R)` proper, and hence (with regularity of `R`,
which passes to matrix rings) makes `Matₙ(R)` `*`-regular for every `n`.

It *does not* follow from `IsStarRegularRing R` alone: with the identity involution on `ℂ`,
`i² + 1² = 0`.  This is why Jaikin-Zapirain–López-Álvarez define positive definiteness as a
separate hypothesis. -/
def HasNoNontrivialSquares (R : Type*) [Ring R] [Star R] : Prop :=
  ∀ (n : ℕ) (x : Fin n → R), (∑ i, x i * star (x i)) = 0 → ∀ i, x i = 0

/-- `Matₙ(U)` is `*`-regular whenever `U` is: this is the content of "positive definiteness"
in Jaikin-Zapirain–López-Álvarez (arXiv:1810.12135, §3.1). -/
def IsPositiveDefinite (R : Type*) [Ring R] [StarRing R] : Prop :=
  IsStarRegularRing R ∧ ∀ n : ℕ, IsStarRegularRing (Matrix (Fin n) (Fin n) R)

/-- Bundled positive definiteness. -/
def IsPositiveDefiniteBundled (R : Type*) [Ring R] [StarRing R] : Prop :=
  Nonempty (StarRegularRing R) ∧ ∀ n : ℕ, Nonempty (StarRegularRing (Matrix (Fin n) (Fin n) R))

end Work.ORVonNeumann
