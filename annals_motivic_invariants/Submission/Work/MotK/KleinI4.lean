/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.KleinIdents

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# I4 (`s(R(z)) = s'(z)³`) over an arbitrary commutative ring

`KleinIdents.kleinSec_kleinR` proves the identity over a domain provided `R_0(z) ≠ 0`: it is the
cancellation of the *multiplied* identity `KleinIdents.kleinI4_mul` by the non-zero-divisor
`R_0(z)`.  Neither hypothesis is available here:

* the composed expression `s(R(z))` is a polynomial of degree 15 in five coordinates and two
  parameters, far too large for `ring` to normalise (see `MotK/GUIDE.md` §2b);
* over a general commutative ring, `R_0(z)` need not be a non-zero-divisor (`R` may be
  non-reduced), so the cancellation in `kleinSec_kleinR` is not legitimate.

The classical way out, and the one taken here, is the **universal ring** of the identity.  Both
sides are integer-coefficient polynomial expressions in the seven atoms `a, b, z 0, …, z 4`, and
the three maps `kleinR`, `kleinSec`, `kleinSecDual` are natural in the ring (`+`, `*`, `-`, `^`,
integer constants only).  Hence it suffices to prove the identity in
`Univ = ℤ[X_0, …, X_6]` — a domain, in which `R_0` is a *non-zero* polynomial (it takes the value
`-1` at `a = b = z_i = 1`) — and to push it back along the evaluation homomorphism
`univEvalMap a b z : Univ →+* R` sending `X_0, …, X_4` to `z 0, …, z 4` and `X_5, X_6` to `b, a`
respectively.

Structure of the file:

* `kleinSec_map`, `kleinSecDual_map`, `kleinR_map` — naturality of the Klein data under an
  arbitrary ring homomorphism `R →+* S`.
* `univR0_ne` — `R_0 ≠ 0` in the universal ring (proof: evaluate at `a = b = z_i = 1`, where
  `R_0 = -1`).
* `kleinI4_univ` — the identity in `Univ`, by `kleinSec_kleinR` (the universal ring is a domain).
* `KleinI4` — the general case, by transferring `kleinI4_univ` along `univEvalMap`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.MotK

/-! ## Naturality of the Klein data under ring homomorphisms -/

/-- The secant quintic is an integer-coefficient polynomial expression, hence natural in the
coefficient ring. -/
theorem kleinSec_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (x : Fin 5 → R) : φ (kleinSec a b x) = kleinSec (φ a) (φ b) (fun i => φ (x i)) := by
  simp only [kleinSec]
  simp only [map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_natCast]

/-- The dual secant quintic is natural in the coefficient ring. -/
theorem kleinSecDual_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (x : Fin 5 → R) :
    φ (kleinSecDual a b x) = kleinSecDual (φ a) (φ b) (fun i => φ (x i)) := by
  simp only [kleinSecDual]
  simp only [map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_natCast]

/-- The inverse quadro-cubic map is natural in the coefficient ring (component `0`). -/
theorem kleinR_map_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (z : Fin 5 → R) : φ (kleinR a b z 0) = kleinR (φ a) (φ b) (fun j => φ (z j)) 0 := by
  simp only [kleinR_zero, kleinR0, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat]

/-- The inverse quadro-cubic map is natural in the coefficient ring (component `1`). -/
theorem kleinR_map_one {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (z : Fin 5 → R) : φ (kleinR a b z 1) = kleinR (φ a) (φ b) (fun j => φ (z j)) 1 := by
  simp only [kleinR_one, kleinR1, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat]

/-- The inverse quadro-cubic map is natural in the coefficient ring (component `2`). -/
theorem kleinR_map_two {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (z : Fin 5 → R) : φ (kleinR a b z 2) = kleinR (φ a) (φ b) (fun j => φ (z j)) 2 := by
  simp only [kleinR_two, kleinR2, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat]

/-- The inverse quadro-cubic map is natural in the coefficient ring (component `3`). -/
theorem kleinR_map_three {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (z : Fin 5 → R) : φ (kleinR a b z 3) = kleinR (φ a) (φ b) (fun j => φ (z j)) 3 := by
  simp only [kleinR_three, kleinR3, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat]

/-- The inverse quadro-cubic map is natural in the coefficient ring (component `4`). -/
theorem kleinR_map_four {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (z : Fin 5 → R) : φ (kleinR a b z 4) = kleinR (φ a) (φ b) (fun j => φ (z j)) 4 := by
  simp only [kleinR_four, kleinR4, map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat]

/-- The inverse quadro-cubic map is natural in the coefficient ring. -/
theorem kleinR_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (z : Fin 5 → R) (i : Fin 5) :
    φ (kleinR a b z i) = kleinR (φ a) (φ b) (fun j => φ (z j)) i := by
  fin_cases i
  · change φ (kleinR a b z 0) = kleinR (φ a) (φ b) (fun j => φ (z j)) 0
    exact kleinR_map_zero φ a b z
  · change φ (kleinR a b z 1) = kleinR (φ a) (φ b) (fun j => φ (z j)) 1
    exact kleinR_map_one φ a b z
  · change φ (kleinR a b z 2) = kleinR (φ a) (φ b) (fun j => φ (z j)) 2
    exact kleinR_map_two φ a b z
  · change φ (kleinR a b z 3) = kleinR (φ a) (φ b) (fun j => φ (z j)) 3
    exact kleinR_map_three φ a b z
  · change φ (kleinR a b z 4) = kleinR (φ a) (φ b) (fun j => φ (z j)) 4
    exact kleinR_map_four φ a b z

/-! ## The universal ring

`Univ = ℤ[X_0, …, X_6]`, with `X_0, …, X_4` the coordinates `z` and `X_5, X_6` the parameters
`a, b`.  It is a domain, and the Klein data in it is *universal*: every other instance is the
image of this one under a unique ring homomorphism. -/

/-- The universal ring of the Klein data: `Fin 5` are the five coordinates, `Fin 2` the
parameters `a, b`. -/
abbrev Univ : Type := MvPolynomial (Fin 5 ⊕ Fin 2) ℤ

/-- The universal coordinate `z i = X i`. -/
noncomputable def univZ : Fin 5 → Univ := fun i => MvPolynomial.X (Sum.inl i)

/-- The universal parameter `a = X 5`. -/
noncomputable def univA : Univ := MvPolynomial.X (Sum.inr 0)

/-- The universal parameter `b = X 6`. -/
noncomputable def univB : Univ := MvPolynomial.X (Sum.inr 1)

/-- Evaluation of the universal ring at `a = b = z_i = 1`. -/
noncomputable def univEvalOne : Univ →+* ℤ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (fun _ => 1)

/-- In the universal ring the first component `R_0` of the inverse quadro-cubic map is a non-zero
polynomial: at `a = b = z_i = 1` it takes the value `-1`. -/
theorem univR0_ne : kleinR univA univB univZ 0 ≠ 0 := by
  intro h
  have h1 : univEvalOne (kleinR univA univB univZ 0) = 0 := by rw [h, map_zero]
  rw [kleinR_map univEvalOne univA univB univZ 0] at h1
  simp only [univEvalOne, univA, univB, univZ, MvPolynomial.eval₂Hom_X'] at h1
  simp only [kleinR_zero, kleinR0] at h1
  norm_num at h1

/-- **I4 in the universal ring.**  The universal ring is a domain and `R_0 ≠ 0` there, so the
multiplied identity `KleinIdents.kleinI4_mul` can be cancelled. -/
theorem kleinI4_univ :
    kleinSec univA univB (kleinR univA univB univZ) = kleinSecDual univA univB univZ ^ 3 :=
  kleinSec_kleinR univA univB univZ univR0_ne

/-! ## Transferring the universal identity to an arbitrary commutative ring -/

/-- The evaluation homomorphism `ℤ[X_0,…,X_6] →+* R` sending `z i ↦ z i`, `a ↦ a`, `b ↦ b`. -/
noncomputable def univEvalMap {R : Type*} [CommRing R] (a b : R) (z : Fin 5 → R) :
    Univ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim z ![a, b])

theorem univEvalMap_univA {R : Type*} [CommRing R] (a b : R) (z : Fin 5 → R) :
    univEvalMap a b z univA = a := by
  simp only [univEvalMap, univA, MvPolynomial.eval₂Hom_X', Sum.elim_inr, Matrix.cons_val_zero]

theorem univEvalMap_univB {R : Type*} [CommRing R] (a b : R) (z : Fin 5 → R) :
    univEvalMap a b z univB = b := by
  simp [univEvalMap, univB, MvPolynomial.eval₂Hom_X', Sum.elim_inr]

theorem univEvalMap_univZ {R : Type*} [CommRing R] (a b : R) (z : Fin 5 → R) (i : Fin 5) :
    univEvalMap a b z (univZ i) = z i := by
  simp only [univEvalMap, univZ, MvPolynomial.eval₂Hom_X', Sum.elim_inl]

/-- The evaluation homomorphism sends the universal coordinates to the given ones. -/
theorem univEvalMap_univZ_fun {R : Type*} [CommRing R] (a b : R) (z : Fin 5 → R) :
    (fun i => univEvalMap a b z (univZ i)) = z :=
  funext fun i => univEvalMap_univZ a b z i

/-- The evaluation homomorphism sends the universal inverse quadro-cubic map to the given one. -/
theorem univEvalMap_kleinR {R : Type*} [CommRing R] (a b : R) (z : Fin 5 → R) :
    (fun i => univEvalMap a b z (kleinR univA univB univZ i)) = kleinR a b z := by
  funext i
  rw [kleinR_map]
  simp only [univEvalMap_univA, univEvalMap_univB, univEvalMap_univZ]

/-- The evaluation homomorphism sends the universal secant quintic of the universal inverse
quadro-cubic map to the one attached to `a, b, z`. -/
theorem univEvalMap_kleinSec {R : Type*} [CommRing R] (a b : R) (z : Fin 5 → R) :
    univEvalMap a b z (kleinSec univA univB (kleinR univA univB univZ))
      = kleinSec a b (kleinR a b z) := by
  rw [kleinSec_map]
  rw [univEvalMap_kleinR, univEvalMap_univA, univEvalMap_univB]

/-- The evaluation homomorphism sends the universal dual secant quintic to the one attached to
`a, b, z`. -/
theorem univEvalMap_kleinSecDual {R : Type*} [CommRing R] (a b : R) (z : Fin 5 → R) :
    univEvalMap a b z (kleinSecDual univA univB univZ) = kleinSecDual a b z := by
  rw [kleinSecDual_map]
  rw [univEvalMap_univZ_fun, univEvalMap_univA, univEvalMap_univB]

/-- **I4 (Klein–Fisher identity)** over an arbitrary commutative ring: the inverse quadro-cubic
map `R` composed with the secant quintic `s` is the cube of the dual secant quintic `s'`. -/
theorem KleinI4 {R : Type*} [CommRing R] (a b : R) (z : Fin 5 → R) :
    Work.MotK.kleinSec a b (Work.MotK.kleinR a b z) = Work.MotK.kleinSecDual a b z ^ 3 := by
  calc kleinSec a b (kleinR a b z)
      = univEvalMap a b z (kleinSec univA univB (kleinR univA univB univZ)) :=
        (univEvalMap_kleinSec a b z).symm
    _ = univEvalMap a b z (kleinSecDual univA univB univZ ^ 3) := by rw [kleinI4_univ]
    _ = univEvalMap a b z (kleinSecDual univA univB univZ) ^ 3 := by rw [map_pow]
    _ = kleinSecDual a b z ^ 3 := by rw [univEvalMap_kleinSecDual]

end Work.MotK
