import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASLink
import Submission.Work.MotAS.KleinLinkUnitAS
import Submission.Work.MotAS.KleinTwI2I4ASBGuide
import Submission.Work.MotAS.kleinRAS_kleinPAS_mul_comm
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The unit condition of the AS link, free of the auxiliary Artin–Schreier root

`Work.MotAS.KleinLinkUnitAS` proves the unit condition of the Crauder–Katz chart in the
Artin–Schreier Galois coordinates over a ring *containing* a root `w` of `X⁵ - X - g`
(`hw : w ^ 5 = w + g`).  Its statement therefore carries the extra datum `w`.

The present file removes that datum from the *statement*.  Every AS coordinate (`kleinQAS`,
`kleinPAS`, `kleinRAS`, `kleinSecAS`, `kleinSecDualAS`, `kleinBilinAS`, `kleinStereoAS`,
`kleinFhomAS`, `kleinGhomAS`) is a polynomial with integer coefficients in `a, b, g` and the
coordinates, hence commutes with every ring homomorphism; the identity therefore descends from
the universal extension `S = R[w]/(w⁵ - w - g)` along the (injective, `X⁵ - X - g` being monic
of positive degree) structure map `R → S`.

Concretely: apply `KleinLinkUnitAS` in `S` to the images of `a, b, g, p, v`, then rewrite both
sides of the *statement over `R`* by the naturality lemmas below and finish with
`AdjoinRoot.of.injective_of_monic_of_degree_pos`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Work.MotAS

variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B]

/-! ## Naturality of the AS link data under an arbitrary ring homomorphism

Each identity is a polynomial identity with integer coefficients, so it is proved by pushing `φ`
through the ring operations.  (`map_kleinPAS_mul_comm` and `map_kleinRAS_mul_comm` are the
componentwise versions already available in
`Submission/Work/MotAS/kleinRAS_kleinPAS_mul_comm.lean`.) -/

/-- Naturality of the twisted quadric `kleinQAS`. -/
theorem freeMap_kleinQAS (φ : A →+* B) (a b : A) (u : Fin 5 → A) :
    φ (kleinQAS a b u) = kleinQAS (φ a) (φ b) (fun i => φ (u i)) := by
  simp only [kleinQAS, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]

/-- Naturality of the polar form `kleinBilinAS`. -/
theorem freeMap_kleinBilinAS (φ : A →+* B) (a b : A) (u v : Fin 5 → A) :
    φ (kleinBilinAS a b u v)
      = kleinBilinAS (φ a) (φ b) (fun i => φ (u i)) (fun i => φ (v i)) := by
  have h1 : (fun i => φ ((u + v) i)) = (fun i => φ (u i)) + (fun i => φ (v i)) := by
    funext i; simp only [Pi.add_apply, map_add]
  simp only [kleinBilinAS, map_sub]
  rw [freeMap_kleinQAS, freeMap_kleinQAS, freeMap_kleinQAS, h1]

/-- Naturality of the stereographic parametrisation `kleinStereoAS`. -/
theorem freeMap_kleinStereoAS (φ : A →+* B) (a b : A) (p v : Fin 5 → A) :
    (fun i => φ (kleinStereoAS a b p v i))
      = kleinStereoAS (φ a) (φ b) (fun i => φ (p i)) (fun i => φ (v i)) := by
  funext i
  simp only [kleinStereoAS, map_sub, map_mul]
  rw [freeMap_kleinQAS, freeMap_kleinBilinAS]

/-- Naturality of the source secant quintic `kleinSecAS`. -/
theorem freeMap_kleinSecAS (φ : A →+* B) (a b g : A) (y : Fin 5 → A) :
    φ (kleinSecAS a b g y) = kleinSecAS (φ a) (φ b) (φ g) (fun i => φ (y i)) := by
  simp only [kleinSecAS, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_neg]

/-- Naturality of the target secant quintic `kleinSecDualAS`. -/
theorem freeMap_kleinSecDualAS (φ : A →+* B) (a b g : A) (z : Fin 5 → A) :
    φ (kleinSecDualAS a b g z) = kleinSecDualAS (φ a) (φ b) (φ g) (fun i => φ (z i)) := by
  simp only [kleinSecDualAS, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_neg]

/-- Naturality of the source equation `kleinFhomAS` of the AS link. -/
theorem freeMap_kleinFhomAS (φ : A →+* B) (a b g : A) (p v : Fin 5 → A) :
    φ (kleinFhomAS a b g p v)
      = kleinFhomAS (φ a) (φ b) (φ g) (fun i => φ (p i)) (fun i => φ (v i)) := by
  simp only [kleinFhomAS, map_mul]
  rw [freeMap_kleinBilinAS, freeMap_kleinSecAS, freeMap_kleinStereoAS]

/-- Naturality of the target equation `kleinGhomAS` of the AS link. -/
theorem freeMap_kleinGhomAS (φ : A →+* B) (a b g : A) (p w : Fin 5 → A) :
    φ (kleinGhomAS a b g p w)
      = kleinGhomAS (φ a) (φ b) (φ g) (fun i => φ (p i)) (fun i => φ (w i)) := by
  simp only [kleinGhomAS, map_mul]
  rw [freeMap_kleinBilinAS, map_kleinRAS_mul_comm, freeMap_kleinSecDualAS]

/-! ## The unit condition, w-free -/

/-- **The unit condition of the AS link, without the auxiliary Artin–Schreier root.**

The statement is the one of `Work.MotAS.KleinLinkUnitAS` with the root `w` of `X⁵ - X - g`
(and the hypothesis `hw : w ^ 5 = w + g`) removed: the identity holds in every commutative ring
with `5 = 0`.  This is the `AdjoinRoot` descent of `KleinLinkUnitAS`. -/
theorem KleinLinkUnitAS_free {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (a b g : R)
    (p v : Fin 5 → R) (hp : kleinQAS a b p = 0) :
    kleinGhomAS a b g p (kleinPAS a b g (kleinStereoAS a b p v))
      = -(kleinSecAS a b g (kleinStereoAS a b p v)) ^ 2 * kleinBilinAS a b p v
          * kleinFhomAS a b g p v := by
  rcases subsingleton_or_nontrivial R with hsub | hnt
  · -- the trivial ring
    haveI : Subsingleton R := hsub
    exact Subsingleton.elim _ _
  · haveI : Nontrivial R := hnt
    -- the universal Artin–Schreier extension `R → S = R[w]/(w⁵ - w - g)`
    let φ : R →+* AdjoinRoot (asGaloisPoly g) := AdjoinRoot.of (asGaloisPoly g)
    let w : AdjoinRoot (asGaloisPoly g) := AdjoinRoot.root (asGaloisPoly g)
    have hw : w ^ 5 = w + φ g := by
      have h : AdjoinRoot.mk (asGaloisPoly g)
          (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) = 0 := AdjoinRoot.mk_self
      simp only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
      linear_combination (norm := first | refl_ring1 | ring1) h
    have h5S : (5 : AdjoinRoot (asGaloisPoly g)) = 0 := by
      rw [show (5 : AdjoinRoot (asGaloisPoly g)) = φ (5 : R) from (map_natCast φ 5).symm]
      rw [h5, map_zero]
    have hφinj : Function.Injective φ :=
      AdjoinRoot.of.injective_of_monic_of_degree_pos (asGaloisPoly_monic g)
        (asGaloisPoly_degree_pos g)
    have hpS : kleinQAS (φ a) (φ b) (fun i => φ (p i)) = 0 := by
      rw [← freeMap_kleinQAS φ a b p, hp, map_zero]
    -- the identity in the universal extension
    have hmain := KleinLinkUnitAS (φ a) (φ b) (φ g) w h5S hw
      (fun i => φ (p i)) (fun i => φ (v i)) hpS
    -- push the statement along `R → S`
    apply hφinj
    simpa only [map_mul, map_neg, map_pow, freeMap_kleinGhomAS, map_kleinPAS_mul_comm,
      freeMap_kleinStereoAS, freeMap_kleinSecAS, freeMap_kleinBilinAS,
      freeMap_kleinFhomAS] using hmain

end Work.MotAS
