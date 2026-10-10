import Mathlib
import Submission.Work.MotAS.CubASDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.MotAS

/-! `P^AS` and `R^AS` are the AS-coordinate quadro-cubic map and its inverse. The *projective*
(ratio) part of `R^AS ∘ P^AS = s·id` is:

Suggested proof (no big `ring` certificate): let `S = AdjoinRoot (Polynomial.X^5 - Polynomial.X - Polynomial.C g)`
over `R` and `w = AdjoinRoot.root _`, so `w^5 = w + g` and `5 = 0` in `S`; then with
`ξ := fun i => ∑ j, asM w i j * y j`: `asTransportP` gives
`kleinP a b ξ = fun i => ∑ j, asN w i j * kleinPAS a b g y j`; `kleinR_kleinP`
(`Work.MotK.KleinIdents`) gives `kleinR a b (kleinP a b ξ) = fun i => kleinSec a b ξ * ξ i`;
`asTransportR` gives `kleinR a b (fun i => ∑ j, asN w i j * kleinPAS a b g y j)
= (asM w).mulVec (kleinRAS a b g (kleinPAS a b g y))`.  Hence
`(asM w).mulVec (kleinRAS ... ) = fun i => kleinSec a b ξ * ξ i`, and `asM_mulVec_injective`
(using `isUnit_288`) cancels `asM w`, giving `kleinRAS ... = fun i => kleinSec a b ξ * y i`.
Multiplying components `i` and `j` by `y j` and `y i` gives the claim in `S`; descend to `R` with
`AdjoinRoot.of.injective_of_monic_of_degree_pos`. -/

/-! ## The Artin--Schreier polynomial and its basic properties -/

/-- The polynomial `X⁵ - X - g` whose root is the Artin--Schreier element `w`. -/
noncomputable def asGaloisPoly {R : Type*} [CommRing R] (g : R) : Polynomial R :=
  Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g

theorem asGaloisPoly_monic {R : Type*} [CommRing R] [Nontrivial R] (g : R) :
    (asGaloisPoly g).Monic := by
  have h : Polynomial.degree ((Polynomial.X + Polynomial.C g : Polynomial R)) < (5 : WithBot ℕ) := by
    rw [Polynomial.degree_X_add_C]; norm_num
  rw [asGaloisPoly, show Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g
        = Polynomial.X ^ 5 - ((Polynomial.X + Polynomial.C g : Polynomial R)) from by ring]
  exact Polynomial.monic_X_pow_sub h

theorem asGaloisPoly_degree_pos {R : Type*} [CommRing R] [Nontrivial R] (g : R) :
    0 < (asGaloisPoly g).degree := by
  have h : Polynomial.degree ((Polynomial.X + Polynomial.C g : Polynomial R)) < (5 : WithBot ℕ) := by
    rw [Polynomial.degree_X_add_C]; norm_num
  have h2 : Polynomial.degree ((Polynomial.X + Polynomial.C g : Polynomial R)) <
      (Polynomial.X ^ 5 : Polynomial R).degree := by
    rw [Polynomial.degree_X_pow]; exact h
  rw [asGaloisPoly, show Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g
        = Polynomial.X ^ 5 - ((Polynomial.X + Polynomial.C g : Polynomial R)) from by ring,
      Polynomial.degree_sub_eq_left_of_degree_lt h2, Polynomial.degree_X_pow]
  norm_num

/-! ## Compatibility of the AS data with ring homomorphisms -/

/-- Naturality of `kleinPAS` under a ring homomorphism.

Name note: this is the `kleinPAS`-naturality statement **of this module**; the same statement
(oriented the other way) is `Work.MotAS.map_kleinPAS` in `Submission/Work/MotAS/KleinTwProjAS.lean`.
The two used to share the name, which made it impossible to import both modules at once; this copy
carries the `_mul_comm` suffix. -/
theorem map_kleinPAS_mul_comm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    (fun i => φ (kleinPAS a b g y i)) = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (y i)) := by
  funext i
  fin_cases i <;>
    simp [kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4, map_ofNat]

/-- Naturality of `kleinRAS` under a ring homomorphism (see the name note on
`map_kleinPAS_mul_comm`). -/
theorem map_kleinRAS_mul_comm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (z : Fin 5 → R) :
    (fun i => φ (kleinRAS a b g z i)) = kleinRAS (φ a) (φ b) (φ g) (fun i => φ (z i)) := by
  funext i
  fin_cases i <;>
    simp [kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4, map_ofNat]

/-! ## The projective part of `R^AS ∘ P^AS = s·id` -/

theorem kleinRAS_kleinPAS_mul_comm {R : Type*} [CommRing R] (h5 : (5 : R) = 0)
    (a b g : R) (y : Fin 5 → R) (i j : Fin 5) :
    kleinRAS a b g (kleinPAS a b g y) i * y j = kleinRAS a b g (kleinPAS a b g y) j * y i := by
  rcases subsingleton_or_nontrivial R with hsub | hnt
  · haveI : Subsingleton R := hsub
    exact Subsingleton.elim _ _
  · haveI : Nontrivial R := hnt
    let φ : R →+* AdjoinRoot (asGaloisPoly g) := AdjoinRoot.of (asGaloisPoly g)
    let w : AdjoinRoot (asGaloisPoly g) := AdjoinRoot.root (asGaloisPoly g)
    let ζ : Fin 5 → AdjoinRoot (asGaloisPoly g) := fun i => φ (y i)
    let ξ : Fin 5 → AdjoinRoot (asGaloisPoly g) := fun i => ∑ j, asM w i j * ζ j
    have hw : w ^ 5 = w + φ g := by
      have h : AdjoinRoot.mk (asGaloisPoly g)
          (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) = 0 := AdjoinRoot.mk_self
      simp only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
      linear_combination (norm := refl_ring1) h
    have h5S : (5 : AdjoinRoot (asGaloisPoly g)) = 0 := by
      rw [show (5 : AdjoinRoot (asGaloisPoly g)) = AdjoinRoot.of (asGaloisPoly g) (5 : R) from
        (map_natCast (AdjoinRoot.of (asGaloisPoly g)) 5).symm]
      rw [h5, map_zero]
    have hφinj : Function.Injective φ :=
      AdjoinRoot.of.injective_of_monic_of_degree_pos (asGaloisPoly_monic g)
        (asGaloisPoly_degree_pos g)
    have hA : Work.MotK.kleinP (φ a) (φ b) ξ =
        (asN w).mulVec (kleinPAS (φ a) (φ b) (φ g) ζ) :=
      asTransportP (φ a) (φ b) (φ g) w h5S hw ζ
    have hB : Work.MotK.kleinR (φ a) (φ b) (Work.MotK.kleinP (φ a) (φ b) ξ) =
        fun i => Work.MotK.kleinSec (φ a) (φ b) ξ * ξ i := by
      funext i
      exact Work.MotK.kleinR_kleinP (φ a) (φ b) ξ i
    have hC : Work.MotK.kleinR (φ a) (φ b) ((asN w).mulVec (kleinPAS (φ a) (φ b) (φ g) ζ)) =
        (asM w).mulVec (kleinRAS (φ a) (φ b) (φ g) (kleinPAS (φ a) (φ b) (φ g) ζ)) :=
      asTransportR (φ a) (φ b) (φ g) w h5S hw (kleinPAS (φ a) (φ b) (φ g) ζ)
    have hmain : (asM w).mulVec
          (kleinRAS (φ a) (φ b) (φ g) (kleinPAS (φ a) (φ b) (φ g) ζ)) =
        fun i => Work.MotK.kleinSec (φ a) (φ b) ξ * ξ i := by
      rw [← hC, ← hA]
      exact hB
    have key2 : (asM w).mulVec (fun i => Work.MotK.kleinSec (φ a) (φ b) ξ * ζ i) =
        fun i => Work.MotK.kleinSec (φ a) (φ b) ξ * ξ i := by
      have h1 : (fun i => Work.MotK.kleinSec (φ a) (φ b) ξ * ζ i) =
          Work.MotK.kleinSec (φ a) (φ b) ξ • ζ := by
        funext i; rfl
      rw [h1, Matrix.mulVec_smul]
      have h2 : (asM w).mulVec ζ = ξ := rfl
      rw [h2]
      funext i; rfl
    have hvv : kleinRAS (φ a) (φ b) (φ g) (kleinPAS (φ a) (φ b) (φ g) ζ) =
        fun i => Work.MotK.kleinSec (φ a) (φ b) ξ * ζ i :=
      asM_mulVec_injective h5S w (hmain.trans key2.symm)
    have hSid : ∀ i j, kleinRAS (φ a) (φ b) (φ g) (kleinPAS (φ a) (φ b) (φ g) ζ) i * ζ j =
        kleinRAS (φ a) (φ b) (φ g) (kleinPAS (φ a) (φ b) (φ g) ζ) j * ζ i := by
      intro i j
      rw [hvv]
      first | refl_ring1 | ring
    have hPAS : (fun k => φ (kleinPAS a b g y k)) = kleinPAS (φ a) (φ b) (φ g) ζ :=
      map_kleinPAS_mul_comm φ a b g y
    have hRAS : (fun k => φ (kleinRAS a b g (kleinPAS a b g y) k)) =
        kleinRAS (φ a) (φ b) (φ g) (kleinPAS (φ a) (φ b) (φ g) ζ) := by
      rw [← hPAS]
      exact map_kleinRAS_mul_comm φ a b g (kleinPAS a b g y)
    have hRi := congrFun hRAS i
    have hRj := congrFun hRAS j
    apply hφinj
    rw [map_mul, map_mul, hRi, hRj]
    exact hSid i j

end Work.MotAS
