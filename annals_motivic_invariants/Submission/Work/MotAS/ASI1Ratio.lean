import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotK.KleinIdents
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# The projective (ratio) form of the AS link identity `I1^AS`

`Work.MotAS.ASI1Ratio`: the composite `R^AS ∘ P^AS` of the AS-coordinate quadro-cubic map and
its inverse is a scalar multiple of the identity, in cross-multiplied (ratio) form.

The proof follows the route recorded in `KleinTwProjASGuide.lean`: transport the *given* data to
the universal Artin--Schreier extension `S = R[w]/(w^5 - w - g)`, use the two transported
identities `asTransportP` / `asTransportR` together with the split Klein--Fisher identity
`kleinR_kleinP`, cancel the invertible matrix `asM w` (`asM_mulVec_injective`), and descend to
`R` along the injection `R ↪ S` (`AdjoinRoot.of.injective_of_monic_of_degree_pos`).

The auxiliary lemmas live in the nested namespace `Work.MotAS.ASI1Aux` so that importing this
module cannot collide with the identically-named ring-hom naturality lemmas proved elsewhere in
`Submission/Work/MotAS`.
-/

namespace Work.MotAS

namespace ASI1Aux

/-- The Artin--Schreier polynomial `X^5 - X - g`. -/
noncomputable def ASpoly {R : Type*} [CommRing R] (g : R) : Polynomial R :=
  Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g

theorem ASpoly_monic {R : Type*} [CommRing R] [Nontrivial R] (g : R) : (ASpoly g).Monic := by
  rw [ASpoly]
  have h1 : (Polynomial.X : Polynomial R) ^ 5 - Polynomial.X - Polynomial.C g
      = Polynomial.X ^ 5 + (-(Polynomial.X) - Polynomial.C g) := by ring
  rw [h1]
  apply Polynomial.monic_X_pow_add
  compute_degree!

theorem ASpoly_degree_pos {R : Type*} [CommRing R] [Nontrivial R] (g : R) :
    0 < (ASpoly g).degree := by
  have hmon : (ASpoly g).Monic := ASpoly_monic g
  have hnd : (ASpoly g).natDegree = 5 := by rw [ASpoly]; compute_degree!
  rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hnd]
  norm_num

/-! ## Ring-hom naturality of the transported AS data -/

theorem map_kleinPAS0 {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinPAS0 (φ a) (φ b) (φ g) (fun k => φ (y k)) = φ (kleinPAS0 a b g y) := by
  simp only [kleinPAS0, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinPAS1 {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinPAS1 (φ a) (φ b) (φ g) (fun k => φ (y k)) = φ (kleinPAS1 a b g y) := by
  simp only [kleinPAS1, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinPAS2 {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinPAS2 (φ a) (φ b) (φ g) (fun k => φ (y k)) = φ (kleinPAS2 a b g y) := by
  simp only [kleinPAS2, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinPAS3 {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinPAS3 (φ a) (φ b) (φ g) (fun k => φ (y k)) = φ (kleinPAS3 a b g y) := by
  simp only [kleinPAS3, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinPAS4 {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinPAS4 (φ a) (φ b) (φ g) (fun k => φ (y k)) = φ (kleinPAS4 a b g y) := by
  simp only [kleinPAS4, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinPAS {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinPAS (φ a) (φ b) (φ g) (fun k => φ (y k)) = fun k => φ (kleinPAS a b g y k) := by
  funext k
  fin_cases k
  · exact map_kleinPAS0 φ a b g y
  · exact map_kleinPAS1 φ a b g y
  · exact map_kleinPAS2 φ a b g y
  · exact map_kleinPAS3 φ a b g y
  · exact map_kleinPAS4 φ a b g y

theorem map_kleinRAS0 {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinRAS0 (φ a) (φ b) (φ g) (fun k => φ (y k)) = φ (kleinRAS0 a b g y) := by
  simp only [kleinRAS0, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinRAS1 {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinRAS1 (φ a) (φ b) (φ g) (fun k => φ (y k)) = φ (kleinRAS1 a b g y) := by
  simp only [kleinRAS1, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinRAS2 {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinRAS2 (φ a) (φ b) (φ g) (fun k => φ (y k)) = φ (kleinRAS2 a b g y) := by
  simp only [kleinRAS2, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinRAS3 {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinRAS3 (φ a) (φ b) (φ g) (fun k => φ (y k)) = φ (kleinRAS3 a b g y) := by
  simp only [kleinRAS3, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinRAS4 {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinRAS4 (φ a) (φ b) (φ g) (fun k => φ (y k)) = φ (kleinRAS4 a b g y) := by
  simp only [kleinRAS4, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinRAS {R : Type*} [CommRing R] {S : Type*} [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    kleinRAS (φ a) (φ b) (φ g) (fun k => φ (y k)) = fun k => φ (kleinRAS a b g y k) := by
  funext k
  fin_cases k
  · exact map_kleinRAS0 φ a b g y
  · exact map_kleinRAS1 φ a b g y
  · exact map_kleinRAS2 φ a b g y
  · exact map_kleinRAS3 φ a b g y
  · exact map_kleinRAS4 φ a b g y

/-! ## The generic (root-present) ratio identity -/

/-- The projective link identity `I1^AS` in a ring in which the Artin--Schreier polynomial
`X^5 - X - g` has an explicit root `w` (`w^5 = w + g`).  The conclusion is `w`-free. -/
theorem ASI1Ratio_generic {R : Type*} [CommRing R] (h5 : (5 : R) = 0)
    (a b g w : R) (hw : w ^ 5 = w + g) (y : Fin 5 → R) (i j : Fin 5) :
    kleinRAS a b g (kleinPAS a b g y) i * y j
      = kleinRAS a b g (kleinPAS a b g y) j * y i := by
  set c : R := Work.MotK.kleinSec a b (fun i => ∑ j, asM w i j * y j) with hc
  have hP : Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * y j)
      = (asN w).mulVec (kleinPAS a b g y) := asTransportP a b g w h5 hw y
  have hR : Work.MotK.kleinR a b ((asN w).mulVec (kleinPAS a b g y))
      = (asM w).mulVec (kleinRAS a b g (kleinPAS a b g y)) :=
    asTransportR a b g w h5 hw (kleinPAS a b g y)
  have key : (asM w).mulVec (kleinRAS a b g (kleinPAS a b g y))
      = fun k => c * ∑ j, asM w k j * y j := by
    rw [← hR, ← hP]
    funext k
    rw [hc]
    exact Work.MotK.kleinR_kleinP a b (fun i => ∑ j, asM w i j * y j) k
  have hscale : (asM w).mulVec (fun k => c * y k)
      = fun k => c * ∑ j, asM w k j * y j := by
    funext k
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    first | refl_ring1 | ring
  have hcancel : kleinRAS a b g (kleinPAS a b g y) = fun k => c * y k := by
    apply asM_mulVec_injective h5 w
    rw [key, hscale]
  rw [hcancel]
  first | refl_ring1 | ring

end ASI1Aux

/-! ## Descent to `R` -/

theorem ASI1Ratio {R : Type*} [CommRing R] (h5 : (5 : R) = 0)
    (a b g : R) (y : Fin 5 → R) (i j : Fin 5) :
    Work.MotAS.kleinRAS a b g (Work.MotAS.kleinPAS a b g y) i * y j
      = Work.MotAS.kleinRAS a b g (Work.MotAS.kleinPAS a b g y) j * y i := by
  by_cases hR : Subsingleton R
  · exact Subsingleton.elim _ _
  · haveI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
    have hw : (AdjoinRoot.root (ASI1Aux.ASpoly g)) ^ 5
        = AdjoinRoot.root (ASI1Aux.ASpoly g) + AdjoinRoot.of (ASI1Aux.ASpoly g) g := by
      have h0 : (AdjoinRoot.mk (ASI1Aux.ASpoly g)) (ASI1Aux.ASpoly g) = 0 := AdjoinRoot.mk_self
      rw [ASI1Aux.ASpoly] at h0
      simp only [map_sub, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X] at h0
      show (AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g)) ^ 5
          = AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g)
            + AdjoinRoot.of (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) g
      have h1 : (AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g)) ^ 5
            - AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g)
          = AdjoinRoot.of (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) g :=
        sub_eq_zero.mp h0
      rw [← h1]
      abel
    have h5S : (5 : AdjoinRoot (ASI1Aux.ASpoly g)) = 0 := by
      rw [show (5 : AdjoinRoot (ASI1Aux.ASpoly g))
            = (AdjoinRoot.of (ASI1Aux.ASpoly g)) (5 : R) from
          (map_ofNat (AdjoinRoot.of (ASI1Aux.ASpoly g)) 5).symm, h5, map_zero]
    have hgen := ASI1Aux.ASI1Ratio_generic (R := AdjoinRoot (ASI1Aux.ASpoly g)) h5S
      (AdjoinRoot.of (ASI1Aux.ASpoly g) a) (AdjoinRoot.of (ASI1Aux.ASpoly g) b)
      (AdjoinRoot.of (ASI1Aux.ASpoly g) g)
      (AdjoinRoot.root (ASI1Aux.ASpoly g)) hw (fun k => AdjoinRoot.of (ASI1Aux.ASpoly g) (y k)) i j
    have hPAS : kleinPAS (AdjoinRoot.of (ASI1Aux.ASpoly g) a) (AdjoinRoot.of (ASI1Aux.ASpoly g) b)
          (AdjoinRoot.of (ASI1Aux.ASpoly g) g) (fun k => AdjoinRoot.of (ASI1Aux.ASpoly g) (y k))
        = fun k => AdjoinRoot.of (ASI1Aux.ASpoly g) (kleinPAS a b g y k) :=
      ASI1Aux.map_kleinPAS (AdjoinRoot.of (ASI1Aux.ASpoly g)) a b g y
    have hA : kleinRAS (AdjoinRoot.of (ASI1Aux.ASpoly g) a) (AdjoinRoot.of (ASI1Aux.ASpoly g) b)
          (AdjoinRoot.of (ASI1Aux.ASpoly g) g)
          (kleinPAS (AdjoinRoot.of (ASI1Aux.ASpoly g) a) (AdjoinRoot.of (ASI1Aux.ASpoly g) b)
            (AdjoinRoot.of (ASI1Aux.ASpoly g) g) (fun k => AdjoinRoot.of (ASI1Aux.ASpoly g) (y k)))
        = fun k => AdjoinRoot.of (ASI1Aux.ASpoly g) (kleinRAS a b g (kleinPAS a b g y) k) := by
      rw [hPAS]
      exact ASI1Aux.map_kleinRAS (AdjoinRoot.of (ASI1Aux.ASpoly g)) a b g (kleinPAS a b g y)
    rw [hA] at hgen
    exact (AdjoinRoot.of.injective_of_monic_of_degree_pos
        (ASI1Aux.ASpoly_monic g) (ASI1Aux.ASpoly_degree_pos g))
      (by simpa only [map_mul] using hgen)

end Work.MotAS
