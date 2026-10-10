import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.KleinTwI2I4ASBGuide
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.asTransportSD
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotAS.AsTransportSDstage
import Submission.Work.MotK.KleinIdents

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The AS link identity I2 (dual secant), `w`-free form

`Work.MotAS.KleinTwI2ASb` is the *w-free* form (valid in an arbitrary `CommRing R` with
`(5 : R) = 0`) of the Artin--Schreier link identity

`P^AS(R^AS(z)) = s'^AS(z) • z`,

the image of the split Crauder--Katz identity `Work.MotK.kleinP_kleinR`
(`kleinP a b (kleinR a b z) = fun i => kleinSecDual a b z * z i`, proved for every `CommRing`)
under the Galois-coordinate substitutions `x = asM w · y` and `z = asN w · ẑ` in characteristic `5`.

## Proof

* `KleinTwI2ASb_vec` proves the identity in any ring containing an element `w` with
  `w ^ 5 = w + g`: apply the split identity to the vector `asN w · z`, use
  `asTransportR` (`R(asN w · z) = asM w · R^AS(z)`), `asTransportP`
  (`p(asM w · y) = asN w · p^AS(y)`) and `AsTransportSDstage`
  (`s'(asN w · z) = s'^AS(z)`), then cancel the injective Vandermonde matrix `asN w`.
* The target ring `R` need not contain such a `w`, so the identity is first proved in the
  universal extension `AdjoinRoot (X^5 - X - C g)` and then descended along the (injective)
  structure map, using the naturality lemmas `KleinTwScalarAS_map_kleinPAS`,
  `KleinTwScalarAS_map_kleinRAS` and `KleinTwI2ASb_sdNaturality`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Polynomial

namespace Work.MotAS

/-- Naturality of the twisted dual secant quintic `s'^AS` under a ring homomorphism
(every monomial of `kleinSecDualAS` has integer coefficients). -/
theorem KleinTwI2ASb_sdNaturality {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (a b g : A) (z : Fin 5 → A) :
    kleinSecDualAS (φ a) (φ b) (φ g) (fun j => φ (z j)) = φ (kleinSecDualAS a b g z) := by
  simp only [kleinSecDualAS, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast]

/-- **The AS link identity I2 in a ring containing a fifth root of `X^5 - X - g`.** -/
theorem KleinTwI2ASb_vec {A : Type*} [CommRing A] (a b g w : A) (h5 : (5 : A) = 0)
    (hw : w ^ 5 = w + g) (z : Fin 5 → A) :
    kleinPAS a b g (kleinRAS a b g z) = fun i => kleinSecDualAS a b g z * z i := by
  have hP : Work.MotK.kleinP a b ((asM w).mulVec (kleinRAS a b g z))
      = (asN w).mulVec (kleinPAS a b g (kleinRAS a b g z)) :=
    asTransportP a b g w h5 hw (kleinRAS a b g z)
  have hR : Work.MotK.kleinR a b ((asN w).mulVec z) = (asM w).mulVec (kleinRAS a b g z) :=
    asTransportR a b g w h5 hw z
  have hSD : Work.MotK.kleinSecDual a b ((asN w).mulVec z) = kleinSecDualAS a b g z :=
    AsTransportSDstage a b g w h5 hw z
  have hsplit : Work.MotK.kleinP a b (Work.MotK.kleinR a b ((asN w).mulVec z))
      = Work.MotK.kleinSecDual a b ((asN w).mulVec z) • ((asN w).mulVec z) := by
    funext i
    simpa only [Pi.smul_apply, smul_eq_mul] using
      Work.MotK.kleinP_kleinR a b ((asN w).mulVec z) i
  have hkey : (asN w).mulVec (kleinPAS a b g (kleinRAS a b g z))
      = (asN w).mulVec (kleinSecDualAS a b g z • z) := by
    rw [← hP, ← hR, hsplit, hSD, Matrix.mulVec_smul]
  have hvec := asN_mulVec_injective h5 w hkey
  funext i
  simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hvec i

theorem KleinTwI2ASb {R : Type*} [CommRing R] (a b g : R) (z : Fin 5 → R) (h5 : (5 : R) = 0) :
    kleinPAS a b g (kleinRAS a b g z) = fun i => kleinSecDualAS a b g z * z i := by
  by_cases hone : (1 : R) = 0
  · -- the trivial ring
    haveI : Subsingleton R := ⟨fun x y => by
      have hx : x = 0 := by rw [← mul_one x, hone, mul_zero]
      have hy : y = 0 := by rw [← one_mul y, hone, zero_mul]
      rw [hx, hy]⟩
    exact Subsingleton.elim _ _
  · haveI : Nontrivial R := ⟨0, 1, fun h => hone h.symm⟩
    -- the universal extension `R[w]/(w^5 - w - g)`
    set p : Polynomial R := Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g with hpdef
    have hpmonic : p.Monic := by
      rw [hpdef, show (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial R)
        = Polynomial.X ^ 5 - (Polynomial.X + Polynomial.C g) by ring]
      refine Polynomial.monic_X_pow_sub ?_
      calc ((Polynomial.X + Polynomial.C g : Polynomial R).degree)
          ≤ max (Polynomial.X : Polynomial R).degree (Polynomial.C g : Polynomial R).degree :=
            Polynomial.degree_add_le _ _
        _ ≤ max (1 : WithBot ℕ) 0 := max_le_max Polynomial.degree_X_le Polynomial.degree_C_le
        _ = 1 := max_eq_left (WithBot.coe_le_coe.mpr (Nat.zero_le 1))
        _ < (5 : WithBot ℕ) := WithBot.coe_lt_coe.mpr (by norm_num)
    have hcoeff : p.coeff 5 = 1 := by
      rw [hpdef]
      simp [Polynomial.coeff_X_pow_self, Polynomial.coeff_X, Polynomial.coeff_C]
    have hdeg : (0 : WithBot ℕ) < p.degree :=
      lt_of_lt_of_le (WithBot.coe_lt_coe.mpr (by norm_num : (0 : ℕ) < 5))
        (Polynomial.le_degree_of_ne_zero (by rw [hcoeff]; exact hone))
    have hinj : Function.Injective (algebraMap R (AdjoinRoot p)) :=
      AdjoinRoot.of.injective_of_monic_of_degree_pos hpmonic hdeg
    have hw : (AdjoinRoot.root p) ^ 5 = AdjoinRoot.root p + algebraMap R (AdjoinRoot p) g := by
      have h : (AdjoinRoot.root p) ^ 5 - AdjoinRoot.root p - algebraMap R (AdjoinRoot p) g = 0 := by
        have h := AdjoinRoot.eval₂_root p
        simpa only [hpdef, AdjoinRoot.algebraMap_eq, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C] using h
      have h4 : (AdjoinRoot.root p) ^ 5 - AdjoinRoot.root p = algebraMap R (AdjoinRoot p) g :=
        sub_eq_zero.mp h
      calc (AdjoinRoot.root p) ^ 5
          = ((AdjoinRoot.root p) ^ 5 - AdjoinRoot.root p) + AdjoinRoot.root p :=
            (sub_add_cancel _ _).symm
        _ = algebraMap R (AdjoinRoot p) g + AdjoinRoot.root p := by rw [h4]
        _ = AdjoinRoot.root p + algebraMap R (AdjoinRoot p) g := by rw [add_comm]
    have h5A : (5 : AdjoinRoot p) = 0 := by
      have h' : algebraMap R (AdjoinRoot p) (5 : R) = 0 := by rw [h5, map_zero]
      rw [← map_ofNat (algebraMap R (AdjoinRoot p)) 5]
      exact h'
    -- the identity in the universal extension
    have hmain := KleinTwI2ASb_vec (algebraMap R (AdjoinRoot p) a) (algebraMap R (AdjoinRoot p) b)
      (algebraMap R (AdjoinRoot p) g) (AdjoinRoot.root p) h5A hw
      (fun j => algebraMap R (AdjoinRoot p) (z j))
    -- push the identity back along `R → AdjoinRoot p`
    funext i
    apply hinj
    have h0 := congrFun hmain i
    simp only [KleinTwScalarAS_map_kleinPAS, KleinTwScalarAS_map_kleinRAS,
      KleinTwI2ASb_sdNaturality] at h0
    simpa only [map_mul] using h0

end Work.MotAS
