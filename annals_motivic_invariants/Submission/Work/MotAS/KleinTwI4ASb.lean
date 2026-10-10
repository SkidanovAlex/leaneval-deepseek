import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.KleinTwI2I4ASBGuide
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.MotK.KleinI4
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.AsTransportSstage
import Submission.Work.MotAS.AsTransportSDstage

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# I4^AS: `s^AS (R^AS z) = s'^AS(z)³`

The target `Work.MotAS.KleinTwI4ASb` is the Artin--Schreier (characteristic `5`) form of the
Klein--Fisher link identity `s ∘ R = (s')³`.  The proof below goes through the *proved* split
identity `Work.MotK.KleinI4` (valid over every `CommRing`) and the three proved transports:

* `Work.MotAS.asTransportR` : `R (asN w · z) = asM w · R^AS z`,
* `Work.MotAS.AsTransportSstage` : `s (asM w · y) = s^AS y`,
* `Work.MotAS.AsTransportSDstage` : `s' (asN w · z) = s'^AS z`,

in a ring containing an element `w` with `w ^ 5 = w + g` (`w` is the reduction parameter of the
Artin--Schreier coordinates; `5 = 0` is needed for all three).  This yields the identity in such a
ring (`KleinTwI4ASb_of_root`); the general case is obtained by passing to the universal extension
`R → AdjoinRoot (X^5 - X - g)` — the Artin--Schreier extension in which the parameter `g` acquires
a root — and descending along the injective structure map.

The hypothesis `hI2` of the statement (`P^AS(R^AS z) = s'^AS(z) • z`) is *not* needed: the
identity holds unconditionally in characteristic `5`.  It is kept because the statement is fixed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open Polynomial

namespace Work.MotAS

/-- Naturality of the AS dual secant quintic under an arbitrary ring homomorphism. -/
lemma KleinTwI4ASb_map_kleinSecDualAS {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (z : Fin 5 → R) :
    φ (kleinSecDualAS a b g z) = kleinSecDualAS (φ a) (φ b) (φ g) (fun i => φ (z i)) := by
  simp only [kleinSecDualAS, map_add, map_sub, map_mul, map_pow, map_ofNat]

/-- **I4^AS in a ring admitting a root `w` of `X ^ 5 - X - g`.**

Composition of the three Artin--Schreier transports with the split Klein--Fisher identity
`Work.MotK.KleinI4` (`s (R x) = s' (x)³`), all evaluated at the vector `asN w · z`:

`kleinSecAS (kleinRAS z) = kleinSec (asM w · kleinRAS z) = kleinSec (kleinR (asN w · z))
= kleinSecDual (asN w · z)³ = kleinSecDualAS(z)³`. -/
theorem KleinTwI4ASb_of_root {A : Type*} [CommRing A] (a b g w : A) (h5 : (5 : A) = 0)
    (hw : w ^ 5 = w + g) (z : Fin 5 → A) :
    kleinSecAS a b g (kleinRAS a b g z) = kleinSecDualAS a b g z ^ 3 := by
  have hR : Work.MotK.kleinR a b (fun k => ∑ j, asN w k j * z j)
      = (asM w).mulVec (kleinRAS a b g z) := asTransportR a b g w h5 hw z
  have hS : Work.MotK.kleinSec a b ((asM w).mulVec (kleinRAS a b g z))
      = kleinSecAS a b g (kleinRAS a b g z) :=
    AsTransportSstage a b g w h5 hw (kleinRAS a b g z)
  have hSD : Work.MotK.kleinSecDual a b (fun k => ∑ j, asN w k j * z j)
      = kleinSecDualAS a b g z := AsTransportSDstage a b g w h5 hw z
  calc kleinSecAS a b g (kleinRAS a b g z)
      = Work.MotK.kleinSec a b ((asM w).mulVec (kleinRAS a b g z)) := hS.symm
    _ = Work.MotK.kleinSec a b (Work.MotK.kleinR a b (fun k => ∑ j, asN w k j * z j)) := by
          rw [← hR]
    _ = Work.MotK.kleinSecDual a b (fun k => ∑ j, asN w k j * z j) ^ 3 :=
          Work.MotK.KleinI4 a b (fun k => ∑ j, asN w k j * z j)
    _ = kleinSecDualAS a b g z ^ 3 := by rw [hSD]

theorem KleinTwI4ASb {R : Type*} [CommRing R] (a b g : R) (z : Fin 5 → R) (h5 : (5 : R) = 0)
    (hI2 : kleinPAS a b g (kleinRAS a b g z) = fun i => kleinSecDualAS a b g z * z i) :
    kleinSecAS a b g (kleinRAS a b g z) = kleinSecDualAS a b g z ^ 3 := by
  by_cases hone : (1 : R) = 0
  · -- the trivial ring
    haveI : Subsingleton R := ⟨fun x y => by
      have hx : x = 0 := by rw [← mul_one x, hone, mul_zero]
      have hy : y = 0 := by rw [← one_mul y, hone, zero_mul]
      rw [hx, hy]⟩
    exact Subsingleton.elim _ _
  · haveI : Nontrivial R := ⟨0, 1, fun h => hone h.symm⟩
    -- the Artin--Schreier extension `R → S = R[w]/(w^5 - w - g)`
    set p : Polynomial R := X ^ 5 - X - C g with hpdef
    have hpmonic : p.Monic := by
      rw [hpdef, show (X ^ 5 - X - C g : Polynomial R) = X ^ 5 - (X + C g) by ring]
      refine Polynomial.monic_X_pow_sub ?_
      calc ((X + C g : Polynomial R).degree)
          ≤ max (X : Polynomial R).degree (C g : Polynomial R).degree :=
            Polynomial.degree_add_le _ _
        _ ≤ max (1 : WithBot ℕ) 0 := max_le_max Polynomial.degree_X_le Polynomial.degree_C_le
        _ = 1 := max_eq_left (WithBot.coe_le_coe.mpr (Nat.zero_le 1))
        _ < (5 : WithBot ℕ) := WithBot.coe_lt_coe.mpr (by norm_num)
    have hcoeff : p.coeff 5 = 1 := by
      rw [hpdef]
      simp [Polynomial.coeff_X_pow_self, Polynomial.coeff_X, Polynomial.coeff_C]
    have hdeg5 : (5 : WithBot ℕ) ≤ p.degree :=
      Polynomial.le_degree_of_ne_zero (by rw [hcoeff]; exact hone)
    have hw : (AdjoinRoot.root p) ^ 5 = AdjoinRoot.root p + algebraMap R (AdjoinRoot p) g := by
      have h : (AdjoinRoot.root p) ^ 5 - AdjoinRoot.root p - algebraMap R (AdjoinRoot p) g = 0 := by
        have h1 := AdjoinRoot.eval₂_root p
        simpa only [hpdef, AdjoinRoot.algebraMap_eq, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C] using h1
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
    have hinj : Function.Injective (algebraMap R (AdjoinRoot p)) := by
      intro x y hxy
      by_contra hne
      have hCz : Polynomial.C (x - y) ≠ 0 := Polynomial.C_ne_zero.mpr (sub_ne_zero.mpr hne)
      have hdeglt : (Polynomial.C (x - y)).degree < p.degree :=
        lt_of_le_of_lt (Polynomial.degree_C_le)
          (lt_of_lt_of_le (WithBot.coe_lt_coe.mpr (by norm_num : (0 : ℕ) < 5)) hdeg5)
      have hsub : algebraMap R (AdjoinRoot p) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have hmk : AdjoinRoot.mk p (Polynomial.C (x - y)) = 0 := by
        rw [AdjoinRoot.mk_C]
        exact hsub
      rw [AdjoinRoot.mk_eq_zero] at hmk
      exact (hpmonic.not_dvd_of_degree_lt hCz hdeglt) hmk
    -- the identity in the extension
    have key : kleinSecAS (algebraMap R (AdjoinRoot p) a) (algebraMap R (AdjoinRoot p) b)
          (algebraMap R (AdjoinRoot p) g)
          (kleinRAS (algebraMap R (AdjoinRoot p) a) (algebraMap R (AdjoinRoot p) b)
            (algebraMap R (AdjoinRoot p) g) (fun i => algebraMap R (AdjoinRoot p) (z i)))
        = kleinSecDualAS (algebraMap R (AdjoinRoot p) a) (algebraMap R (AdjoinRoot p) b)
            (algebraMap R (AdjoinRoot p) g) (fun i => algebraMap R (AdjoinRoot p) (z i)) ^ 3 :=
      KleinTwI4ASb_of_root (algebraMap R (AdjoinRoot p) a) (algebraMap R (AdjoinRoot p) b)
        (algebraMap R (AdjoinRoot p) g) (AdjoinRoot.root p) h5A hw
        (fun i => algebraMap R (AdjoinRoot p) (z i))
    -- push the identity back along the structure map
    rw [KleinTwScalarAS_map_kleinRAS (algebraMap R (AdjoinRoot p)) a b g z] at key
    rw [KleinTwScalarAS_map_kleinSecAS (algebraMap R (AdjoinRoot p)) a b g
      (kleinRAS a b g z)] at key
    rw [← KleinTwI4ASb_map_kleinSecDualAS (algebraMap R (AdjoinRoot p)) a b g z] at key
    refine hinj ?_
    simpa only [map_pow] using key

end Work.MotAS
