import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.KleinTwI34ASGuide
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.MotAS.KleinTwProjAS
import Submission.Work.MotAS.KleinTwI2AS
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.AsTransportSstage
import Submission.Work.MotAS.AsTransportSDstage
import Submission.Work.MotK.KleinIdents

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The AS link identity I3^AS  (`s'^AS (P^AS y) = s^AS(y) ^ 2`)

Part of `Submission/Work/MotAS` (`Work.MotAS`), the characteristic-`5` (Artin--Schreier) branch of
the Crauder--Katz chart of H.-Y. Lin and E. Shinder, *Motivic invariants of birational maps*,
Ann. of Math. **199** (2024).

The AS coordinates `kleinPAS`, `kleinRAS`, `kleinSecAS`, `kleinSecDualAS`
(`Submission/Work/MotAS/ASData.lean`) are the images of the *split* Klein--Fisher data of
`Work.MotK` under the Galois-coordinate substitution `x_i = Σ_j y_j (w+i)^j` (source) and
`z_k = Σ_j ẑ_j (w+2k)^j` (target), reduced modulo `w^5 = w + g` and `5 = 0`.

## Proof route

`KleinTwI3AS_vec` is the identity in a ring containing an element `w` with `w^5 = w + g`:
the split identity `KleinIdents.kleinSecDual_kleinP` (`s'(p(x)) = s(x)^2` over *any* `CommRing`),
applied at `x := asM w · y`, transported by `asTransportP` (left), `AsTransportSstage` (right) and
`AsTransportSDstage` (the dual quintic, `s'(asN w · z) = s'^AS(z)`).  The target ring `R` need not
contain such an `w`, so the identity is first proved in the universal extension
`AdjoinRoot (X^5 - X - g)` and pushed back along the injective structure map
`R → AdjoinRoot (X^5 - X - g)` — the same scheme as `Work.MotAS.KleinTwScalarAS`.  The naturality
lemmas `KleinTwScalarAS_map_kleinPAS`, `KleinTwScalarAS_map_kleinSecAS` and
`KleinTwI3AS_map_kleinSecDualAS` make the push-forward explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open Polynomial

namespace Work.MotAS

/-- **I3^AS in a ring containing a root `w` of `X^5 - X - g`.** -/
theorem KleinTwI3AS_vec {A : Type*} [CommRing A] (a b g w : A) (h5 : (5 : A) = 0)
    (hw : w ^ 5 = w + g) (y : Fin 5 → A) :
    kleinSecDualAS a b g (kleinPAS a b g y) = kleinSecAS a b g y ^ 2 := by
  have hP := asTransportP a b g w h5 hw y
  have hP' : (fun k => ∑ j, asN w k j * kleinPAS a b g y j)
      = Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * y j) := by
    rw [hP]
    rfl
  have hSD := AsTransportSDstage a b g w h5 hw (kleinPAS a b g y)
  rw [hP'] at hSD
  rw [Work.MotK.kleinSecDual_kleinP a b (fun i => ∑ j, asM w i j * y j)] at hSD
  rw [AsTransportSstage a b g w h5 hw y] at hSD
  exact hSD.symm

/-- Naturality of the dual secant quintic under a ring homomorphism. -/
theorem KleinTwI3AS_map_kleinSecDualAS {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (a b g : A) (z : Fin 5 → A) :
    kleinSecDualAS (φ a) (φ b) (φ g) (fun j => φ (z j)) = φ (kleinSecDualAS a b g z) := by
  simp only [kleinSecDualAS, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast]
    <;> ring

/-- **I3^AS.**  `s'^AS (P^AS y) = s^AS(y)^2` in every commutative ring with `5 = 0`. -/
theorem KleinTwI3AS {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) (h5 : (5 : R) = 0) :
    kleinSecDualAS a b g (kleinPAS a b g y) = kleinSecAS a b g y ^ 2 := by
  by_cases hone : (1 : R) = 0
  · -- the trivial ring
    haveI : Subsingleton R := ⟨fun x y => by
      have hx : x = 0 := by rw [← mul_one x, hone, mul_zero]
      have hy : y = 0 := by rw [← one_mul y, hone, zero_mul]
      rw [hx, hy]⟩
    exact Subsingleton.elim _ _
  · haveI : Nontrivial R := ⟨0, 1, fun h => hone h.symm⟩
    -- the universal root `w` of `w ^ 5 - w - g`
    set p : Polynomial R := X ^ 5 - X - C g with hpdef
    have hpmonic : p.Monic := by
      rw [hpdef, show (X ^ 5 - X - C g : Polynomial R) = X ^ 5 - (X + C g) by ring]
      refine Polynomial.monic_X_pow_sub ?_
      calc ((X + C g : Polynomial R).degree)
          ≤ max (X : Polynomial R).degree (C g : Polynomial R).degree := Polynomial.degree_add_le _ _
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
    -- injectivity of the structure map `R → R[X]/(X^5 - X - g)`
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
    -- the identity in the universal extension
    have hmain := KleinTwI3AS_vec (algebraMap R (AdjoinRoot p) a)
      (algebraMap R (AdjoinRoot p) b) (algebraMap R (AdjoinRoot p) g) (AdjoinRoot.root p)
      h5A hw (fun j => algebraMap R (AdjoinRoot p) (y j))
    rw [KleinTwScalarAS_map_kleinPAS] at hmain
    rw [KleinTwI3AS_map_kleinSecDualAS] at hmain
    rw [KleinTwScalarAS_map_kleinSecAS] at hmain
    rw [← map_pow] at hmain
    -- push the identity back along `R → AdjoinRoot p`
    exact hinj hmain

end Work.MotAS
