import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.MotAS.KleinTwI2I4ASBGuide

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open Polynomial

namespace Work.MotAS

/-- **I1^AS, full vector form.**  This is the statement of `Work.MotAS.KleinTwScalarAS` for all
five components at once.  The proof is the one of `KleinTwScalarAS` with the final
`congrFun … 0` removed: everything (the transported split identity `KleinTwScalarAS_vec`, the
`AdjoinRoot` descent, the naturality lemmas) is already component-uniform. -/
theorem KleinTwScalarASv {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) (h5 : (5 : R) = 0) :
    kleinRAS a b g (kleinPAS a b g y) = fun i => kleinSecAS a b g y * y i := by
  by_cases hone : (1 : R) = 0
  · -- the trivial ring
    haveI : Subsingleton R := ⟨fun x y => by
      have hx : x = 0 := by rw [← mul_one x, hone, mul_zero]
      have hy : y = 0 := by rw [← one_mul y, hone, zero_mul]
      rw [hx, hy]⟩
    funext i
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
    have hmain := KleinTwScalarAS_vec (algebraMap R (AdjoinRoot p) a)
      (algebraMap R (AdjoinRoot p) b) (algebraMap R (AdjoinRoot p) g) (AdjoinRoot.root p) h5A hw
      (fun j => algebraMap R (AdjoinRoot p) (y j))
    -- push the identity back along `R → AdjoinRoot p`, componentwise
    funext i
    apply hinj
    have hi := congrFun hmain i
    simp only [KleinTwScalarAS_map_kleinPAS, KleinTwScalarAS_map_kleinRAS,
      KleinTwScalarAS_map_kleinSecAS] at hi
    rw [map_mul]
    simpa only [Pi.smul_apply, smul_eq_mul] using hi

end Work.MotAS
