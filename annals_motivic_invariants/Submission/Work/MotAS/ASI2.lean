import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASLink
import Submission.Work.MotAS.ASI1Ratio
import Submission.Work.MotAS.KleinTwI3AS

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The AS link identity `I2^AS`: `P^AS (R^AS z) = s'^AS(z) · z`

Part of `Submission/Work/MotAS` (`Work.MotAS`), the characteristic-`5` (Artin--Schreier) branch of
the Crauder--Katz chart of H.-Y. Lin and E. Shinder, *Motivic invariants of birational maps*,
Ann. of Math. **199** (2024).

The identity is first proved in the universal Artin--Schreier extension
`S = AdjoinRoot (X^5 - X - g)` of `R`, where the transported split Klein--Fisher identity
`kleinPAS_kleinRAS` (`Submission/Work/MotAS/ASLink.lean`, obtained from `asTransportP`,
`asTransportR` and the split `KleinIdents.kleinP_kleinR` after cancelling the invertible matrix
`asN w`) applies, and is then pushed back along the injective structure map `R → S`
(`AdjoinRoot.of.injective_of_monic_of_degree_pos`), using the naturality of `kleinPAS`, `kleinRAS`
and `kleinSecDualAS` under ring homomorphisms.  This is the same descent scheme as the one used for
`Work.MotAS.ASI1Ratio`.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Work.MotAS

/-- **`I2^AS`**: `P^AS (R^AS z) = s'^AS(z) · z` in every commutative ring with `5 = 0`. -/
theorem ASI2 {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (a b g : R) (z : Fin 5 → R) :
    kleinPAS a b g (kleinRAS a b g z) = fun i => kleinSecDualAS a b g z * z i := by
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
    have hgen := kleinPAS_kleinRAS (AdjoinRoot.of (ASI1Aux.ASpoly g) a)
      (AdjoinRoot.of (ASI1Aux.ASpoly g) b) (AdjoinRoot.of (ASI1Aux.ASpoly g) g)
      (AdjoinRoot.root (ASI1Aux.ASpoly g)) h5S hw
      (fun k => AdjoinRoot.of (ASI1Aux.ASpoly g) (z k))
    rw [ASI1Aux.map_kleinRAS (AdjoinRoot.of (ASI1Aux.ASpoly g)) a b g z,
        ASI1Aux.map_kleinPAS (AdjoinRoot.of (ASI1Aux.ASpoly g)) a b g (kleinRAS a b g z),
        KleinTwI3AS_map_kleinSecDualAS (AdjoinRoot.of (ASI1Aux.ASpoly g)) a b g z] at hgen
    funext i
    refine AdjoinRoot.of.injective_of_monic_of_degree_pos (ASI1Aux.ASpoly_monic g)
      (ASI1Aux.ASpoly_degree_pos g) ?_
    have hi := congrFun hgen i
    simpa only [map_mul] using hi

end Work.MotAS
