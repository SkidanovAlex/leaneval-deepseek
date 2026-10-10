import Mathlib
import Submission.Work.MotAS.WitPt
import Submission.Work.MotAS.asRuleMinP_isHomogeneous
import Submission.Work.MotAS.witCert
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.witValue`

The value of the AS `(0,1)`-minor `Work.MotAS.asRuleMinP a b g` at the witness point
`Work.MotAS.witPt a b`:

`asRuleMinP a b g (witPt a b) = (X⁵ − X − g) · witH a b g + witPhi a b g`

This is an explicit polynomial identity in `K[a,b,g][X]` for `K` a field of characteristic `5`.

## Proof

* `asRuleMinP` is the `(0,1)`-minor `asRuleQA · 1 * asRuleQB · 0 − asRuleQA · 0 * asRuleQB · 1`
  of the two AS ruling vectors (`Work.MotAS.asRuleMinP_eq`), and `MvPolynomial.aeval`
  commutes with the ruling vectors (`Work.MotAS.aeval_asRuleQX`, `Work.MotAS.aeval_asRuleQBX`).
* Each of the four evaluations `asRuleQA (C a) (C b) (C g) (witPt a b) i`,
  `asRuleQB (C a) (C b) (C g) (witPt a b) i` (`i = 0,1`) is a concrete polynomial in `a,b,g,X`;
  the explicit values are the certificates `witA1, witA0, witB0, witB1` of
  `Submission/Work/MotAS/witCert.lean`.  Each equality is a *quadratic-form-at-a-point* identity
  and is closed by `ring`.
* The final identity

  `witA1 * witB0 - witA0 * witB1 - ((X⁵ − X − C g) * witH + witPhi) = 5 * witZ`

  is an identity over `ℤ` between explicit polynomials (the cofactor `witZ` is also in
  `witCert.lean`), proved by `ring`.  Since `(5 : Polynomial K) = 0` by `CharP K 5`, the left side
  vanishes.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

open MvPolynomial Polynomial

theorem witValue (K : Type) [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.aeval (Work.MotAS.witPt a b) (Work.MotAS.asRuleMinP a b g)
      = (Polynomial.X^5 - Polynomial.X - Polynomial.C g) * Work.MotAS.witH a b g
        + Work.MotAS.witPhi a b g := by
  rw [asRuleMinP_eq]
  simp only [map_sub, map_mul]
  rw [aeval_asRuleQX, aeval_asRuleQBX, aeval_asRuleQX, aeval_asRuleQBX]
  simp only [Polynomial.algebraMap_eq]
  have hA1 : asRuleQA (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) (witPt a b) 1
      = witA1 a b g := by
    unfold asRuleQA asPolarP asTanQ kleinBilinAS kleinQAS kleinPAS kleinPAS0 kleinPAS1
      kleinPAS2 kleinPAS3 kleinPAS4 Work.MotK.kleinE witPt
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ',
      Pi.single_apply, Pi.add_apply]
    simp (config := { decide := true })
    simp only [map_ofNat, map_zero, map_one, map_neg, map_sub, map_add, map_mul, map_pow]
    unfold witA1
    refl_ring1
  have hB0 : asRuleQB (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) (witPt a b) 0
      = witB0 a b g := by
    unfold asRuleQB asPolarP asTanQ kleinBilinAS kleinQAS kleinPAS kleinPAS0 kleinPAS1
      kleinPAS2 kleinPAS3 kleinPAS4 Work.MotK.kleinE witPt
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ',
      Pi.single_apply, Pi.add_apply]
    simp (config := { decide := true })
    simp only [map_ofNat, map_zero, map_one, map_neg, map_sub, map_add, map_mul, map_pow]
    unfold witB0
    refl_ring1
  have hA0 : asRuleQA (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) (witPt a b) 0
      = witA0 a b g := by
    unfold asRuleQA asPolarP asTanQ kleinBilinAS kleinQAS kleinPAS kleinPAS0 kleinPAS1
      kleinPAS2 kleinPAS3 kleinPAS4 Work.MotK.kleinE witPt
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ',
      Pi.single_apply, Pi.add_apply]
    simp (config := { decide := true })
    simp only [map_ofNat, map_zero, map_one, map_neg, map_sub, map_add, map_mul, map_pow]
    unfold witA0
    refl_ring1
  have hB1 : asRuleQB (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) (witPt a b) 1
      = witB1 a b g := by
    unfold asRuleQB asPolarP asTanQ kleinBilinAS kleinQAS kleinPAS kleinPAS0 kleinPAS1
      kleinPAS2 kleinPAS3 kleinPAS4 Work.MotK.kleinE witPt
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ',
      Pi.single_apply, Pi.add_apply]
    simp (config := { decide := true })
    simp only [map_ofNat, map_zero, map_one, map_neg, map_sub, map_add, map_mul, map_pow]
    unfold witB1
    refl_ring1
  rw [hA1, hB0, hA0, hB1]
  have hZ : witA1 a b g * witB0 a b g - witA0 a b g * witB1 a b g
      - ((Polynomial.X^5 - Polynomial.X - Polynomial.C g) * witH a b g + witPhi a b g)
      = 5 * witZ a b g := by
    unfold witA1 witB0 witA0 witB1 witZ witZ_0 witZ_1 witZ_2 witZ_3 witZ_4 witZ_5 witZ_6 witZ_7
      witZ_8 witZ_9 witH witPhi
    simp only [map_ofNat, map_zero, map_one, map_neg, map_sub, map_add, map_mul, map_pow]
    refl_ring1
  have h5 : (5 : Polynomial K) = 0 := CharP.cast_eq_zero (Polynomial K) 5
  rw [← sub_eq_zero, hZ, h5, zero_mul]

end Work.MotAS
