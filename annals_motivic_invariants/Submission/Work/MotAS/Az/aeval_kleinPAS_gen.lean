import Mathlib
import Submission.Work.MotAS.azThetaDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.Az

/-- `aeval` commutes with the AS Pfaffian map `kleinPAS` (the AS analogue of
`Work.MotK.TGen.aeval_kleinTwP_gen` in `Submission/Work/MotK/TGen/AevalFwPoly.lean`).
Route: `fin_cases j`, unfold `kleinPAS, kleinPAS0, ..., kleinPAS4`, push `aeval` through
`+ − * ^` with `map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, MvPolynomial.aeval_C`,
then `ring` (or `ring_nf`).  Note: here the polynomial-variable type is `σ` while the vector index
is `Fin 5` (they coincide in the MotK analogue), so the simp set may need
`Fin.reduceFinMk, Fin.isValue` in addition to `Matrix.cons_val_zero, Matrix.cons_val_one,
Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
Matrix.tail_cons`.  Raise `maxHeartbeats` if needed. -/
theorem aeval_kleinPAS_gen {K A σ : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a b g : K) (U : Fin 5 → MvPolynomial σ K) (y : σ → A) (j : Fin 5) :
    MvPolynomial.aeval y
        ((Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) U) j)
      = Work.MotAS.kleinPAS (algebraMap K A a) (algebraMap K A b) (algebraMap K A g)
          (fun i => MvPolynomial.aeval y (U i)) j := by
  fin_cases j <;>
    simp only [kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      map_add, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.aeval_C]

end Work.MotAS.Az
