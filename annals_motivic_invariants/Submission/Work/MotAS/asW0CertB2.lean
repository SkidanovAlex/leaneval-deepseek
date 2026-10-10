import Mathlib
import Submission.Work.MotAS.asW0Defs
import Submission.Work.MotAS.ASRulDefs
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Work.MotAS

open Work.MotK.TwRuling.SdWfour

/-- The tangent direction `asTanQ · 2` of the AS quadric in explicit form. -/
theorem asW0_asTanQ_two {S : Type*} [CommRing S] (a b : S) (y : Fin 5 → S) :
    asTanQ a b y 2 = ![0, 0,
      2 * ((a ^ 2 - a * b - b ^ 2) * y 0 + (a ^ 2 + b ^ 2) * y 2
        + (2 * a ^ 2 - a * b - 2 * b ^ 2) * y 4), 0,
      -(2 * ((a ^ 2 - a * b - b ^ 2) * y 2 + (a ^ 2 + b ^ 2) * y 4))] := by
  funext i
  fin_cases i <;>
    simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceMul, Fin.reduceAdd, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Matrix.of_apply,
      asTanQ, kleinBilinAS, kleinQAS, Work.MotK.kleinE, Pi.single_apply, Pi.add_apply] <;>
    norm_num <;>
    first | refl_ring1 | ring

/-- **The quadratic form `B` in the fifteen pair monomials.** -/
theorem asW0_cB_sum {S : Type*} [CommRing S] (a b g : S) (y : Fin 5 → S) :
    (∑ q : Fin 5 × Fin 3, cB a b g q * (y (pfA q) * y (pfB q))) = asRuleQB a b g y 0 := by
  simp only [asRuleQB, asPolarP, asW0_asTanQ_two, kleinPAS_apply_zero]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_three, pfA_zero, pfB_zero, pfA_one, pfB_one,
    pfA_two, pfB_two]
  simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceMul, Fin.reduceAdd, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Matrix.of_apply,
    cB, kleinPAS0, Pi.add_apply, Pi.sub_apply]
  first | refl_ring1 | ring

end Work.MotAS
