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
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

open Work.MotK.TwRuling.SdWfour

variable {R : Type*} [CommRing R]


theorem cPAS_sum {S : Type*} [CommRing S] (a b g : S) (y : Fin 5 → S) (k : Fin 5) :
    (∑ q : Fin 5 × Fin 3, cPAS a b g k q * (y (pfA q) * y (pfB q))) = kleinPAS a b g y k := by
  fin_cases k <;>
  · rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_five, Fin.sum_univ_three, pfA_zero, pfB_zero, pfA_one, pfB_one,
      pfA_two, pfB_two]
    simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceMul, Fin.reduceAdd, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Matrix.of_apply,
      cPAS, cPASmat, kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4]
    first | refl_ring1 | ring

end Work.MotAS
