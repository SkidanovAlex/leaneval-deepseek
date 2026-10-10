import Submission.Work.MotC5N3.SatCert.K0_defs
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotC5N3
open MvPolynomial

variable {K : Type} [Field K] [CharP K 5]

lemma zdec0 (a b g : K) :
    Work.MotAS.zcubAS a b g 0 = f00 a b g + f01 a b g * X 0 + f02 a b g * X 0 ^ 2 := by
  simp only [Work.MotAS.zcubAS, Work.MotAS.kleinRAS, Work.MotAS.kleinRAS0,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, f00, f01, f02,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat,
    MvPolynomial.C_add, MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_neg,
    MvPolynomial.C_sub]
  first | refl_ring1 | ring

end Work.MotC5N3
