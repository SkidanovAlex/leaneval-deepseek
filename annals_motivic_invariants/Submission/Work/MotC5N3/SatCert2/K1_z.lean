import Submission.Work.MotC5N3.SatCert2.K1_defs
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

lemma zdec1 (a b g : K) :
    Work.MotAS.zcubAS a b g 1 = f10 a b g + f11 a b g * X 0 + f12 a b g * X 0 ^ 2 + f13 a b g * X 0 ^ 3 := by
  simp only [Work.MotAS.zcubAS, Work.MotAS.kleinRAS, Work.MotAS.kleinRAS1,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, fd10_0, fd10_1, fd10_2, fd10_3, fd10_4, fd10_5, fd10_6, f10, fd11_0, fd11_1, fd11_2, fd11_3, f11, fd12_0, f12, fd13_0, f13, sd1_0, sd1_1, sd1_2, sd1_3, sd1_4, S1,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat,
    MvPolynomial.C_add, MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_neg,
    MvPolynomial.C_sub]
  first | refl_ring1 | ring

end Work.MotC5N3
