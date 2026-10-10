import Submission.Work.MotC5N3.SatCert2.K3_defs
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

lemma zdec3 (a b g : K) :
    Work.MotAS.zcubAS a b g 3 = f30 a b g + f31 a b g * X 0 + f32 a b g * X 0 ^ 2 + f33 a b g * X 0 ^ 3 := by
  simp only [Work.MotAS.zcubAS, Work.MotAS.kleinRAS, Work.MotAS.kleinRAS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, fd30_0, fd30_1, fd30_2, fd30_3, fd30_4, f30, fd31_0, fd31_1, fd31_2, f31, fd32_0, f32, fd33_0, f33, sd3_0, sd3_1, sd3_2, sd3_3, sd3_4, S3,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat,
    MvPolynomial.C_add, MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_neg,
    MvPolynomial.C_sub]
  first | refl_ring1 | ring

end Work.MotC5N3
