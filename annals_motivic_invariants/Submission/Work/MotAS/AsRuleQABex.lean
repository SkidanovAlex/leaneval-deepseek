import Mathlib
import Submission.Work.MotAS.AsRuleQAAex
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Work.MotAS

open MvPolynomial Polynomial

variable {K : Type} [Field K] [CharP K 5]

noncomputable def asBex0 (a b g : K) : Polynomial K :=
    Polynomial.C (b ^(6:ℕ) + 2 * a * b ^(5:ℕ) + 4 * a ^(3:ℕ) * b ^(3:ℕ) + a ^(4:ℕ) * b ^(2:ℕ) + a ^(5:ℕ) * b + 4 * a ^(6:ℕ) + 6 * b ^(6:ℕ) * g + 5 * a * b ^(5:ℕ) * g + 3 * a ^(5:ℕ) * b * g + 5 * a ^(6:ℕ) * g) + Polynomial.C (3 * b ^(6:ℕ) + 5 * a * b ^(5:ℕ) + 4 * a ^(2:ℕ) * b ^(4:ℕ) + 2 * a ^(3:ℕ) * b ^(3:ℕ) + 2 * a ^(4:ℕ) * b ^(2:ℕ) + 4 * a ^(5:ℕ) * b + 2 * a ^(6:ℕ) + b ^(6:ℕ) * g + 3 * a * b ^(5:ℕ) * g + 3 * a ^(5:ℕ) * b * g + 4 * a ^(6:ℕ) * g) * Polynomial.X ^(1:ℕ) + Polynomial.C (3 * b ^(6:ℕ) + 2 * a * b ^(5:ℕ) + a ^(2:ℕ) * b ^(4:ℕ) + 2 * a ^(3:ℕ) * b ^(3:ℕ) + 4 * a ^(4:ℕ) * b ^(2:ℕ) + 2 * a ^(5:ℕ) * b + 2 * a ^(6:ℕ) + 3 * b ^(6:ℕ) * g + 4 * a * b ^(5:ℕ) * g + 4 * a ^(5:ℕ) * b * g + 2 * a ^(6:ℕ) * g) * Polynomial.X ^(2:ℕ) + Polynomial.C (b ^(6:ℕ) + 4 * a * b ^(5:ℕ) + 2 * a ^(2:ℕ) * b ^(4:ℕ) + 4 * a ^(3:ℕ) * b ^(3:ℕ) + 3 * a ^(4:ℕ) * b ^(2:ℕ) + 4 * a ^(5:ℕ) * b + 4 * a ^(6:ℕ)) * Polynomial.X ^(3:ℕ)

noncomputable def asE0 (a b g : K) : Polynomial K :=
    Polynomial.C (2 * b ^(6:ℕ) + 4 * a * b ^(5:ℕ) + a ^(5:ℕ) * b + 2 * a ^(6:ℕ))

noncomputable def asBex1 (a b g : K) : Polynomial K :=
    Polynomial.C (3 * b ^(6:ℕ) + a * b ^(5:ℕ) + 4 * a ^(2:ℕ) * b ^(4:ℕ) + 4 * a ^(3:ℕ) * b ^(3:ℕ) + 3 * a ^(5:ℕ) * b + 4 * a ^(6:ℕ) + 6 * b ^(6:ℕ) * g + 3 * a * b ^(5:ℕ) * g + 3 * a ^(5:ℕ) * b * g + 4 * a ^(6:ℕ) * g) + Polynomial.C (6 * b ^(6:ℕ) + 3 * a * b ^(5:ℕ) + 4 * a ^(2:ℕ) * b ^(4:ℕ) + 3 * a ^(3:ℕ) * b ^(3:ℕ) + a ^(4:ℕ) * b ^(2:ℕ) + 5 * a ^(5:ℕ) * b + 3 * a ^(6:ℕ) + 6 * b ^(6:ℕ) * g + 3 * a * b ^(5:ℕ) * g + 3 * a ^(5:ℕ) * b * g + 4 * a ^(6:ℕ) * g) * Polynomial.X ^(1:ℕ) + Polynomial.C (5 * b ^(6:ℕ) + 3 * a * b ^(5:ℕ) + 2 * a ^(2:ℕ) * b ^(4:ℕ) + 4 * a ^(3:ℕ) * b ^(3:ℕ) + 3 * a ^(4:ℕ) * b ^(2:ℕ) + 6 * a ^(5:ℕ) * b + a ^(6:ℕ)) * Polynomial.X ^(2:ℕ) + Polynomial.C (2 * b ^(6:ℕ) + 4 * a * b ^(5:ℕ) + a ^(5:ℕ) * b + 2 * a ^(6:ℕ)) * Polynomial.X ^(3:ℕ) + Polynomial.C (3 * b ^(6:ℕ) + a * b ^(5:ℕ) + 4 * a ^(5:ℕ) * b + 3 * a ^(6:ℕ)) * Polynomial.X ^(4:ℕ)

noncomputable def asE1 (a b g : K) : Polynomial K :=
    Polynomial.C (4 * b ^(6:ℕ) + 2 * a * b ^(5:ℕ) + 2 * a ^(5:ℕ) * b + a ^(6:ℕ)) + Polynomial.C (4 * b ^(6:ℕ) + 2 * a * b ^(5:ℕ) + 2 * a ^(5:ℕ) * b + a ^(6:ℕ)) * Polynomial.X ^(1:ℕ)

noncomputable def asBex2 (a b g : K) : Polynomial K :=
    Polynomial.C (4 * b ^(6:ℕ) + 3 * a * b ^(5:ℕ) + 4 * a ^(2:ℕ) * b ^(4:ℕ) + 3 * a ^(3:ℕ) * b ^(3:ℕ) + a ^(4:ℕ) * b ^(2:ℕ) + 4 * a ^(5:ℕ) * b + 3 * a ^(6:ℕ) + 4 * b ^(6:ℕ) * g + 7 * a * b ^(5:ℕ) * g + 7 * a ^(5:ℕ) * b * g + 6 * a ^(6:ℕ) * g) + Polynomial.C (6 * b ^(6:ℕ) + 7 * a * b ^(5:ℕ) + 4 * a ^(2:ℕ) * b ^(4:ℕ) + 3 * a ^(3:ℕ) * b ^(3:ℕ) + a ^(4:ℕ) * b ^(2:ℕ) + 5 * a ^(5:ℕ) * b + 5 * a ^(6:ℕ)) * Polynomial.X ^(1:ℕ) + Polynomial.C (3 * b ^(6:ℕ) + a * b ^(5:ℕ) + 4 * a ^(5:ℕ) * b + 3 * a ^(6:ℕ)) * Polynomial.X ^(2:ℕ) + Polynomial.C (b ^(6:ℕ) + 2 * a * b ^(5:ℕ) + 3 * a ^(5:ℕ) * b + a ^(6:ℕ)) * Polynomial.X ^(3:ℕ)

noncomputable def asE2 (a b g : K) : Polynomial K :=
    Polynomial.C (3 * b ^(6:ℕ) + 4 * a * b ^(5:ℕ) + 4 * a ^(5:ℕ) * b + 2 * a ^(6:ℕ))

noncomputable def asBex3 (a b g : K) : Polynomial K :=
    Polynomial.C (2 * b ^(6:ℕ) + 4 * a * b ^(5:ℕ) + 2 * a ^(2:ℕ) * b ^(4:ℕ) + 4 * a ^(3:ℕ) * b ^(3:ℕ) + 3 * a ^(4:ℕ) * b ^(2:ℕ) + 2 * a ^(5:ℕ) * b + 4 * a ^(6:ℕ)) + Polynomial.C (4 * b ^(6:ℕ) + a * b ^(5:ℕ) + 2 * a ^(5:ℕ) * b + 3 * a ^(6:ℕ)) * Polynomial.X ^(1:ℕ) + Polynomial.C (2 * a * b ^(5:ℕ) + a ^(6:ℕ)) * Polynomial.X ^(2:ℕ) + Polynomial.C (3 * b ^(6:ℕ) + 4 * a * b ^(5:ℕ) + 4 * a ^(5:ℕ) * b + 2 * a ^(6:ℕ)) * Polynomial.X ^(3:ℕ) + Polynomial.C (2 * b ^(6:ℕ) + a * b ^(5:ℕ) + a ^(5:ℕ) * b + 3 * a ^(6:ℕ)) * Polynomial.X ^(4:ℕ)

noncomputable def asE3 (a b g : K) : Polynomial K :=
    0

noncomputable def asBex4 (a b g : K) : Polynomial K := 0
noncomputable def asE4 (a b g : K) : Polynomial K := 0

lemma hred0 (a b g : K) :
    asAex0 a b g = asBex0 a b g
      + (Polynomial.X ^(5:ℕ) - Polynomial.X - Polynomial.C g) * asE0 a b g := by
  simp only [asBex0, asE0, asAex0_c0, asAex0_c1, asAex0_c2, asAex0_c3, asAex0_c5, asAex0,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  first | refl_ring1 | ring

lemma hred1 (a b g : K) :
    asAex1 a b g = asBex1 a b g
      + (Polynomial.X ^(5:ℕ) - Polynomial.X - Polynomial.C g) * asE1 a b g := by
  simp only [asBex1, asE1, asAex1_c0, asAex1_c1, asAex1_c2, asAex1_c3, asAex1_c4, asAex1_c5, asAex1_c6, asAex1,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  first | refl_ring1 | ring

lemma hred2 (a b g : K) :
    asAex2 a b g = asBex2 a b g
      + (Polynomial.X ^(5:ℕ) - Polynomial.X - Polynomial.C g) * asE2 a b g := by
  simp only [asBex2, asE2, asAex2_c0, asAex2_c1, asAex2_c2, asAex2_c3, asAex2_c5, asAex2,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  first | refl_ring1 | ring

lemma hred3 (a b g : K) :
    asAex3 a b g = asBex3 a b g
      + (Polynomial.X ^(5:ℕ) - Polynomial.X - Polynomial.C g) * asE3 a b g := by
  simp only [asBex3, asE3, asAex3_c0, asAex3_c1, asAex3_c2, asAex3_c3, asAex3_c4, asAex3,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  first | refl_ring1 | ring

lemma hred4 (a b g : K) :
    asAex4 a b g = asBex4 a b g
      + (Polynomial.X ^(5:ℕ) - Polynomial.X - Polynomial.C g) * asE4 a b g := by
  simp only [asBex4, asE4, asAex4,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  first | refl_ring1 | ring

end Work.MotAS
