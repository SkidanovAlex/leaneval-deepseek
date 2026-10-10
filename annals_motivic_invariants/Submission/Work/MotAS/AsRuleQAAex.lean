import Mathlib
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotAS.WitPt
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Generated data for `Work.MotAS.kleinRAS0_asRuleQA_notMem_asIdeal6`. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Work.MotAS

open MvPolynomial Polynomial

variable {K : Type} [Field K] [CharP K 5]

noncomputable def asAex0_c0 (a b g : K) : K :=
    b ^(6:ℕ) +
      2 * a * b ^(5:ℕ) +
      4 * a ^(3:ℕ) * b ^(3:ℕ) +
      a ^(4:ℕ) * b ^(2:ℕ) +
      a ^(5:ℕ) * b +
      4 * a ^(6:ℕ) +
      4 * b ^(6:ℕ) * g +
      a * b ^(5:ℕ) * g +
      2 * a ^(5:ℕ) * b * g +
      3 * a ^(6:ℕ) * g

noncomputable def asAex0_c1 (a b g : K) : K :=
    b ^(6:ℕ) +
      a * b ^(5:ℕ) +
      4 * a ^(2:ℕ) * b ^(4:ℕ) +
      2 * a ^(3:ℕ) * b ^(3:ℕ) +
      2 * a ^(4:ℕ) * b ^(2:ℕ) +
      3 * a ^(5:ℕ) * b +
      b ^(6:ℕ) * g +
      3 * a * b ^(5:ℕ) * g +
      3 * a ^(5:ℕ) * b * g +
      4 * a ^(6:ℕ) * g

noncomputable def asAex0_c2 (a b g : K) : K :=
    3 * b ^(6:ℕ) +
      2 * a * b ^(5:ℕ) +
      a ^(2:ℕ) * b ^(4:ℕ) +
      2 * a ^(3:ℕ) * b ^(3:ℕ) +
      4 * a ^(4:ℕ) * b ^(2:ℕ) +
      2 * a ^(5:ℕ) * b +
      2 * a ^(6:ℕ) +
      3 * b ^(6:ℕ) * g +
      4 * a * b ^(5:ℕ) * g +
      4 * a ^(5:ℕ) * b * g +
      2 * a ^(6:ℕ) * g

noncomputable def asAex0_c3 (a b g : K) : K :=
    b ^(6:ℕ) +
      4 * a * b ^(5:ℕ) +
      2 * a ^(2:ℕ) * b ^(4:ℕ) +
      4 * a ^(3:ℕ) * b ^(3:ℕ) +
      3 * a ^(4:ℕ) * b ^(2:ℕ) +
      4 * a ^(5:ℕ) * b +
      4 * a ^(6:ℕ)

noncomputable def asAex0_c5 (a b g : K) : K :=
    2 * b ^(6:ℕ) +
      4 * a * b ^(5:ℕ) +
      a ^(5:ℕ) * b +
      2 * a ^(6:ℕ)

noncomputable def asAex0 (a b g : K) : Polynomial K :=
    Polynomial.C (asAex0_c0 a b g) + Polynomial.C (asAex0_c1 a b g) * Polynomial.X ^(1:ℕ) + Polynomial.C (asAex0_c2 a b g) * Polynomial.X ^(2:ℕ) + Polynomial.C (asAex0_c3 a b g) * Polynomial.X ^(3:ℕ) + Polynomial.C (asAex0_c5 a b g) * Polynomial.X ^(5:ℕ)

noncomputable def asAex1_c0 (a b g : K) : K :=
    3 * b ^(6:ℕ) +
      a * b ^(5:ℕ) +
      4 * a ^(2:ℕ) * b ^(4:ℕ) +
      4 * a ^(3:ℕ) * b ^(3:ℕ) +
      3 * a ^(5:ℕ) * b +
      4 * a ^(6:ℕ) +
      2 * b ^(6:ℕ) * g +
      a * b ^(5:ℕ) * g +
      a ^(5:ℕ) * b * g +
      3 * a ^(6:ℕ) * g

noncomputable def asAex1_c1 (a b g : K) : K :=
    2 * b ^(6:ℕ) +
      a * b ^(5:ℕ) +
      4 * a ^(2:ℕ) * b ^(4:ℕ) +
      3 * a ^(3:ℕ) * b ^(3:ℕ) +
      a ^(4:ℕ) * b ^(2:ℕ) +
      3 * a ^(5:ℕ) * b +
      2 * a ^(6:ℕ) +
      2 * b ^(6:ℕ) * g +
      a * b ^(5:ℕ) * g +
      a ^(5:ℕ) * b * g +
      3 * a ^(6:ℕ) * g

noncomputable def asAex1_c2 (a b g : K) : K :=
    b ^(6:ℕ) +
      a * b ^(5:ℕ) +
      2 * a ^(2:ℕ) * b ^(4:ℕ) +
      4 * a ^(3:ℕ) * b ^(3:ℕ) +
      3 * a ^(4:ℕ) * b ^(2:ℕ) +
      4 * a ^(5:ℕ) * b

noncomputable def asAex1_c3 (a b g : K) : K :=
    2 * b ^(6:ℕ) +
      4 * a * b ^(5:ℕ) +
      a ^(5:ℕ) * b +
      2 * a ^(6:ℕ)

noncomputable def asAex1_c4 (a b g : K) : K :=
    3 * b ^(6:ℕ) +
      a * b ^(5:ℕ) +
      4 * a ^(5:ℕ) * b +
      3 * a ^(6:ℕ)

noncomputable def asAex1_c5 (a b g : K) : K :=
    4 * b ^(6:ℕ) +
      2 * a * b ^(5:ℕ) +
      2 * a ^(5:ℕ) * b +
      a ^(6:ℕ)

noncomputable def asAex1_c6 (a b g : K) : K :=
    4 * b ^(6:ℕ) +
      2 * a * b ^(5:ℕ) +
      2 * a ^(5:ℕ) * b +
      a ^(6:ℕ)

noncomputable def asAex1 (a b g : K) : Polynomial K :=
    Polynomial.C (asAex1_c0 a b g) + Polynomial.C (asAex1_c1 a b g) * Polynomial.X ^(1:ℕ) + Polynomial.C (asAex1_c2 a b g) * Polynomial.X ^(2:ℕ) + Polynomial.C (asAex1_c3 a b g) * Polynomial.X ^(3:ℕ) + Polynomial.C (asAex1_c4 a b g) * Polynomial.X ^(4:ℕ) + Polynomial.C (asAex1_c5 a b g) * Polynomial.X ^(5:ℕ) + Polynomial.C (asAex1_c6 a b g) * Polynomial.X ^(6:ℕ)

noncomputable def asAex2_c0 (a b g : K) : K :=
    4 * b ^(6:ℕ) +
      3 * a * b ^(5:ℕ) +
      4 * a ^(2:ℕ) * b ^(4:ℕ) +
      3 * a ^(3:ℕ) * b ^(3:ℕ) +
      a ^(4:ℕ) * b ^(2:ℕ) +
      4 * a ^(5:ℕ) * b +
      3 * a ^(6:ℕ) +
      b ^(6:ℕ) * g +
      3 * a * b ^(5:ℕ) * g +
      3 * a ^(5:ℕ) * b * g +
      4 * a ^(6:ℕ) * g

noncomputable def asAex2_c1 (a b g : K) : K :=
    3 * b ^(6:ℕ) +
      3 * a * b ^(5:ℕ) +
      4 * a ^(2:ℕ) * b ^(4:ℕ) +
      3 * a ^(3:ℕ) * b ^(3:ℕ) +
      a ^(4:ℕ) * b ^(2:ℕ) +
      a ^(5:ℕ) * b +
      3 * a ^(6:ℕ)

noncomputable def asAex2_c2 (a b g : K) : K :=
    3 * b ^(6:ℕ) +
      a * b ^(5:ℕ) +
      4 * a ^(5:ℕ) * b +
      3 * a ^(6:ℕ)

noncomputable def asAex2_c3 (a b g : K) : K :=
    b ^(6:ℕ) +
      2 * a * b ^(5:ℕ) +
      3 * a ^(5:ℕ) * b +
      a ^(6:ℕ)

noncomputable def asAex2_c5 (a b g : K) : K :=
    3 * b ^(6:ℕ) +
      4 * a * b ^(5:ℕ) +
      4 * a ^(5:ℕ) * b +
      2 * a ^(6:ℕ)

noncomputable def asAex2 (a b g : K) : Polynomial K :=
    Polynomial.C (asAex2_c0 a b g) + Polynomial.C (asAex2_c1 a b g) * Polynomial.X ^(1:ℕ) + Polynomial.C (asAex2_c2 a b g) * Polynomial.X ^(2:ℕ) + Polynomial.C (asAex2_c3 a b g) * Polynomial.X ^(3:ℕ) + Polynomial.C (asAex2_c5 a b g) * Polynomial.X ^(5:ℕ)

noncomputable def asAex3_c0 (a b g : K) : K :=
    2 * b ^(6:ℕ) +
      4 * a * b ^(5:ℕ) +
      2 * a ^(2:ℕ) * b ^(4:ℕ) +
      4 * a ^(3:ℕ) * b ^(3:ℕ) +
      3 * a ^(4:ℕ) * b ^(2:ℕ) +
      2 * a ^(5:ℕ) * b +
      4 * a ^(6:ℕ)

noncomputable def asAex3_c1 (a b g : K) : K :=
    4 * b ^(6:ℕ) +
      a * b ^(5:ℕ) +
      2 * a ^(5:ℕ) * b +
      3 * a ^(6:ℕ)

noncomputable def asAex3_c2 (a b g : K) : K :=
    2 * a * b ^(5:ℕ) +
      a ^(6:ℕ)

noncomputable def asAex3_c3 (a b g : K) : K :=
    3 * b ^(6:ℕ) +
      4 * a * b ^(5:ℕ) +
      4 * a ^(5:ℕ) * b +
      2 * a ^(6:ℕ)

noncomputable def asAex3_c4 (a b g : K) : K :=
    2 * b ^(6:ℕ) +
      a * b ^(5:ℕ) +
      a ^(5:ℕ) * b +
      3 * a ^(6:ℕ)

noncomputable def asAex3 (a b g : K) : Polynomial K :=
    Polynomial.C (asAex3_c0 a b g) + Polynomial.C (asAex3_c1 a b g) * Polynomial.X ^(1:ℕ) + Polynomial.C (asAex3_c2 a b g) * Polynomial.X ^(2:ℕ) + Polynomial.C (asAex3_c3 a b g) * Polynomial.X ^(3:ℕ) + Polynomial.C (asAex3_c4 a b g) * Polynomial.X ^(4:ℕ)

noncomputable def asAex4 (a b g : K) : Polynomial K :=
    0

lemma haeval_A0 (a b g : K) :
    MvPolynomial.aeval (witPt a b) (qAS_A K a b g 0) = asAex0 a b g := by
  simp (config := { failIfUnchanged := false }) only [qAS_A, asRuleQA, asPolarP, asTanQ, kleinBilinAS, kleinQAS, kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4, Work.MotK.kleinE, witPt, Pi.add_apply]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [asAex0, asAex0_c0, asAex0_c1, asAex0_c2, asAex0_c3, asAex0_c5]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  all_goals refl_ring1 (mod := 5)

lemma haeval_A1 (a b g : K) :
    MvPolynomial.aeval (witPt a b) (qAS_A K a b g 1) = asAex1 a b g := by
  simp (config := { failIfUnchanged := false }) only [qAS_A, asRuleQA, asPolarP, asTanQ, kleinBilinAS, kleinQAS, kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4, Work.MotK.kleinE, witPt, Pi.add_apply]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [asAex1, asAex1_c0, asAex1_c1, asAex1_c2, asAex1_c3, asAex1_c4, asAex1_c5, asAex1_c6]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  all_goals refl_ring1 (mod := 5)

lemma haeval_A2 (a b g : K) :
    MvPolynomial.aeval (witPt a b) (qAS_A K a b g 2) = asAex2 a b g := by
  simp (config := { failIfUnchanged := false }) only [qAS_A, asRuleQA, asPolarP, asTanQ, kleinBilinAS, kleinQAS, kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4, Work.MotK.kleinE, witPt, Pi.add_apply]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [asAex2, asAex2_c0, asAex2_c1, asAex2_c2, asAex2_c3, asAex2_c5]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  all_goals refl_ring1 (mod := 5)

lemma haeval_A3 (a b g : K) :
    MvPolynomial.aeval (witPt a b) (qAS_A K a b g 3) = asAex3 a b g := by
  simp (config := { failIfUnchanged := false }) only [qAS_A, asRuleQA, asPolarP, asTanQ, kleinBilinAS, kleinQAS, kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4, Work.MotK.kleinE, witPt, Pi.add_apply]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [asAex3, asAex3_c0, asAex3_c1, asAex3_c2, asAex3_c3, asAex3_c4]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  all_goals refl_ring1 (mod := 5)

lemma haeval_A4 (a b g : K) :
    MvPolynomial.aeval (witPt a b) (qAS_A K a b g 4) = asAex4 a b g := by
  simp (config := { failIfUnchanged := false }) only [qAS_A, asRuleQA, asPolarP, asTanQ, kleinBilinAS, kleinQAS, kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4, Work.MotK.kleinE, witPt, Pi.add_apply]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [asAex4]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try norm_num
  simp (config := { failIfUnchanged := false }) only [Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  all_goals refl_ring1 (mod := 5)

end Work.MotAS

