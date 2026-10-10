import Mathlib
import Submission.Work.MotAS.AsRuleQAAex
import Submission.Work.MotAS.AsRuleQACtri
import Submission.Work.MotAS.AsRuleQACoeff
import Submission.Work.MotAS.WitPt
import Submission.Work.MotAS.witPfaff
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.AsCoeff6Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Work.MotAS

open MvPolynomial Polynomial

variable {K : Type} [Field K] [CharP K 5]

lemma hdecomp_sym (a b g : K) (z : Fin 5 → Polynomial K) (hz : z 4 = 0) :
    kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) z
      = Polynomial.C (asCt1 a b g) * (z 0 * (z 0 * z 0)) + (Polynomial.C (asCt2 a b g) * (z 0 * (z 0 * z 2)) + (Polynomial.C (asCt3 a b g) * (z 0 * (z 1 * z 1)) + (Polynomial.C (asCt4 a b g) * (z 0 * (z 1 * z 3)) + (Polynomial.C (asCt5 a b g) * (z 0 * (z 2 * z 2)) + (Polynomial.C (asCt6 a b g) * (z 0 * (z 2 * z 3)) + (Polynomial.C (asCt7 a b g) * (z 0 * (z 3 * z 3)) + (Polynomial.C (asCt8 a b g) * (z 1 * (z 1 * z 3)) + (Polynomial.C (asCt9 a b g) * (z 1 * (z 2 * z 2)) + (Polynomial.C (asCt10 a b g) * (z 1 * (z 2 * z 3)) + (Polynomial.C (asCt11 a b g) * (z 1 * (z 3 * z 3)) + (Polynomial.C (asCt12 a b g) * (z 2 * (z 2 * z 2)) + (Polynomial.C (asCt13 a b g) * (z 2 * (z 2 * z 3)) + (Polynomial.C (asCt14 a b g) * (z 2 * (z 3 * z 3)) + (Polynomial.C (asCt15 a b g) * (z 3 * (z 3 * z 3)))))))))))))))) := by
  simp only [kleinRAS0, hz,
    asCt1, asCt2, asCt3, asCt4, asCt5, asCt6, asCt7, asCt8, asCt9, asCt10, asCt11, asCt12, asCt13, asCt14, asCt15,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  try norm_num
  try ring

lemma aeval_witPt_kleinRAS0 (a b g : K) (Z : Fin 5 → MvPolynomial (Fin 5) K) :
    MvPolynomial.aeval (witPt a b)
        (kleinRAS0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) Z)
      = kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (fun i => MvPolynomial.aeval (witPt a b) (Z i)) := by
  simp (config := { failIfUnchanged := false }) only [kleinRAS0, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
  try rfl

theorem asValueMod (a b g : K) :
    (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣
      MvPolynomial.aeval (witPt a b)
        (kleinRAS0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fun k => qAS_A K a b g k)) - asPhiP a b g := by
  rw [aeval_witPt_kleinRAS0 a b g (fun k => qAS_A K a b g k)]
  have hz : (fun i => MvPolynomial.aeval (witPt a b) (qAS_A K a b g i)) 4 = 0 := by
    simpa [asAex4] using haeval_A4 a b g
  rw [hdecomp_sym a b g (fun i => MvPolynomial.aeval (witPt a b) (qAS_A K a b g i)) hz]
  rw [haeval_A0, haeval_A1, haeval_A2, haeval_A3]
  have h := hdivAll a b g
  rw [asTerms] at h
  rw [asPhiP]
  exact h

end Work.MotAS
