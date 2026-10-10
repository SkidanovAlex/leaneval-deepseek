import Mathlib
import Submission.Work.MotAS.AsRuleQAAex
import Submission.Work.MotAS.AsRuleQACtri
import Submission.Work.MotAS.AsRuleQATri1
import Submission.Work.MotAS.AsRuleQATri2
import Submission.Work.MotAS.AsRuleQATri3
import Submission.Work.MotAS.AsRuleQATri4
import Submission.Work.MotAS.AsRuleQATri5
import Submission.Work.MotAS.AsRuleQATri6
import Submission.Work.MotAS.AsRuleQATri7
import Submission.Work.MotAS.AsRuleQATri8
import Submission.Work.MotAS.AsRuleQATri9
import Submission.Work.MotAS.AsRuleQATri10
import Submission.Work.MotAS.AsRuleQATri11
import Submission.Work.MotAS.AsRuleQATri12
import Submission.Work.MotAS.AsRuleQATri13
import Submission.Work.MotAS.AsRuleQATri14
import Submission.Work.MotAS.AsRuleQATri15
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.Reflect.PolyId

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

noncomputable def asTerms (a b g : K) : Polynomial K :=
    Polynomial.C (asCt1 a b g) * (asAex0 a b g * (asAex0 a b g * asAex0 a b g)) + (Polynomial.C (asCt2 a b g) * (asAex0 a b g * (asAex0 a b g * asAex2 a b g)) + (Polynomial.C (asCt3 a b g) * (asAex0 a b g * (asAex1 a b g * asAex1 a b g)) + (Polynomial.C (asCt4 a b g) * (asAex0 a b g * (asAex1 a b g * asAex3 a b g)) + (Polynomial.C (asCt5 a b g) * (asAex0 a b g * (asAex2 a b g * asAex2 a b g)) + (Polynomial.C (asCt6 a b g) * (asAex0 a b g * (asAex2 a b g * asAex3 a b g)) + (Polynomial.C (asCt7 a b g) * (asAex0 a b g * (asAex3 a b g * asAex3 a b g)) + (Polynomial.C (asCt8 a b g) * (asAex1 a b g * (asAex1 a b g * asAex3 a b g)) + (Polynomial.C (asCt9 a b g) * (asAex1 a b g * (asAex2 a b g * asAex2 a b g)) + (Polynomial.C (asCt10 a b g) * (asAex1 a b g * (asAex2 a b g * asAex3 a b g)) + (Polynomial.C (asCt11 a b g) * (asAex1 a b g * (asAex3 a b g * asAex3 a b g)) + (Polynomial.C (asCt12 a b g) * (asAex2 a b g * (asAex2 a b g * asAex2 a b g)) + (Polynomial.C (asCt13 a b g) * (asAex2 a b g * (asAex2 a b g * asAex3 a b g)) + (Polynomial.C (asCt14 a b g) * (asAex2 a b g * (asAex3 a b g * asAex3 a b g)) + (Polynomial.C (asCt15 a b g) * (asAex3 a b g * (asAex3 a b g * asAex3 a b g))))))))))))))))

noncomputable def asRterms (a b g : K) : Polynomial K :=
    Polynomial.C (asCt1 a b g) * asTriR1 a b g + (Polynomial.C (asCt2 a b g) * asTriR2 a b g + (Polynomial.C (asCt3 a b g) * asTriR3 a b g + (Polynomial.C (asCt4 a b g) * asTriR4 a b g + (Polynomial.C (asCt5 a b g) * asTriR5 a b g + (Polynomial.C (asCt6 a b g) * asTriR6 a b g + (Polynomial.C (asCt7 a b g) * asTriR7 a b g + (Polynomial.C (asCt8 a b g) * asTriR8 a b g + (Polynomial.C (asCt9 a b g) * asTriR9 a b g + (Polynomial.C (asCt10 a b g) * asTriR10 a b g + (Polynomial.C (asCt11 a b g) * asTriR11 a b g + (Polynomial.C (asCt12 a b g) * asTriR12 a b g + (Polynomial.C (asCt13 a b g) * asTriR13 a b g + (Polynomial.C (asCt14 a b g) * asTriR14 a b g + (Polynomial.C (asCt15 a b g) * asTriR15 a b g))))))))))))))

noncomputable def asPhiP (a b g : K) : Polynomial K := asRterms a b g

theorem hdivAll (a b g : K) :
    (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣ asTerms a b g - asRterms a b g := by
  have hD1 := hdiv1 a b g
  have hD2 := hdiv2 a b g
  have hD3 := hdiv3 a b g
  have hD4 := hdiv4 a b g
  have hD5 := hdiv5 a b g
  have hD6 := hdiv6 a b g
  have hD7 := hdiv7 a b g
  have hD8 := hdiv8 a b g
  have hD9 := hdiv9 a b g
  have hD10 := hdiv10 a b g
  have hD11 := hdiv11 a b g
  have hD12 := hdiv12 a b g
  have hD13 := hdiv13 a b g
  have hD14 := hdiv14 a b g
  have hD15 := hdiv15 a b g
  have hsum : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣
      (Polynomial.C (asCt1 a b g) * (asAex0 a b g * (asAex0 a b g * asAex0 a b g)) - Polynomial.C (asCt1 a b g) * asTriR1 a b g) + ((Polynomial.C (asCt2 a b g) * (asAex0 a b g * (asAex0 a b g * asAex2 a b g)) - Polynomial.C (asCt2 a b g) * asTriR2 a b g) + ((Polynomial.C (asCt3 a b g) * (asAex0 a b g * (asAex1 a b g * asAex1 a b g)) - Polynomial.C (asCt3 a b g) * asTriR3 a b g) + ((Polynomial.C (asCt4 a b g) * (asAex0 a b g * (asAex1 a b g * asAex3 a b g)) - Polynomial.C (asCt4 a b g) * asTriR4 a b g) + ((Polynomial.C (asCt5 a b g) * (asAex0 a b g * (asAex2 a b g * asAex2 a b g)) - Polynomial.C (asCt5 a b g) * asTriR5 a b g) + ((Polynomial.C (asCt6 a b g) * (asAex0 a b g * (asAex2 a b g * asAex3 a b g)) - Polynomial.C (asCt6 a b g) * asTriR6 a b g) + ((Polynomial.C (asCt7 a b g) * (asAex0 a b g * (asAex3 a b g * asAex3 a b g)) - Polynomial.C (asCt7 a b g) * asTriR7 a b g) + ((Polynomial.C (asCt8 a b g) * (asAex1 a b g * (asAex1 a b g * asAex3 a b g)) - Polynomial.C (asCt8 a b g) * asTriR8 a b g) + ((Polynomial.C (asCt9 a b g) * (asAex1 a b g * (asAex2 a b g * asAex2 a b g)) - Polynomial.C (asCt9 a b g) * asTriR9 a b g) + ((Polynomial.C (asCt10 a b g) * (asAex1 a b g * (asAex2 a b g * asAex3 a b g)) - Polynomial.C (asCt10 a b g) * asTriR10 a b g) + ((Polynomial.C (asCt11 a b g) * (asAex1 a b g * (asAex3 a b g * asAex3 a b g)) - Polynomial.C (asCt11 a b g) * asTriR11 a b g) + ((Polynomial.C (asCt12 a b g) * (asAex2 a b g * (asAex2 a b g * asAex2 a b g)) - Polynomial.C (asCt12 a b g) * asTriR12 a b g) + ((Polynomial.C (asCt13 a b g) * (asAex2 a b g * (asAex2 a b g * asAex3 a b g)) - Polynomial.C (asCt13 a b g) * asTriR13 a b g) + ((Polynomial.C (asCt14 a b g) * (asAex2 a b g * (asAex3 a b g * asAex3 a b g)) - Polynomial.C (asCt14 a b g) * asTriR14 a b g) + ((Polynomial.C (asCt15 a b g) * (asAex3 a b g * (asAex3 a b g * asAex3 a b g)) - Polynomial.C (asCt15 a b g) * asTriR15 a b g))))))))))))))) := by
    exact dvd_add hD1 (dvd_add hD2 (dvd_add hD3 (dvd_add hD4 (dvd_add hD5 (dvd_add hD6 (dvd_add hD7 (dvd_add hD8 (dvd_add hD9 (dvd_add hD10 (dvd_add hD11 (dvd_add hD12 (dvd_add hD13 (dvd_add hD14 (hD15))))))))))))))
  have hEq : asTerms a b g - asRterms a b g =
      (Polynomial.C (asCt1 a b g) * (asAex0 a b g * (asAex0 a b g * asAex0 a b g)) - Polynomial.C (asCt1 a b g) * asTriR1 a b g) + ((Polynomial.C (asCt2 a b g) * (asAex0 a b g * (asAex0 a b g * asAex2 a b g)) - Polynomial.C (asCt2 a b g) * asTriR2 a b g) + ((Polynomial.C (asCt3 a b g) * (asAex0 a b g * (asAex1 a b g * asAex1 a b g)) - Polynomial.C (asCt3 a b g) * asTriR3 a b g) + ((Polynomial.C (asCt4 a b g) * (asAex0 a b g * (asAex1 a b g * asAex3 a b g)) - Polynomial.C (asCt4 a b g) * asTriR4 a b g) + ((Polynomial.C (asCt5 a b g) * (asAex0 a b g * (asAex2 a b g * asAex2 a b g)) - Polynomial.C (asCt5 a b g) * asTriR5 a b g) + ((Polynomial.C (asCt6 a b g) * (asAex0 a b g * (asAex2 a b g * asAex3 a b g)) - Polynomial.C (asCt6 a b g) * asTriR6 a b g) + ((Polynomial.C (asCt7 a b g) * (asAex0 a b g * (asAex3 a b g * asAex3 a b g)) - Polynomial.C (asCt7 a b g) * asTriR7 a b g) + ((Polynomial.C (asCt8 a b g) * (asAex1 a b g * (asAex1 a b g * asAex3 a b g)) - Polynomial.C (asCt8 a b g) * asTriR8 a b g) + ((Polynomial.C (asCt9 a b g) * (asAex1 a b g * (asAex2 a b g * asAex2 a b g)) - Polynomial.C (asCt9 a b g) * asTriR9 a b g) + ((Polynomial.C (asCt10 a b g) * (asAex1 a b g * (asAex2 a b g * asAex3 a b g)) - Polynomial.C (asCt10 a b g) * asTriR10 a b g) + ((Polynomial.C (asCt11 a b g) * (asAex1 a b g * (asAex3 a b g * asAex3 a b g)) - Polynomial.C (asCt11 a b g) * asTriR11 a b g) + ((Polynomial.C (asCt12 a b g) * (asAex2 a b g * (asAex2 a b g * asAex2 a b g)) - Polynomial.C (asCt12 a b g) * asTriR12 a b g) + ((Polynomial.C (asCt13 a b g) * (asAex2 a b g * (asAex2 a b g * asAex3 a b g)) - Polynomial.C (asCt13 a b g) * asTriR13 a b g) + ((Polynomial.C (asCt14 a b g) * (asAex2 a b g * (asAex3 a b g * asAex3 a b g)) - Polynomial.C (asCt14 a b g) * asTriR14 a b g) + ((Polynomial.C (asCt15 a b g) * (asAex3 a b g * (asAex3 a b g * asAex3 a b g)) - Polynomial.C (asCt15 a b g) * asTriR15 a b g))))))))))))))) := by
    rw [asTerms, asRterms]
    first | refl_ring1 | ring
  rwa [hEq]

end Work.MotAS
