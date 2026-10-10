import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.aszDpQuad
import Submission.Work.MotAS.ZiasGraphData
import Submission.Work.MotC5N3.ASZPrimeness.DpQuadNoHab

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASRulV2M

theorem ZiasLeSpanPQG (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    Work.MotAS.ZIAS a b g ≤ Ideal.span
      ({MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g),
       (MvPolynomial.X 0 : MvPolynomial (Fin 3) K) ^ 2
         + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
             * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g))
           * MvPolynomial.X 0
         + MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
             * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g),
       MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
           * MvPolynomial.X 0
         + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)} :
        Set (MvPolynomial (Fin 3) K)) := by sorry

end Work.MotAS.ASRulV2M
