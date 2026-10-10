import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZGC.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASRulV2M

theorem ann_eq_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    ∀ s : MvPolynomial (Fin 2) K,
      (∃ u v : MvPolynomial (Fin 2) K,
        s * Work.MotAS.ASZGC.R0 a b g
          = u * Work.MotAS.ASZElim.P a b g + v * Work.MotAS.ASZGC.D0 a b g) →
      s ∈ Ideal.span {Work.MotAS.ASZElim.P a b g, Work.MotAS.ASZGC.D0 a b g,
        Work.MotAS.ASZGC.R0 a b g} := by sorry

end Work.MotAS.ASRulV2M
