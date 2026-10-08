import Mathlib
import Submission.Work.Coherence.Inner

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Coherence

theorem cfInner_expand_zsmul {G : Type*} [Fintype G] (a b c d : G → ℂ) (p q r s : ℤ) :
    Work.Coherence.cfInner (p • a - q • b) (r • c - s • d) =
      (p : ℂ) * (r : ℂ) * Work.Coherence.cfInner a c
        - (p : ℂ) * (s : ℂ) * Work.Coherence.cfInner a d
        - (q : ℂ) * (r : ℂ) * Work.Coherence.cfInner b c
        + (q : ℂ) * (s : ℂ) * Work.Coherence.cfInner b d := by
  simp only [cfInner_sub_left, cfInner_sub_right, cfInner_zsmul_left, cfInner_zsmul_right]
  ring

end Work.Coherence
