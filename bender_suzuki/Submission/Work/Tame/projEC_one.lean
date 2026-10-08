import Mathlib
import Submission.Work.Tame.Tau

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- `projEC` sends `1` to `1`: `1 = 1 · 1` is the decomposition of the identity (and the
hypothesis `𝔎 ⊓ 𝔏 = 1` makes the element of `𝔏 ⊓ 𝔑` unique). -/
theorem projEC_one {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {K : Subgroup X}
    (hinf : K ⊓ Lgrp Lhat = ⊥) : projEC Lhat K 1 = 1 :=
  projEC_eq_of hinf (by simp)

end Work.Tame
