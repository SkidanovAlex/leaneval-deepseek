import Mathlib
import Submission.Work.Tame.Tau

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- The projection `projEC` fixes the elements of `𝔏 ⊓ 𝔑` (Feit–Thompson's decomposition
`𝔑 = 𝔎(𝔏 ∩ 𝔑)` with `𝔎 ∩ 𝔏 = 1`): for `m ∈ 𝔏 ⊓ 𝔑`, regarded as an element of `𝔑`, the element
selected by `projEC` is `m` itself. -/
theorem projEC_eq_self {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {K : Subgroup X}
    (hinf : K ⊓ Lgrp Lhat = ⊥) (m : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) :
    projEC Lhat K (⟨(m : X), m.2.2⟩ : ↥(Lgrp (K : Set X))) = m := by
  apply projEC_eq_of hinf
  show (m : X) * (m : X)⁻¹ ∈ K
  rw [mul_inv_cancel]
  exact K.one_mem

end Work.Tame
