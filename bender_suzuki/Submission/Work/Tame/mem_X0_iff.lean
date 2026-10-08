import Mathlib
import Submission.Work.Tame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- Feit–Thompson Lemma 9.5: `𝔛₀` is the set of elements of `X` conjugate to an element of
`⋃_{i=0}^n ⋃_{L ∈ 𝔏_i} 𝔄_L`. -/
theorem mem_X0_iff {X : Type*} [Group X] {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    {x : X} : x ∈ X0 Lhat n Hs ↔ ∃ a ∈ AU Lhat n Hs, IsConj a x := by
  simp only [X0, Set.mem_iUnion, Set.mem_image, isConj_iff]
  constructor
  · rintro ⟨i, a, ha, h⟩; exact ⟨a, ha, i, h⟩
  · rintro ⟨a, ha, c, h⟩; exact ⟨c, a, ha, h⟩

end Work.Tame
