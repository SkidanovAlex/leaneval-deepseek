import Mathlib
import Submission.Work.Tame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- `Ñ^# = ⋃_{H ∈ 𝔎^#} C_{N(𝔎)}(H) - 𝔎`: removing `𝔎^#` from the union and then removing `1`
gives the same set as removing the whole of `𝔎` (since `1 ∈ 𝔎`). -/
theorem hatNp_eq {X : Type*} [Group X] (K : Subgroup X) : hatNp K = hatNCore K \ (K : Set X) := by
  ext x
  simp only [hatNp, hatN, punct, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun hxK => h2 ⟨hxK, h3⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun h => h2 h.1⟩, fun h => h2 (h ▸ K.one_mem)⟩

end Work.Tame
