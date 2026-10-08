import Mathlib
import Submission.Work.Tame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- Feit–Thompson (ii)(e), p. 804: for a non-trivial subgroup `𝔎`, the identity lies in
`Ñ = (⋃_{H ∈ 𝔎^#} C_{N(𝔎)}(H)) - 𝔎^#`, because `1` centralizes every element of `𝔎` and (as
`𝔎 ≠ ⊥`) the indexing set `𝔎^#` is non-empty.

(The hypothesis `𝔎 ≠ ⊥` is necessary: `hatN ⊥ = ∅` since `punct ⊥ = ∅`.) -/
theorem one_mem_hatN {X : Type*} [Group X] {K : Subgroup X} (hK : K ≠ ⊥) :
    (1 : X) ∈ hatN K := by
  obtain ⟨H, hHK, hH1⟩ : ∃ H ∈ K, H ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one K with h | h
    · exact absurd h hK
    · exact h
  rw [hatN, Set.mem_sdiff]
  refine ⟨?_, ?_⟩
  · rw [hatNCore, Set.mem_iUnion]
    exact ⟨H, Set.mem_iUnion.mpr ⟨⟨hHK, hH1⟩, by simp⟩⟩
  · simp [punct]

end Work.Tame
