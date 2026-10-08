import Mathlib
import Submission.Work.ZJB.Step1.Defs

namespace Work.ZJB2.Step1

open Work.ZJB Subgroup

/-- **I.6** `𝓗` has a member with maximal `ν_p(|N(H)|)`: the set `𝓗` of subgroups `H` satisfying
`InScrH p S D a H` is a set of subgroups of the finite group `G`, hence finite, and it is
nonempty because the hypothesis gives `D ∈ 𝓗`; so `ν_p(|N(H)|)` attains a maximum on it. -/
theorem existsMaxHProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.ExistsMaxHProp p G := by
  intro S D a hD
  classical
  obtain ⟨H, hH, hmax⟩ :=
    Set.exists_max_image {H : Subgroup G | InScrH p S D a H}
      (fun H => nuP p (normalizer (H : Set G))) (Set.toFinite _) ⟨D, hD⟩
  exact ⟨H, hH, fun H' hH' => hmax H' hH'⟩

end Work.ZJB2.Step1
