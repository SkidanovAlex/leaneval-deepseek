import Mathlib
import Submission.Work.CORE2A.Defs

namespace Work.CORE2A

theorem normalizer_eq_of_coatom {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K Z : Subgroup G}
    (hK : IsCoatom K) (hZK : Z ≤ K) (hZ : Z ≠ ⊥)
    (hKnorm : K ≤ Subgroup.normalizer (Z : Set G)) : Subgroup.normalizer (Z : Set G) = K := by
  -- `N_G(Z)` contains `K`, and `K` is a coatom, so `N_G(Z)` is `K` or `⊤`.
  rcases lt_or_eq_of_le hKnorm with hlt | heq
  · -- If `K < N_G(Z)`, maximality forces `N_G(Z) = ⊤`, i.e. `Z` is normal in `G`.
    have htop : Subgroup.normalizer (Z : Set G) = ⊤ := (hK.lt_iff).mp hlt
    have hZn : Z.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    -- Simplicity then forces `Z = ⊥` or `Z = ⊤`; both contradict the hypotheses.
    rcases Subgroup.Normal.eq_bot_or_eq_top (H := Z) with hbot | htopZ
    · exact absurd hbot hZ
    · exact absurd (top_le_iff.mp (htopZ ▸ hZK)) hK.ne_top
  · exact heq.symm

end Work.CORE2A
