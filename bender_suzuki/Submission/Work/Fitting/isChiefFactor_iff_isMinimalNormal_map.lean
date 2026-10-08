import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.isChiefFactor_isMinimalNormal_map

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- `K/H` is a chief factor of `G` iff its image in `G/H` is a minimal normal subgroup
of `G/H` (for `H ≤ K`, `H` normal). -/
theorem isChiefFactor_iff_isMinimalNormal_map {G : Type*} [Group G] {H K : Subgroup G} [H.Normal]
    (hHK : H ≤ K) :
    Work.Fitting.IsChiefFactor H K ↔ Work.Fitting.IsMinimalNormal (K.map (QuotientGroup.mk' H)) := by
  constructor
  · exact isChiefFactor_isMinimalNormal_map
  · intro hm
    obtain ⟨hNnorm, hNne, hmin⟩ := hm
    have hker : (QuotientGroup.mk' H).ker = H := QuotientGroup.ker_mk' H
    have hcomap : (K.map (QuotientGroup.mk' H)).comap (QuotientGroup.mk' H) = K :=
      Subgroup.comap_map_eq_self (by rw [hker]; exact hHK)
    have hKnorm : K.Normal := by
      have h := hNnorm.comap (QuotientGroup.mk' H)
      rwa [hcomap] at h
    refine ⟨inferInstance, hKnorm, ?_, ?_⟩
    · refine lt_of_le_of_ne hHK fun hEq => hNne ?_
      rw [← hEq]
      exact (Subgroup.map_eq_bot_iff H).mpr (le_of_eq (QuotientGroup.ker_mk' H).symm)
    · intro M hMnorm hHM hMK
      by_cases hMH : M = H
      · exact Or.inl hMH
      · right
        have hsurj : Function.Surjective (QuotientGroup.mk' H : G →* G ⧸ H) :=
          QuotientGroup.mk'_surjective H
        have hMmapnorm : (M.map (QuotientGroup.mk' H)).Normal := hMnorm.map _ hsurj
        have hMmaple : M.map (QuotientGroup.mk' H) ≤ K.map (QuotientGroup.mk' H) :=
          Subgroup.map_mono hMK
        have hMmapne : M.map (QuotientGroup.mk' H) ≠ ⊥ := by
          intro hb
          apply hMH
          have hMHle : M ≤ H := by
            rw [Subgroup.map_eq_bot_iff M, hker] at hb
            exact hb
          exact le_antisymm hMHle hHM
        have hEq := hmin _ hMmapnorm hMmaple hMmapne
        have hMcomap : (M.map (QuotientGroup.mk' H)).comap (QuotientGroup.mk' H) = M :=
          Subgroup.comap_map_eq_self (by rw [hker]; exact hHM)
        rw [← hMcomap, hEq, hcomap]

end Work.Fitting
