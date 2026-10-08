import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- The image of a chief factor `K/H` in `G/H` is a minimal normal subgroup of `G/H`. -/
theorem isChiefFactor_isMinimalNormal_map {G : Type*} [Group G] {H K : Subgroup G} [H.Normal]
    (h : Work.Fitting.IsChiefFactor H K) :
    Work.Fitting.IsMinimalNormal (K.map (QuotientGroup.mk' H)) := by
  obtain ⟨hH, hK, hlt, hmin⟩ := h
  have hHK : H ≤ K := hlt.le
  have hsurj : Function.Surjective (QuotientGroup.mk' H : G →* G ⧸ H) :=
    QuotientGroup.mk'_surjective H
  refine ⟨hK.map _ hsurj, ?_, ?_⟩
  · -- `K/H` is nontrivial
    intro hbot
    have hle : K ≤ (QuotientGroup.mk' H).ker := by
      rw [← Subgroup.map_eq_bot_iff]; exact hbot
    rw [QuotientGroup.ker_mk'] at hle
    exact hlt.ne' (le_antisymm hle hHK)
  · -- minimality of `K/H` among normal subgroups of `G/H`
    intro M hMnorm hMle hMne
    have hM'norm : (M.comap (QuotientGroup.mk' H)).Normal := Subgroup.normal_comap _
    have hHM' : H ≤ M.comap (QuotientGroup.mk' H) := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hx1 : (QuotientGroup.mk' H) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [hx1]; exact M.one_mem
    have hM'K : M.comap (QuotientGroup.mk' H) ≤ K := by
      calc M.comap (QuotientGroup.mk' H)
          ≤ (K.map (QuotientGroup.mk' H)).comap (QuotientGroup.mk' H) :=
            Subgroup.comap_mono hMle
        _ = K := Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hHK)
    rcases hmin _ hM'norm hHM' hM'K with hEq | hEq
    · exfalso
      apply hMne
      have hMmap : M = (M.comap (QuotientGroup.mk' H)).map (QuotientGroup.mk' H) :=
        (Subgroup.map_comap_eq_self_of_surjective hsurj M).symm
      rw [hMmap, hEq, Subgroup.map_eq_bot_iff]
      rw [QuotientGroup.ker_mk']
    · have hMmap : M = (M.comap (QuotientGroup.mk' H)).map (QuotientGroup.mk' H) :=
        (Subgroup.map_comap_eq_self_of_surjective hsurj M).symm
      rw [hMmap, hEq]

end Work.Fitting
