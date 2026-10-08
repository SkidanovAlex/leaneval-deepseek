import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

theorem isNilpotent_map_of_surjective' {G H : Type*} [Group G] [Group H] {N : Subgroup G}
    [Group.IsNilpotent ↥N] (φ : G →* H) : Group.IsNilpotent ↥(N.map φ) := by
  have hker : (φ.comp N.subtype).range = N.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h := Group.nilpotent_of_surjective (φ.comp N.subtype).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  rwa [hker] at h

theorem map_fitting_le {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) : (Work.Fitting.fitting G).map φ ≤ Work.Fitting.fitting H := by
  rw [fitting, map_sSup, fitting]
  refine sSup_le ?_
  rintro _ ⟨N, hN, rfl⟩
  rw [mem_fittingSet] at hN
  obtain ⟨hNnorm, hNnil⟩ := hN
  haveI := hNnil
  exact le_sSup ⟨hNnorm.map φ hφ, isNilpotent_map_of_surjective' φ⟩

end Work.Fitting
