import Mathlib
import Submission.Work.ZJB.Step1.Defs

namespace Work.ZJB2.Step1

theorem exists_isSylowIn_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A M : Subgroup G} (hAM : A ≤ M) (hAp : IsPGroup p A) :
    ∃ T : Subgroup G, Work.ZJB.IsSylowIn p T M ∧ A ≤ T := by
  -- View `A` as a `p`-subgroup of the group `↥M`, extend it to a Sylow `p`-subgroup `Q` of `↥M`
  -- (Sylow's first theorem), and push `Q` back into `G` along `M.subtype`.
  have hAp' : IsPGroup p (A.subgroupOf M) := by
    rw [← Subgroup.comap_subtype A M]
    exact hAp.comap_of_injective M.subtype Subtype.coe_injective
  obtain ⟨Q, hQle⟩ := hAp'.exists_le_sylow
  refine ⟨Subgroup.map M.subtype (Q : Subgroup ↥M), ?_, ?_⟩
  · refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map M.subtype, ?_⟩
    -- Maximality: any `p`-subgroup `R` of `M` with `T ≤ R` corresponds to a `p`-subgroup
    -- `R.subgroupOf M` of `↥M` containing `Q`, hence equals `Q`.
    intro R hTR hRM hRp
    have hR'p : IsPGroup p (R.subgroupOf M) := by
      rw [← Subgroup.comap_subtype R M]
      exact hRp.comap_of_injective M.subtype Subtype.coe_injective
    have hQR' : (Q : Subgroup ↥M) ≤ R.subgroupOf M := by
      intro q hq
      rw [Subgroup.mem_subgroupOf]
      exact hTR ⟨q, hq, rfl⟩
    have hEq : R.subgroupOf M = (Q : Subgroup ↥M) := Q.is_maximal' hR'p hQR'
    have h2 : Subgroup.map M.subtype ↑(R.subgroupOf M) = R := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRM]
    rw [hEq] at h2
    exact h2.symm
  · intro a ha
    exact ⟨⟨a, hAM ha⟩, hQle (by rw [Subgroup.mem_subgroupOf]; exact ha), rfl⟩

end Work.ZJB2.Step1
