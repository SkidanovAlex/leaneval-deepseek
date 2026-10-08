import Mathlib
import Submission.Work.ThmG.centralizer_le_twoPoint_of_fixedPts_card_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

open LeanEval.GroupTheory.Defs Submission.Blueprint in theorem fixedPts_zpowers_eq_pair {G : Type} [Group G] [Finite G] {H : Subgroup G} {t k : G}
    (ht : t ∉ H) (hk : k ∈ twoPoint H t)
    (h2 : (fixedPts H (Subgroup.zpowers k)).ncard = 2) :
    fixedPts H (Subgroup.zpowers k) = {((1 : G) : G ⧸ H), ((t : G) : G ⧸ H)} := by
  -- `k ∈ D = H ∩ Hᵗ`: it lies in `H` and in `t H t⁻¹`.
  have hkH : k ∈ H := hk.1
  have hkt : k ∈ Submission.Blueprint.conj t H := hk.2
  -- every element of `⟨k⟩` lies in `H`
  have hzH : ∀ y ∈ Subgroup.zpowers k, y ∈ H := fun y hy => Subgroup.zpowers_le.mpr hkH hy
  -- the coset `H` is fixed by `⟨k⟩` (since `⟨k⟩ ≤ H`)
  have hmem1 : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers k) := by
    rw [Submission.Blueprint.fixedPts]
    intro y hy
    have hyH : y ∈ H := hzH y hy
    change ((y * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [mul_one, QuotientGroup.eq]
    simpa using H.inv_mem hyH
  -- the coset `tH` is fixed by `⟨k⟩` (since `t⁻¹ k t ∈ H`)
  have hmemt : ((t : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers k) := by
    rw [Submission.Blueprint.fixedPts]
    intro y hy
    change ((y * t : G) : G ⧸ H) = ((t : G) : G ⧸ H)
    rw [QuotientGroup.eq]
    rcases Subgroup.mem_map.mp (Subgroup.zpowers_le.mpr hkt hy) with ⟨h, hh, hhy⟩
    change (MulAut.conj t) h = y at hhy
    rw [MulAut.conj_apply] at hhy
    have hh' : (y * t)⁻¹ * t = h⁻¹ := by rw [← hhy]; group
    rw [hh']; exact H.inv_mem hh
  -- the two cosets are distinct because `t ∉ H`
  have hab : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact ht (by simpa using hcon)
  -- the two-element set `{1, t}` is contained in `fixedPts`, which has `ncard 2`; hence equal
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
  · rintro ω (rfl | rfl)
    · exact hmem1
    · exact hmemt
  · rw [h2, Set.ncard_pair hab]

end Work.ThmF.ChV3.Prove
