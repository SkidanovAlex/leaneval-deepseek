import Mathlib
import Submission.Work.BSW.Basic

namespace Work.BSW.Api

open Subgroup

/-- `K` is normal in `C_G(t) = K⟨s⟩`, since `s` inverts `K`. -/
theorem K_normal_in_centralizer {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    (K.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal := by
  -- `K` is normal in `C_G(t)` iff `C_G(t) ≤ N_G(K)`; and `C_G(t) = K ⊔ ⟨s⟩`.
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (K_le_centralizer_t h), centralizer_t_eq h]
  -- `K ≤ N_G(K)` trivially; and `s ∈ N_G(K)` since `s` inverts `K`.
  refine sup_le K.le_normalizer ?_
  rw [Subgroup.le_normalizer_iff]
  intro x hx k hk
  rcases mem_zpowers_s h hx with rfl | rfl
  · simpa using hk
  · rw [inverts_s_K h k hk]
    exact K.inv_mem hk

end Work.BSW.Api
