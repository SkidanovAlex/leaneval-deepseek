import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

namespace Work.CORE2A

theorem exists_mul_of_mem_sup_of_normal {G : Type} [Group G] {U S H : Subgroup G}
    (hUH : U ≤ H) (hSH : S ≤ H) (hUnorm : (U.subgroupOf H).Normal) (hsup : U ⊔ S = H) :
    ∀ h ∈ H, ∃ u ∈ U, ∃ y ∈ S, u * y = h := by
  intro h hh
  -- Work inside the group `H`.  `U.subgroupOf H` is normal in `H` and, since `U ⊔ S = H`,
  -- the two subgroups `U.subgroupOf H` and `S.subgroupOf H` generate `H`.
  have hsup' : U.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    have h1 := Subgroup.subgroupOf_sup (A := U) (A' := S) (B := H) hUH hSH
    rw [hsup, Subgroup.subgroupOf_self] at h1
    exact h1.symm
  -- A normal subgroup times anything generates via the pointwise product:
  -- `↑(U.subgroupOf H ⊔ S.subgroupOf H) = ↑(U.subgroupOf H) * ↑(S.subgroupOf H)`.
  have hmem : (⟨h, hh⟩ : H) ∈ (↑(U.subgroupOf H ⊔ S.subgroupOf H) : Set H) := by
    rw [hsup']; trivial
  rw [Subgroup.normal_mul (U.subgroupOf H) (S.subgroupOf H)] at hmem
  obtain ⟨k, hk, y, hy, hky⟩ := hmem
  exact ⟨(k : G), (Subgroup.mem_subgroupOf.mp hk), (y : G), (Subgroup.mem_subgroupOf.mp hy),
    by have := congrArg (fun z : H => (z : G)) hky; simpa using this⟩

end Work.CORE2A
