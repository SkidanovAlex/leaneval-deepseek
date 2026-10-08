import Mathlib
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Char.coset_sK_involutions
import Submission.Work.BSW.Char.isTISubset_Kdiff

namespace Work.BSW.Cases

open Subgroup Work.GW2

/-- For a subgroup `H ≤ G`, the union of the `G`-conjugates of `H` may be written either as the
conjugacy closure `conjClassSet H` or as the comprehension `{y | ∃ g, g * y * g⁻¹ ∈ H}` of the
elements conjugate into `H`. -/
theorem setOf_exists_conj_mem_eq_conjClassSet {G : Type*} [Group G] (H : Subgroup G) :
    {y : G | ∃ g : G, g * y * g⁻¹ ∈ H} = OddOrder.GroupTheory.conjClassSet (H : Set G) := by
  ext y
  change (∃ g : G, g * y * g⁻¹ ∈ H) ↔ y ∈ OddOrder.GroupTheory.conjClassSet (H : Set G)
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g * y * g⁻¹, hg, g⁻¹, by rw [inv_inv]; group⟩
  · rintro ⟨z, hz, g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    have h : g⁻¹ * y * (g⁻¹)⁻¹ = z := by rw [inv_inv, ← hg]; group
    rw [h]; exact hz

/-- In Bender's setting `H = C_G(t) = K⟨s⟩` has the same `G`-conjugacy closure as `K`: every
element of `H` lies in `K` or is an involution (`k * s`) and hence conjugate to `t ∈ K`. -/
theorem conjClassSet_K_eq_conjClassSet_centralizer {G : Type} [Group G] [Finite G] {t s : G}
    {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K) :
    OddOrder.GroupTheory.conjClassSet (K : Set G) =
      OddOrder.GroupTheory.conjClassSet
        ((Subgroup.centralizer ({t} : Set G)) : Set G) := by
  apply Set.Subset.antisymm
  · intro y hy
    rw [OddOrder.GroupTheory.mem_conjClassSet] at hy ⊢
    obtain ⟨x, hxK, g, hg⟩ := hy
    exact ⟨x, Work.BSW.K_le_centralizer_t h hxK, g, hg⟩
  · intro y hy
    rw [OddOrder.GroupTheory.mem_conjClassSet] at hy ⊢
    obtain ⟨x, hxH, g, hg⟩ := hy
    have hxK : x ∈ OddOrder.GroupTheory.conjClassSet (K : Set G) := by
      have hxH' : x ∈ Subgroup.centralizer ({t} : Set G) := hxH
      rw [Work.BSW.Api.mem_centralizer_iff h x] at hxH'
      rcases hxH' with hxK | ⟨k, hk, rfl⟩
      · exact OddOrder.GroupTheory.subset_conjClassSet hxK
      · have hord : orderOf (k * s) = 2 := ((Work.BSW.Char.coset_sK_involutions h).1 k hk).1
        obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h (k * s) hord)
        exact ⟨t, Work.BSW.t_mem_K h, c⁻¹, by rw [inv_inv, ← hc]; group⟩
    exact hg ▸ (OddOrder.GroupTheory.mem_conjClassSet_conj_iff g x).mpr hxK

theorem conjClassSet_K_eq_centralizer {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    OddOrder.GroupTheory.conjClassSet (K : Set G) =
      {y : G | ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G)} := by
  rw [conjClassSet_K_eq_conjClassSet_centralizer h,
    setOf_exists_conj_mem_eq_conjClassSet (Subgroup.centralizer ({t} : Set G))]

end Work.BSW.Cases
