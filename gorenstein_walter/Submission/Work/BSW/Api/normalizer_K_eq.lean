import Mathlib
import Submission.Work.BSW.Basic

namespace Work.BSW.Api

open Subgroup Work.GW2

section Helpers

variable {G : Type} [Group G] {K : Subgroup G}

/-- An element of the normalizer of `K` conjugates `conjSub` to `K` itself:
`g ∈ N_G(K)` means `K^g = K` in the notation `conjSub g K = gKg⁻¹`. -/
theorem conjSub_eq_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    conjSub g K = K := by
  rw [conjSub]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

end Helpers

section Helpers2

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {t s : G}

/-- Since `s` inverts `K`, the conjugate `s K s⁻¹` is again `K` (it is the same set, with each
element replaced by its inverse). -/
theorem conjSub_s_eq (h : BSWHyps2 G t s K) :
    conjSub s K = K := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change s * y * s⁻¹ ∈ K
    rw [Work.BSW.inverts_s_K h y hy]
    exact K.inv_mem hy
  · intro x hx
    refine ⟨x⁻¹, K.inv_mem hx, ?_⟩
    change s * x⁻¹ * s⁻¹ = x
    rw [Work.BSW.inverts_s_K h x⁻¹ (K.inv_mem hx), inv_inv]

/-- `s` normalizes `K`. -/
theorem s_mem_normalizer (h : BSWHyps2 G t s K) : s ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact conjSub_s_eq h

end Helpers2

section Main

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- `N_G(K) ≤ C_G(t)`: if `g` normalizes `K` but does not centralize `t`, then
`K = K ∩ K^g = ⊥` by the TI condition, contradicting `t ∈ K`, `t ≠ 1`. -/
theorem normalizer_le_centralizer_t (h : BSWHyps2 G t s K) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  intro g hg
  by_contra hgc
  have hconj : conjSub g K = K := conjSub_eq_of_mem_normalizer hg
  have hTI := Work.BSW.TI h g hgc
  rw [hconj, inf_idem] at hTI
  have ht : t ∈ (⊥ : Subgroup G) := by
    rw [← hTI]
    exact Work.BSW.t_mem_K h
  exact Work.BSW.t_ne_one h (Subgroup.mem_bot.mp ht)

/-- `C_G(t) = K⟨s⟩ ≤ N_G(K)`: both `K` and `s` normalize `K` (`s` because it inverts it). -/
theorem centralizer_t_le_normalizer (h : BSWHyps2 G t s K) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  rw [Work.BSW.centralizer_t_eq h]
  exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr (s_mem_normalizer h))

end Main

/-- `N_G(K) = C_G(t)`: if `g` normalizes `K` then `K ∩ K^g = K ≠ ⊥`, so `g ∈ C_G(t)` by the TI
condition; conversely `C_G(t) = K⟨s⟩` normalizes `K`, since `s` inverts `K`. -/
theorem normalizer_K_eq {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({t} : Set G) :=
  le_antisymm (normalizer_le_centralizer_t h) (centralizer_t_le_normalizer h)

end Work.BSW.Api
