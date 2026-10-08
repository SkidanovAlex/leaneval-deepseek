/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: involutions inverting `t` lie in `K ∪ Ks`

Bender's count `i(t) = |K| + 1` (`Work.BSW.Char.iFn_t`) needs the classification of the
involutions `u` with `u⁻¹ t u = t⁻¹`: such a `u` lies in `C_G(t) = K⟨s⟩`, hence is either `t`
(the unique involution of `K`) or an element of the coset `Ks`.
-/
import Mathlib
import Submission.Work.BSW.Api.mem_centralizer_iff

namespace Work.BSW.Char

open Subgroup Work.GW2

/-- An involution `u` inverting `t` lies in `C_G(t) = K⟨s⟩` (from `u⁻¹ t u = t⁻¹` we get
`t u = u t⁻¹ = u t`), hence — by `Work.BSW.Api.mem_centralizer_iff` — either in `K`, in which case
it is `t` (`Work.BSW.orderOf_eq_two_of_mem_K`), or in the right coset `Ks`. -/
theorem inv_inverting_t_mem_coset {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) {u : G} (hu2 : orderOf u = 2)
    (hu : u⁻¹ * t * u = t⁻¹) : u = t ∨ ∃ k ∈ K, u = k * s := by
  -- `u` centralizes `t`.
  have htu : t * u = u * t := by
    have h1 : t * u = u * t⁻¹ := by
      calc t * u = u * (u⁻¹ * t * u) := by group
        _ = u * t⁻¹ := by rw [hu]
    rwa [Work.BSW.t_inv h] at h1
  have hmem : u ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact htu
  rcases (Work.BSW.Api.mem_centralizer_iff h u).mp hmem with huK | ⟨k, hk, hks⟩
  · exact Or.inl (Work.BSW.orderOf_eq_two_of_mem_K h huK hu2)
  · exact Or.inr ⟨k, hk, hks⟩

end Work.BSW.Char
