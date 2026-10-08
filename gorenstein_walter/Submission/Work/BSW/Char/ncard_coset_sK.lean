/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: the cardinality of the coset `Ks`

Bender's count `i(t) = |K| + 1` (`Work.BSW.Char.iFn_t`) counts the coset `Ks` (which has `|K|`
elements) together with `t` itself, the two parts being disjoint because `t ∉ Ks`.
-/
import Mathlib
import Submission.Work.BSW.Basic

namespace Work.BSW.Char

open Subgroup Work.GW2

/-- The right coset `Ks = {x | ∃ k ∈ K, x = k * s}` has `|K|` elements (the map `k ↦ k * s` is
injective), and `t ∉ Ks` because `t = k * s` would give `s = k⁻¹ t ∈ K`, contradicting `s ∉ K`. -/
theorem ncard_coset_sK {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    {x : G | ∃ k ∈ K, x = k * s}.ncard = Nat.card ↥K ∧
      t ∉ {x : G | ∃ k ∈ K, x = k * s} := by
  constructor
  · -- `Ks` is the image of `K` under the injective map `k ↦ k * s`.
    have himg : {x : G | ∃ k ∈ K, x = k * s} = (fun k : G => k * s) '' (K : Set G) := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
    rw [himg, Set.ncard_image_of_injective _ (fun a b hab => mul_right_cancel hab)]
    rfl
  · rintro ⟨k, hk, hks⟩
    have hs : s = k⁻¹ * t := by rw [hks]; group
    exact Work.BSW.s_notMem_K h
      (by rw [hs]; exact K.mul_mem (K.inv_mem hk) (Work.BSW.t_mem_K h))

end Work.BSW.Char
