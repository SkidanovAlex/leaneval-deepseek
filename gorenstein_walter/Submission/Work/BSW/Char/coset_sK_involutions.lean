/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: the involutions of the coset `Ks`

Bender's count `i(t) = |K| + 1` (`Work.BSW.Char.iFn_t`) identifies the involutions inverting `t`
with the coset `Ks` together with `t` itself.  This file shows that every element of `Ks` — and
`t` itself — is an involution inverting `t`.
-/
import Mathlib
import Submission.Work.BSW.Basic

namespace Work.BSW.Char

open Subgroup Work.GW2

/-- Every element `k * s` of the right coset `Ks` is an involution inverting `t` (`(k s)² = 1`
and `(k s) t (k s) = t⁻¹`), and `t` itself is an involution inverting `t`. -/
theorem coset_sK_involutions {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    (∀ k ∈ K, orderOf (k * s) = 2 ∧ (k * s)⁻¹ * t * (k * s) = t⁻¹) ∧
      orderOf t = 2 ∧ t⁻¹ * t * t = t⁻¹ := by
  -- `s` inverts every element of `K`, and `s⁻¹ = s`.
  have hsks : ∀ k ∈ K, s * k * s = k⁻¹ := by
    intro k hk
    have hk' := Work.BSW.inverts_s_K h k hk
    rwa [Work.BSW.s_inv h] at hk'
  have htinv : t⁻¹ * t * t = t⁻¹ := by
    rw [Work.BSW.t_inv h, Work.BSW.t_mul_self h, one_mul]
  refine ⟨?_, Work.BSW.orderOf_t h, htinv⟩
  intro k hk
  -- `(k s)² = k (s k s) = k k⁻¹ = 1`
  have hks2 : (k * s) * (k * s) = 1 := by
    calc (k * s) * (k * s) = k * (s * k * s) := by group
      _ = k * k⁻¹ := by rw [hsks k hk]
      _ = 1 := mul_inv_cancel k
  have hne : k * s ≠ 1 := by
    intro h1
    have hs : s = k⁻¹ := by
      calc s = k⁻¹ * (k * s) := by group
        _ = k⁻¹ * 1 := by rw [h1]
        _ = k⁻¹ := mul_one _
    exact Work.BSW.s_notMem_K h (by rw [hs]; exact K.inv_mem hk)
  refine ⟨orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hks2) hne, ?_⟩
  -- `(k s)⁻¹ t (k s) = (k s) t (k s)`: push `s` past `k` using `k t = t k` and `s t = t s`.
  have hinv : (k * s)⁻¹ = k * s := inv_eq_of_mul_eq_one_left hks2
  rw [hinv, Work.BSW.t_inv h]
  have hst : s * t = t * s := Work.BSW.s_mul_t_eq_t_mul_s h
  have hkt : k * t = t * k := by
    have hmem : k ∈ Subgroup.centralizer ({t} : Set G) := Work.BSW.K_le_centralizer_t h hk
    rw [Subgroup.mem_centralizer_iff] at hmem
    exact (hmem t (Set.mem_singleton t)).symm
  calc (k * s) * t * (k * s) = k * (s * t) * (k * s) := by group
    _ = k * (t * s) * (k * s) := by rw [hst]
    _ = (k * t) * (s * k * s) := by group
    _ = (k * t) * k⁻¹ := by rw [hsks k hk]
    _ = t * k * k⁻¹ := by rw [hkt]
    _ = t := by group

end Work.BSW.Char
