/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 2` case)

# The `|K| = 2` case of BSW: the elementary structure of `C_G(t)`

Under `Work.GW2.BSWHyps2 G t s K` with `Nat.card K = 2`, the subgroup `K` is `{1, t}` and

`C := C_G(t) = K ⊔ ⟨s⟩ = {1, t, s, t * s}`

is a Klein four-group (of order `4`): it is abelian, all its nonidentity elements are involutions,
and it is self-centralizing (`C_G(C) = C`).

These are the elementary facts on which the analysis of the normalizer
`N = N_G(C_G(t))` (file `Submission/Work/BSW/Cases/normalizer_centralizer_structure.lean`)
rests.

The main statement about `N` itself is recorded here as the definition `ActionDichotomy`: an
element `x ∈ N` outside `C` permutes the three involutions `t, s, t * s` of `C` by a 3-cycle,
i.e. either `x t x⁻¹ = s` and `x s x⁻¹ = t * s`, or `x t x⁻¹ = t * s` and `x s x⁻¹ = t`.
-/
import Mathlib
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Api.card_centralizer_of_card_K_two
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Cases.bswK2Involution

namespace Work.BSW.Cases.K2NCS

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- In the `|K| = 2` case, `K = {1, t}`: `t ∈ K` and `|K| = 2`, and `t` is the unique involution
of `K`. -/
theorem mem_K_iff (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) {x : G} :
    x ∈ K ↔ x = 1 ∨ x = t := by
  constructor
  · intro hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr (Work.BSW.orderOf_eq_two_of_mem_K h hx ?_)
      have hdvd : orderOf x ∣ Nat.card ↥K := by
        rw [← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
      rw [hk] at hdvd
      have hle : orderOf x ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < orderOf x := orderOf_pos x
      have hne : orderOf x ≠ 1 := by
        intro h1
        exact hx1 (orderOf_eq_one_iff.mp h1)
      omega
  · rintro (rfl | rfl)
    · exact K.one_mem
    · exact Work.BSW.t_mem_K h

/-- The elements of `C = C_G(t)` are exactly `1`, `t`, `s` and `t * s`. -/
theorem mem_centralizer_iff_one_or (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) (x : G) :
    x ∈ Subgroup.centralizer ({t} : Set G) ↔ x = 1 ∨ x = t ∨ x = s ∨ x = t * s := by
  rw [Work.BSW.Api.mem_centralizer_iff h x]
  constructor
  · rintro (hxK | ⟨k, hkK, hxks⟩)
    · rcases (mem_K_iff h hk).mp hxK with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · rcases (mem_K_iff h hk).mp hkK with h1 | h1
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [h1, one_mul] at hxks
        exact hxks
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [h1] at hxks
        exact hxks
  · rintro (h1 | h1 | h1 | h1)
    · rw [h1]; exact Or.inl K.one_mem
    · rw [h1]; exact Or.inl (Work.BSW.t_mem_K h)
    · rw [h1]; exact Or.inr ⟨1, K.one_mem, by rw [one_mul]⟩
    · rw [h1]; exact Or.inr ⟨t, Work.BSW.t_mem_K h, rfl⟩

/-- The subgroup `C = C_G(t)` of the `|K| = 2` case is abelian: two elements of
`{1, t, s, t * s}` commute. -/
theorem mul_comm_of_mem_centralizer (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) {a b : G}
    (ha : a ∈ Subgroup.centralizer ({t} : Set G)) (hb : b ∈ Subgroup.centralizer ({t} : Set G)) :
    a * b = b * a := by
  have h1 : t * (t * s) = s := by rw [← mul_assoc, Work.BSW.t_mul_self h, one_mul]
  have h2 : t * s * t = s := by
    rw [mul_assoc, Work.BSW.s_mul_t_eq_t_mul_s h, ← mul_assoc, Work.BSW.t_mul_self h, one_mul]
  have h3 : s * (t * s) = t := by
    rw [← mul_assoc, Work.BSW.s_mul_t_eq_t_mul_s h, mul_assoc, Work.BSW.s_mul_self h, mul_one]
  have h4 : t * s * s = t := by rw [mul_assoc, Work.BSW.s_mul_self h, mul_one]
  rcases (mem_centralizer_iff_one_or h hk a).mp ha with rfl | rfl | rfl | rfl <;>
    rcases (mem_centralizer_iff_one_or h hk b).mp hb with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, h1, h2, h3, h4, mul_assoc, Work.BSW.t_mul_self h,
      Work.BSW.s_mul_self h, Work.BSW.s_mul_t_eq_t_mul_s h]

/-- Every element of `C = C_G(t)` other than `1` is an involution. -/
theorem orderOf_eq_two_of_mem_centralizer (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) {z : G}
    (hz : z ∈ Subgroup.centralizer ({t} : Set G)) (hz1 : z ≠ 1) : orderOf z = 2 := by
  rcases (mem_centralizer_iff_one_or h hk z).mp hz with rfl | rfl | rfl | rfl
  · exact absurd rfl hz1
  · exact Work.BSW.orderOf_t h
  · exact Work.BSW.orderOf_s h
  · -- `z = t * s`
    have hinv : (t * s)⁻¹ = t * s := by
      rw [mul_inv_rev, Work.BSW.s_inv h, Work.BSW.t_inv h, Work.BSW.s_mul_t_eq_t_mul_s h]
    have hsq : t * s * (t * s) = 1 := by
      have h5 : (t * s) * (t * s)⁻¹ = 1 := mul_inv_cancel _
      rwa [hinv] at h5
    have hdvd : orderOf (t * s) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using hsq
    have hne : orderOf (t * s) ≠ 1 := by
      intro h1
      have hts : t * s = 1 := orderOf_eq_one_iff.mp h1
      have hst : s = t := by
        have h2 := congrArg (fun z => t * z) hts
        rw [← mul_assoc, Work.BSW.t_mul_self h, one_mul, mul_one] at h2
        exact h2
      exact Work.BSW.s_notMem_K h (hst ▸ Work.BSW.t_mem_K h)
    have hle : orderOf (t * s) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf (t * s) := orderOf_pos _
    omega

/-- `C_G(C) = C`: the centralizer of `C = C_G(t)` is `C` itself (it is contained in `C_G(t)`, and
`C` is abelian). -/
theorem centralizer_centralizer_eq (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    Subgroup.centralizer ((Subgroup.centralizer ({t} : Set G)) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.centralizer_le ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Work.BSW.t_mem_centralizer_t h
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact mul_comm_of_mem_centralizer h hk hb ha

/-- **The action of `N_G(C_G(t))` on the three involutions of `C_G(t)`**, in the `|K| = 2` case:
an element `x` of the normalizer of `C = C_G(t)` that does not lie in `C` permutes `t`, `s` and
`t * s` by a 3-cycle.  This is the dichotomy on which the whole analysis of `N_G(C_G(t))` rests. -/
abbrev ActionDichotomy (G : Type) [Group G] [Finite G] (t s : G) : Prop :=
  ∀ x : G, x ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G) →
    x ∉ Subgroup.centralizer ({t} : Set G) →
    (x * t * x⁻¹ = s ∧ x * s * x⁻¹ = t * s) ∨
      (x * t * x⁻¹ = t * s ∧ x * s * x⁻¹ = t)

end Work.BSW.Cases.K2NCS
