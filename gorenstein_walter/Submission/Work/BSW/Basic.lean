/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: the API of `BSWHyps2`

Bender's hypotheses (`Work.GW2.BSWHyps2`) are a conjunction of nine clauses about a finite group
`G`, two involutions `t`, `s` and an abelian subgroup `K ≤ C_G(t)`.  This file exposes them as
named lemmas and draws the first elementary consequences.  The deeper consequences
(`|C_G(t)| = 2|K|`, `N_G(K) = C_G(t)`, `K` has a unique involution, `|K|` is even, the involution
count, and the `|K| = 2` Sylow structure) are in the sibling files of this directory; see
`Submission/Work/BSW/NOTES_BSW.md` for the index.

Notation used throughout the area: `H := centralizer {t}` is Bender's `H = C_G(t) = K⟨s⟩`.
-/
import Submission.Work.BSW.Defs

open scoped MatrixGroups

namespace Work.BSW

open Subgroup Work.GW2

section Accessors

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

theorem orderOf_t {t s : G} {K : Subgroup G} (h : BSWHyps2 G t s K) : orderOf t = 2 := h.1

theorem orderOf_s (h : BSWHyps2 G t s K) : orderOf s = 2 := h.2.1

theorem t_mem_K (h : BSWHyps2 G t s K) : t ∈ K := h.2.2.1

theorem s_notMem_K (h : BSWHyps2 G t s K) : s ∉ K := h.2.2.2.1

theorem isMulCommutative_K (h : BSWHyps2 G t s K) : IsMulCommutative K := h.2.2.2.2.1

/-- Bender's `H = K⟨s⟩`. -/
theorem centralizer_t_eq (h : BSWHyps2 G t s K) :
    centralizer ({t} : Set G) = K ⊔ zpowers s := h.2.2.2.2.2.1

theorem inverts_s_K (h : BSWHyps2 G t s K) : Inverts s K := h.2.2.2.2.2.2.1

theorem K_inf_centralizer_s (h : BSWHyps2 G t s K) :
    K ⊓ centralizer ({s} : Set G) = zpowers t := h.2.2.2.2.2.2.2.1

/-- Condition (iii): `K` is TI with respect to `C_G(t)`. -/
theorem TI (h : BSWHyps2 G t s K) :
    ∀ g : G, g ∉ centralizer ({t} : Set G) → K ⊓ conjSub g K = ⊥ :=
  h.2.2.2.2.2.2.2.2.1

/-- Condition (iv): all involutions are conjugate to `t`. -/
theorem involutions_conj (h : BSWHyps2 G t s K) :
    ∀ x : G, orderOf x = 2 → IsConj x t := h.2.2.2.2.2.2.2.2.2

end Accessors

section Consequences

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

theorem t_ne_one (h : BSWHyps2 G t s K) : t ≠ 1 := by
  intro h1
  have h2 := orderOf_t h
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem s_ne_one (h : BSWHyps2 G t s K) : s ≠ 1 := by
  intro h1
  have h2 := orderOf_s h
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem t_mul_self (h : BSWHyps2 G t s K) : t * t = 1 := by
  have h2 := pow_orderOf_eq_one t
  rw [orderOf_t h] at h2
  simpa [pow_two] using h2

theorem s_mul_self (h : BSWHyps2 G t s K) : s * s = 1 := by
  have h2 := pow_orderOf_eq_one s
  rw [orderOf_s h] at h2
  simpa [pow_two] using h2

theorem t_inv (h : BSWHyps2 G t s K) : t⁻¹ = t := by
  calc t⁻¹ = t⁻¹ * (t * t) := by rw [t_mul_self h, mul_one]
    _ = (t⁻¹ * t) * t := by rw [mul_assoc]
    _ = t := by rw [inv_mul_cancel, one_mul]

theorem s_inv (h : BSWHyps2 G t s K) : s⁻¹ = s := by
  calc s⁻¹ = s⁻¹ * (s * s) := by rw [s_mul_self h, mul_one]
    _ = (s⁻¹ * s) * s := by rw [mul_assoc]
    _ = s := by rw [inv_mul_cancel, one_mul]

/-- `s` commutes with `t` (because `s` inverts `t`, and `t⁻¹ = t`). -/
theorem s_mul_t_eq_t_mul_s (h : BSWHyps2 G t s K) : s * t = t * s := by
  have h1 : s * t * s⁻¹ = t := by
    rw [inverts_s_K h t (t_mem_K h), t_inv h]
  calc s * t = (s * t * s⁻¹) * s := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = t * s := by rw [h1]

theorem s_mem_centralizer_t (h : BSWHyps2 G t s K) : s ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (s_mul_t_eq_t_mul_s h).symm

theorem t_mem_centralizer_t (h : BSWHyps2 G t s K) : t ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rfl

theorem K_le_centralizer_t (h : BSWHyps2 G t s K) : K ≤ centralizer ({t} : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  haveI : IsMulCommutative ↥K := isMulCommutative_K h
  exact (congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥K)).comm
    (⟨x, hx⟩ : ↥K) (⟨t, t_mem_K h⟩ : ↥K))).symm

theorem zpowers_s_le_centralizer_t (h : BSWHyps2 G t s K) :
    zpowers s ≤ centralizer ({t} : Set G) :=
  Subgroup.zpowers_le.mpr (s_mem_centralizer_t h)

theorem zpowers_t_le_K (h : BSWHyps2 G t s K) : zpowers t ≤ K :=
  Subgroup.zpowers_le.mpr (t_mem_K h)

/-- The elements of `⟨s⟩` are `1` and `s` (as `s` is an involution). -/
theorem mem_zpowers_s (h : BSWHyps2 G t s K) {x : G} (hx : x ∈ zpowers s) :
    x = 1 ∨ x = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : s ^ k = s ^ (k % (2 : ℤ)) := zpow_eq_zpow_emod' k (by simpa [pow_two] using s_mul_self h)
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [h1, hk, zpow_zero]
  · right
    rw [h1, hk, zpow_one]

/-- The elements of `⟨t⟩` are `1` and `t`. -/
theorem mem_zpowers_t (h : BSWHyps2 G t s K) {x : G} (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : t ^ k = t ^ (k % (2 : ℤ)) := zpow_eq_zpow_emod' k (by simpa [pow_two] using t_mul_self h)
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [h1, hk, zpow_zero]
  · right
    rw [h1, hk, zpow_one]

/-- `K ⊓ ⟨s⟩ = ⊥`, since `s ∉ K` and the only elements of `⟨s⟩` are `1` and `s`. -/
theorem K_inf_zpowers_s (h : BSWHyps2 G t s K) : K ⊓ zpowers s = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxs⟩
  rcases mem_zpowers_s h hxs with rfl | rfl
  · exact Subgroup.mem_bot.mpr rfl
  · exact absurd hxK (s_notMem_K h)

/-- `s` inverts `t`. -/
theorem inverts_t (h : BSWHyps2 G t s K) : s * t * s⁻¹ = t⁻¹ :=
  inverts_s_K h t (t_mem_K h)

/-- Every involution of `K` is `t`: if `x² = 1` then `s` inverts `x`, hence `x` centralizes `s`
and `x ∈ K ⊓ C_G(s) = ⟨t⟩`. -/
theorem involution_mem_K (h : BSWHyps2 G t s K) {x : G} (hxK : x ∈ K) (hx : x * x = 1) :
    x = 1 ∨ x = t := by
  have hxinv : x⁻¹ = x := by
    calc x⁻¹ = x⁻¹ * (x * x) := by rw [hx, mul_one]
      _ = (x⁻¹ * x) * x := by rw [mul_assoc]
      _ = x := by rw [inv_mul_cancel, one_mul]
  have h1 : s * x * s⁻¹ = x := by rw [inverts_s_K h x hxK, hxinv]
  have hxs : s * x = x * s := by
    calc s * x = (s * x * s⁻¹) * s := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = x * s := by rw [h1]
  have hmem : x ∈ K ⊓ centralizer ({s} : Set G) := by
    refine ⟨hxK, ?_⟩
    change x ∈ centralizer ({s} : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hxs
  rw [K_inf_centralizer_s h] at hmem
  exact mem_zpowers_t h hmem

/-- `K` has a unique involution, namely `t`. -/
theorem orderOf_eq_two_of_mem_K (h : BSWHyps2 G t s K) {x : G} (hxK : x ∈ K)
    (hx : orderOf x = 2) : x = t := by
  have hx1 : x * x = 1 := by
    have h2 := pow_orderOf_eq_one x
    rw [hx] at h2
    simpa [pow_two] using h2
  rcases involution_mem_K h hxK hx1 with h1 | h1
  · rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · exact h1

end Consequences

end Work.BSW
