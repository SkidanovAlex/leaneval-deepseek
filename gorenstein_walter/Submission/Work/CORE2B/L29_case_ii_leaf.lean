import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.no_elementary_abelian_eight_of_dihOrCycSylow
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

/-!
# `Work.CORE2B.L29_case_ii_leaf` — Bender 1981, Lemma 2.9, case (ii), leaf form

The sibling `Work.CORE2B.L29_case_ii` handles the case where a central involution `z ∈ Z(N)`
of `N` is given **and** `S ≤ N`: then `z` centralises the Sylow 2-subgroup `S`, so `⟨z⟩ · S`
is a 2-subgroup containing `S`, hence equals `S`; consequently `z ∈ S`, and the structure of
`S` (cyclic `S₀` of index two) forces `z ∈ V`, whence `z ∈ V ⊓ O₂(N) = ⊥`.

Here the hypothesis `S ≤ N` is absent; only `z ∈ N` with `z` central in `N` is assumed.  The
argument is then different: `⟨z⟩` is a normal subgroup of `N` of order two, so
`z ∈ O₂(N)`; if `z ∉ V` then `⟨z⟩ ⊔ V` is an **elementary abelian** 2-subgroup of `G` of
order `8` (`⟨z⟩` and `V` commute elementwise and meet trivially), which is impossible because
the Sylow 2-subgroups of `G` are cyclic or dihedral (`BenderCtx.sylow`), i.e. have 2-rank at
most `2`.

Note that apart from `z ∈ Z(N)` and `V ≤ N` of type `(2,2)` with `V ⊓ O₂(N) = ⊥`, no
hypothesis of `L29Hyp` is used (in particular not `V ≤ S`, `t ∈ V`, `hyp` or `N ≠ ⊤`).

The two general facts used are
* `card_sup_zpowers_four_of` below: an involution `z ∉ V` commuting with a four-group `V`
  produces inside `⟨z⟩ ⊔ V` an elementary abelian group of order `8`;
* `Work.CORE2B.no_elementary_abelian_eight_of_dihOrCycSylow` (delegated): no group with
  cyclic-or-dihedral Sylow 2-subgroups contains one.
-/

namespace Work.CORE2B

open Subgroup
open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- In a group, if `z` is an involution then every element of `⟨z⟩` is `1` or `z`. -/
theorem mem_zpowers_eq_one_or {G : Type} [Group G] {z x : G} (hz : z * z = 1)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  let H : Subgroup G :=
    { carrier := {1, z}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hz]
      one_mem' := by
        simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl
        · simp
        · exact Or.inr (inv_eq_of_mul_eq_one_right hz) }
  have hzH : z ∈ H := by
    show z ∈ ({1, z} : Set G)
    exact Or.inr rfl
  have hle : Subgroup.zpowers z ≤ H := Subgroup.zpowers_le.mpr hzH
  exact hle hx

/-- A finite cyclic group of exponent two has at most two elements. -/
theorem natCard_le_two_of_isCyclic_sq {H : Type} [Group H] [Finite H] [IsCyclic H]
    (h : ∀ x : H, x * x = 1) : Nat.card H ≤ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have htop : Subgroup.zpowers g = (⊤ : Subgroup H) := eq_top_iff.mpr (fun x _ => hg x)
  have hord : orderOf g = Nat.card H := by
    rw [← Nat.card_zpowers g, htop, Subgroup.card_top]
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact h g
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- **The elementary abelian group of order `8` built from an involution and a four-group.**

If `z` is an involution lying outside a four-group `V` of the same (finite) group and
commuting with every element of `V`, then `⟨z⟩ ⊔ V` is an elementary abelian group of
order `8`: the two subgroups commute elementwise (so `V` normalises `⟨z⟩` and the carrier of
the join is the pointwise product), they meet trivially (elements of `⟨z⟩` are `1` or `z`),
and every element of the product is a product of two commuting involutions. -/
theorem card_sup_zpowers_four_of {G : Type} [Group G] [Finite G] {z : G} {V : Subgroup G}
    (hz2 : orderOf z = 2) (hVcard : Nat.card V = 4) (hVsq : ∀ v ∈ V, v ^ 2 = 1)
    (hzV : z ∉ V) (hcomm : ∀ v ∈ V, v * z = z * v) :
    Nat.card ↥(Subgroup.zpowers z ⊔ V) = 8 ∧
      ∀ x ∈ Subgroup.zpowers z ⊔ V, x ^ 2 = 1 := by
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  -- `⟨z⟩ ⊓ V = ⊥`, since the elements of `⟨z⟩` are `1` and `z ∉ V`.
  have hZinfV : Subgroup.zpowers z ⊓ V = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxZ, hxV⟩ := Subgroup.mem_inf.mp hx
    rcases mem_zpowers_eq_one_or hzz hxZ with rfl | rfl
    · rfl
    · exact absurd hxV hzV
  -- `V` normalises `⟨z⟩`, because `z` commutes with `V` elementwise.
  have hVnorm : V ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    have hzcent : z ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hcomm v hv
    have hZle : Subgroup.zpowers z ≤ Subgroup.centralizer (V : Set G) :=
      Subgroup.zpowers_le.mpr hzcent
    exact (Subgroup.le_centralizer_iff.mp hZle).trans
      (Subgroup.centralizer_le_normalizer (Subgroup.zpowers z : Set G))
  constructor
  · have h := Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hVnorm hZinfV
    rw [h, Nat.card_zpowers, hz2, hVcard]
  · intro x hx
    -- rewrite membership in the join as membership in the pointwise product
    have hx' : x ∈ ((Subgroup.zpowers z : Subgroup G) : Set G) * (V : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers z) V hVnorm]
      exact hx
    obtain ⟨a, haZ, b, hbV, hab⟩ := Set.mem_mul.mp hx'
    have hbb : b * b = 1 := by
      have h := hVsq b hbV
      simpa [pow_two] using h
    rcases mem_zpowers_eq_one_or hzz haZ with ha | ha
    · rw [ha, one_mul] at hab
      rw [← hab, pow_two, hbb]
    · rw [ha] at hab
      rw [← hab, pow_two]
      have hbz : b * z = z * b := hcomm b hbV
      calc (z * b) * (z * b) = (z * z) * (b * b) := by
            rw [show (z * b) * (z * b) = z * (b * z) * b by group,
              show b * z = z * b from hbz,
              show z * (z * b) * b = (z * z) * (b * b) by group]
        _ = 1 := by rw [hzz, hbb, one_mul]

/-- **`Work.CORE2B.L29_case_ii_leaf`.**  A central involution `z` of `N` (order two) cannot
coexist with `V ≤ N` of type `(2,2)` meeting `O₂(N)` trivially. -/
theorem L29_case_ii_leaf {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (V N : Subgroup G) (h : Work.CORE2B.L29Hyp B V N)
    (h1 : V ⊓ Work.GW2.pCoreIn 2 N = ⊥) (z : G) (hzN : z ∈ N)
    (hzc : ∀ n ∈ N, n * z = z * n) (hz2 : orderOf z = 2) : False := by
  classical
  -- ## `⟨z⟩` is a normal subgroup of `N` of order two, hence `z ∈ O₂(N)`.
  have hzcenter : (⟨z, hzN⟩ : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  have hnorm : (Subgroup.zpowers (⟨z, hzN⟩ : ↥N)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzcenter)
  have hpgrp : IsPGroup 2 ↥(Subgroup.zpowers (⟨z, hzN⟩ : ↥N)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz2]; norm_num)
  have hle : Subgroup.zpowers (⟨z, hzN⟩ : ↥N) ≤ Work.GW2.pCore 2 ↥N := by
    rw [Work.GW2.pCore]
    haveI := hnorm
    exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hnorm, hpgrp⟩)
  have hzO2 : z ∈ Work.GW2.pCoreIn 2 N := by
    rw [Work.GW2.pCoreIn, Subgroup.mem_map]
    exact ⟨⟨z, hzN⟩, hle (Subgroup.mem_zpowers _), rfl⟩
  -- ## If `z ∈ V` we are done immediately.
  by_cases hzV : z ∈ V
  · have hmem : z ∈ V ⊓ Work.GW2.pCoreIn 2 N := ⟨hzV, hzO2⟩
    rw [h1] at hmem
    have hz1 : z = 1 := Subgroup.mem_bot.mp hmem
    rw [hz1] at hz2
    exact absurd hz2 (by norm_num)
  · -- ## Otherwise `⟨z⟩ ⊔ V` is elementary abelian of order `8` inside `N ≤ G`.
    obtain ⟨hcard, hsq⟩ :=
      card_sup_zpowers_four_of hz2 h.four.1 h.four.2 hzV (fun v hv => hzc v (h.V_le_N hv))
    -- ## Impossible: the Sylow 2-subgroups of `G` are cyclic or dihedral, hence have
    -- 2-rank at most two (`BenderCtx.sylow`).
    exact no_elementary_abelian_eight_of_dihOrCycSylow hctx.sylow
      ⟨Subgroup.zpowers z ⊔ V, hcard, hsq⟩

end Work.CORE2B
