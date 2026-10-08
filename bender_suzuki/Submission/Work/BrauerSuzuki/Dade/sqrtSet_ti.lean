import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two
import Submission.Work.BrauerSuzuki.Dade.complement_and_sqrtSet

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Dade

open Classical

/-!
# Dade's Proposition 5.12: `√σ` is a TI set with normalizer `N_G(⟨σ⟩)`

For `σ ≠ 1` in a finite group `G`, the set `√σ = {τ | σ ∈ ⟨τ⟩}` of "roots of `σ`" is a TI set
(trivial intersection set) with normalizer `N_G(⟨σ⟩)`.

The substance is `conj_disjoint`: if `g x g⁻¹ = y` with `x, y ∈ √σ`, then `⟨σ⟩ ≤ ⟨x⟩` and
`g⁻¹⟨σ⟩g ≤ ⟨x⟩`, so `⟨σ⟩` and `g⁻¹⟨σ⟩g` are subgroups of the *cyclic* group `⟨x⟩` of the same
finite order, hence equal, and `g ∈ N_G(⟨σ⟩)`.
-/

/-- An element of `⟨b⟩` commutes with `b`. -/
private lemma commute_of_mem_zpowers {G : Type*} [Group G] {a b : G}
    (h : a ∈ Subgroup.zpowers b) : Commute a b := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← hk]
  exact (Commute.refl b).zpow_left k

/-- If `a` and `c` both lie in the cyclic group `⟨x⟩` and have the same order, then they
generate the same subgroup. -/
private lemma zpowers_eq_of_mem_zpowers_of_orderOf_eq {G : Type*} [Group G] [Finite G]
    {x a c : G} (ha : a ∈ Subgroup.zpowers x) (hc : c ∈ Subgroup.zpowers x)
    (horder : orderOf a = orderOf c) : Subgroup.zpowers a = Subgroup.zpowers c := by
  set T : Subgroup G := Subgroup.zpowers x with hT
  haveI : IsCyclic ↥T := isCyclic_zpowers_subtype x
  have haT : Subgroup.zpowers a ≤ T := Subgroup.zpowers_le.mpr ha
  have hcT : Subgroup.zpowers c ≤ T := Subgroup.zpowers_le.mpr hc
  have hcard_a : Nat.card ↥((Subgroup.zpowers a).subgroupOf T) =
      Nat.card ↥(Subgroup.zpowers a) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe haT).toEquiv
  have hcard_c : Nat.card ↥((Subgroup.zpowers c).subgroupOf T) =
      Nat.card ↥(Subgroup.zpowers c) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcT).toEquiv
  have heq : (Subgroup.zpowers a).subgroupOf T = (Subgroup.zpowers c).subgroupOf T := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, hcard_a, hcard_c, Nat.card_zpowers, Nat.card_zpowers,
      horder]
  have hinf : Subgroup.zpowers a ⊓ T = Subgroup.zpowers c ⊓ T := Subgroup.subgroupOf_inj.mp heq
  rw [inf_eq_left.mpr haT, inf_eq_left.mpr hcT] at hinf
  exact hinf

/-- `orderOf (g⁻¹ * σ * g) = orderOf σ`. -/
private lemma orderOf_conj_inv_eq {G : Type*} [Group G] (g σ : G) :
    orderOf (g⁻¹ * σ * g) = orderOf σ := by
  simpa using Work.BrauerSuzuki.Group.orderOf_conj_eq g⁻¹ σ

/-- **Dade's Proposition 5.12.**  For `σ ≠ 1` in a finite group, `√σ = {τ | σ ∈ ⟨τ⟩}` is a TI
set with normalizer `N_G (⟨σ⟩)`. -/
theorem sqrtSet_isTISet {G : Type*} [Group G] [Finite G] {σ : G} (hσ : σ ≠ 1) :
    Work.BrauerSuzuki.IsTISet (Work.BrauerSuzuki.sqrtSet σ)
      (Subgroup.normalizer (Subgroup.zpowers σ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Work.BrauerSuzuki.mem_sqrtSet, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot]
    exact hσ
  · intro x hx
    rw [Work.BrauerSuzuki.mem_sqrtSet] at hx
    refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers σ : Subgroup G) : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hm]
    exact ((commute_of_mem_zpowers hx).zpow_left m).eq
  · intro x hx
    rw [Work.BrauerSuzuki.mem_sqrtSet] at hx ⊢
    rwa [Subgroup.zpowers_inv]
  · intro h hh x hx
    rw [Work.BrauerSuzuki.mem_sqrtSet] at hx ⊢
    -- `h⁻¹ σ h ∈ ⟨σ⟩ ≤ ⟨x⟩`, so `σ = h (h⁻¹ σ h) h⁻¹ = (h x h⁻¹) ^ k`
    have hmem : h⁻¹ * σ * h ∈ Subgroup.zpowers σ :=
      (Subgroup.mem_normalizer_iff''.mp hh σ).mp (Subgroup.mem_zpowers σ)
    have hmem' : h⁻¹ * σ * h ∈ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hx hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem'
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : (h * x * h⁻¹) ^ k = h * x ^ k * h⁻¹ := by
      rw [← MulAut.conj_apply h x, ← map_zpow (MulAut.conj h) x k, MulAut.conj_apply]
    rw [h1, hk]
    group
  · intro g hg
    -- `g σ g⁻¹ ∈ √σ` gives `σ = (g σ g⁻¹) ^ k`, hence `g⁻¹ σ g = σ ^ k`
    have hgσ : g * σ * g⁻¹ ∈ Work.BrauerSuzuki.sqrtSet σ := hg (Subgroup.mem_zpowers σ)
    rw [Work.BrauerSuzuki.mem_sqrtSet] at hgσ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgσ
    have h1 : (g * σ * g⁻¹) ^ k = g * σ ^ k * g⁻¹ := by
      rw [← MulAut.conj_apply g σ, ← map_zpow (MulAut.conj g) σ k, MulAut.conj_apply]
    rw [h1] at hk
    have hstep : σ ^ k = g⁻¹ * σ * g := by
      have h2 := congrArg (fun t => g⁻¹ * t * g) hk
      simpa [mul_assoc] using h2
    -- hence `g⁻¹ σ g ∈ ⟨σ⟩` and `⟨g⁻¹ σ g⟩ = ⟨σ⟩`
    have hmem : g⁻¹ * σ * g ∈ Subgroup.zpowers σ :=
      Subgroup.mem_zpowers_iff.mpr ⟨k, hstep⟩
    have heq : Subgroup.zpowers (g⁻¹ * σ * g) = Subgroup.zpowers σ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) (by
        simp [Nat.card_zpowers, orderOf_conj_inv_eq])
    -- so `g⁻¹` normalizes `⟨σ⟩`, hence so does `g`
    have hmap : (Subgroup.zpowers σ).map (MulAut.conj g⁻¹).toMonoidHom = Subgroup.zpowers σ := by
      rw [MonoidHom.map_zpowers]
      simpa [MulAut.conj_apply, inv_inv] using heq
    simpa using Subgroup.inv_mem _ (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap)
  · -- `conj_disjoint`
    intro g hg x y hx hy hxy
    rw [Work.BrauerSuzuki.mem_sqrtSet] at hx hy
    -- `g⁻¹ σ g ∈ ⟨x⟩`
    have hzx : g⁻¹ * σ * g ∈ Subgroup.zpowers x := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have h1 : (g * x * g⁻¹) ^ k = g * x ^ k * g⁻¹ := by
        rw [← MulAut.conj_apply g x, ← map_zpow (MulAut.conj g) x k, MulAut.conj_apply]
      rw [← hxy, h1] at hk
      have h2 := congrArg (fun t => g⁻¹ * t * g) hk
      simpa [mul_assoc] using h2
    -- `⟨σ⟩ = ⟨g⁻¹ σ g⟩`, both being cyclic subgroups of `⟨x⟩` of the same order
    have heq : Subgroup.zpowers σ = Subgroup.zpowers (g⁻¹ * σ * g) :=
      zpowers_eq_of_mem_zpowers_of_orderOf_eq hx hzx (orderOf_conj_inv_eq g σ).symm
    -- hence `g σ g⁻¹ ∈ ⟨σ⟩`, so `g` normalizes `⟨σ⟩`, contradicting `hg`
    have hσmem : σ ∈ Subgroup.zpowers (g⁻¹ * σ * g) := heq ▸ Subgroup.mem_zpowers σ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hσmem
    have hmem : g * σ * g⁻¹ ∈ Subgroup.zpowers σ := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
      have h3 : g * (g⁻¹ * σ * g) ^ j * g⁻¹ = (g * (g⁻¹ * σ * g) * g⁻¹) ^ j := by
        rw [← MulAut.conj_apply g (g⁻¹ * σ * g), ← map_zpow (MulAut.conj g) (g⁻¹ * σ * g) j,
          MulAut.conj_apply]
      rw [hj] at h3
      rw [show g * (g⁻¹ * σ * g) * g⁻¹ = σ from by group] at h3
      exact h3.symm
    have hmap : (Subgroup.zpowers σ).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers σ := by
      rw [MonoidHom.map_zpowers]
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) (by
        rw [Nat.card_zpowers, Nat.card_zpowers]
        exact le_of_eq (Work.BrauerSuzuki.Group.orderOf_conj_eq g σ).symm)
    exact hg (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap)

end Work.BrauerSuzuki.Dade
