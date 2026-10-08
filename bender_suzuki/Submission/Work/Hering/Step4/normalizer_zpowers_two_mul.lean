import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The normalizer of a cyclic subgroup of order `3` inverted by conjugation

If `z` has order `3` and some `g` satisfies `g * z * g⁻¹ = z⁻¹`, then
`N_G(⟨z⟩)` is the union of the two cosets `C_G(z)` and `g · C_G(z)`, and these are disjoint.
Hence `|N_G(⟨z⟩)| = 2 * |C_G(z)|`.

The mathematical content: `N_G(⟨z⟩)/C_G(z)` embeds into `Aut(⟨z⟩) ≅ (ℤ/3)^* ≅ ℤ/2`; the
hypothesis that `z` is inverted by a conjugating element says the image is the full `ℤ/2`.

The proof below makes this explicit rather than passing through the automorphism group: an
element of `N_G(⟨z⟩)` conjugates `z` to `z` or to `z⁻¹`, because `⟨z⟩ = {1, z, z⁻¹}`.
-/

namespace Work.Hering.Step4

/-- Conjugation by an element `g` with `g * z * g⁻¹ = z⁻¹` sends each power of `z` to the
opposite power. -/
private lemma conj_zpow_eq_inv_zpow {G : Type*} [Group G] {z g : G}
    (hg : g * z * g⁻¹ = z⁻¹) (k : ℤ) : g * z ^ k * g⁻¹ = z ^ (-k) := by
  calc g * z ^ k * g⁻¹ = (MulAut.conj g) (z ^ k) := by rw [MulAut.conj_apply]
    _ = ((MulAut.conj g) z) ^ k := by rw [map_zpow]
    _ = (z⁻¹) ^ k := by rw [MulAut.conj_apply, hg]
    _ = z ^ (-k) := inv_zpow' z k

/-- An element commuting with `z` normalises `⟨z⟩`. -/
private lemma centralizer_le_normalizer_zpowers {G : Type*} [Group G] (z : G) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  have h1 : Subgroup.centralizer ({z} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [h1]
  exact Subgroup.centralizer_le_normalizer _

/-- If `g * z * g⁻¹ = z⁻¹` then `g` normalises `⟨z⟩`. -/
private lemma mem_normalizer_zpowers_of_conj_eq_inv {G : Type*} [Group G] {z g : G}
    (hg : g * z * g⁻¹ = z⁻¹) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  -- conjugation by `g⁻¹` also sends `z` to `z⁻¹`
  have hgi : g⁻¹ * z * g = z⁻¹ := by
    have h : z = g⁻¹ * z⁻¹ * g := by
      have hh : g⁻¹ * (g * z * g⁻¹) * g = g⁻¹ * z⁻¹ * g :=
        congrArg (fun t : G => g⁻¹ * t * g) hg
      rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at hh
    have h2 : z⁻¹ = g⁻¹ * z * g := by
      have hh : z⁻¹ = (g⁻¹ * z⁻¹ * g)⁻¹ := congrArg (fun t : G => t⁻¹) h
      rwa [show (g⁻¹ * z⁻¹ * g)⁻¹ = g⁻¹ * z * g by group] at hh
    exact h2.symm
  have hconj' : ∀ k : ℤ, g⁻¹ * z ^ k * g = z ^ (-k) := by
    intro k
    calc g⁻¹ * z ^ k * g = (MulAut.conj g⁻¹) (z ^ k) := by rw [MulAut.conj_apply, inv_inv]
      _ = ((MulAut.conj g⁻¹) z) ^ k := by rw [map_zpow]
      _ = (z⁻¹) ^ k := by rw [MulAut.conj_apply, inv_inv, hgi]
      _ = z ^ (-k) := inv_zpow' z k
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact Subgroup.mem_zpowers_iff.mpr ⟨-k, (conj_zpow_eq_inv_zpow hg k).symm⟩
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    calc z ^ (-k) = g⁻¹ * z ^ k * g := (hconj' k).symm
      _ = g⁻¹ * (g * h * g⁻¹) * g := by rw [← hk]
      _ = h := by group

/-- In a cyclic group of order `3`, the elements of order `3` are `z` and `z⁻¹`. -/
private lemma eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three {G : Type*} [Group G] [Finite G]
    {z w : G} (hz : orderOf z = 3) (hw : orderOf w = 3) (hwZ : w ∈ Subgroup.zpowers z) :
    w = z ∨ w = z⁻¹ := by
  classical
  have hmem : ∃ n ∈ Finset.range (orderOf z), z ^ n = w :=
    Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf (x := z) (y := w)).mp hwZ)
  obtain ⟨n, hn, hnw⟩ := hmem
  rw [hz, Finset.mem_range] at hn
  interval_cases n
  · exfalso
    have hw1 : w = 1 := by rw [← hnw]; exact pow_zero z
    rw [hw1] at hw
    simp only [orderOf_one] at hw
    omega
  · left
    rw [pow_one] at hnw
    exact hnw.symm
  · right
    rw [← hnw, pow_two]
    have hz3 : z ^ 3 = 1 := by simpa [hz] using pow_orderOf_eq_one z
    have hzz : z * z * z = 1 := by
      have h : z ^ 3 = z * z * z := by
        calc z ^ 3 = z ^ (2 + 1) := rfl
          _ = z ^ 2 * z := pow_succ z 2
          _ = (z * z) * z := by rw [pow_two]
      rwa [h] at hz3
    exact mul_eq_one_iff_eq_inv.mp hzz

/-- An element of `N_G(⟨z⟩)` conjugates `z` to `z` or to `z⁻¹`. -/
private lemma conj_eq_or_inv_of_mem_normalizer {G : Type*} [Group G] [Finite G] {z x : G}
    (hz : orderOf z = 3)
    (hxN : x ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) :
    x * z * x⁻¹ = z ∨ x * z * x⁻¹ = z⁻¹ := by
  have hmem : x * z * x⁻¹ ∈ Subgroup.zpowers z :=
    (Subgroup.mem_normalizer_iff.mp hxN z).mp (Subgroup.mem_zpowers z)
  have hord : orderOf (x * z * x⁻¹) = 3 := by
    have hsem : SemiconjBy x z (x * z * x⁻¹) := by
      show x * z = (x * z * x⁻¹) * x
      group
    rw [← SemiconjBy.orderOf_eq x hsem, hz]
  exact eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hz hord hmem

theorem normalizer_zpowers_two_mul {G : Type*} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 3) (h : ∃ g : G, g * z * g⁻¹ = z⁻¹) :
    Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G))
      = 2 * Nat.card ↥(Subgroup.centralizer ({z} : Set G)) := by
  classical
  obtain ⟨g, hg⟩ := h
  set N : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) with hN
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hCN : C ≤ N := by
    rw [hC, hN]
    exact centralizer_le_normalizer_zpowers z
  have hgN : g ∈ N := by
    rw [hN]
    exact mem_normalizer_zpowers_of_conj_eq_inv hg
  have hgC : g ∉ C := by
    rw [hC]
    intro hcomm
    rw [Subgroup.mem_centralizer_singleton_iff] at hcomm
    have h1 : z = z⁻¹ := by rw [← hg, hcomm]; group
    have hz2 : z ^ 2 = 1 := by
      rw [pow_two]
      exact (congrArg (fun t : G => z * t) h1).trans (mul_inv_cancel z)
    have hdvd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
    rw [hz] at hdvd
    omega
  have hunion : (N : Set G) = (C : Set G) ∪ (fun y : G => g * y) '' (C : Set G) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
        rw [← hN]; exact hx
      rcases conj_eq_or_inv_of_mem_normalizer hz hx' with hxz | hxz
      · left
        rw [hC]
        have hh : (x * z * x⁻¹) * x = z * x := congrArg (fun t : G => t * x) hxz
        have h2 : x * z = z * x := by
          rwa [show x * z * x⁻¹ * x = x * z by group] at hh
        exact Subgroup.mem_centralizer_singleton_iff.mpr h2
      · right
        have hxz' : x * z = z⁻¹ * x := by
          have hh : (x * z * x⁻¹) * x = z⁻¹ * x := congrArg (fun t : G => t * x) hxz
          rwa [show x * z * x⁻¹ * x = x * z by group] at hh
        have hg'' : g⁻¹ * z⁻¹ = z * g⁻¹ := by
          have hrel : z = g⁻¹ * z⁻¹ * g := by
            have hh : g⁻¹ * (g * z * g⁻¹) * g = g⁻¹ * z⁻¹ * g :=
              congrArg (fun t : G => g⁻¹ * t * g) hg
            rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at hh
          calc g⁻¹ * z⁻¹ = g⁻¹ * z⁻¹ * (g * g⁻¹) := by group
            _ = (g⁻¹ * z⁻¹ * g) * g⁻¹ := by group
            _ = z * g⁻¹ := by rw [← hrel]
        refine ⟨g⁻¹ * x, ?_, ?_⟩
        · rw [hC]
          have h2 : (g⁻¹ * x) * z = z * (g⁻¹ * x) := by
            calc (g⁻¹ * x) * z = g⁻¹ * (x * z) := by group
              _ = g⁻¹ * (z⁻¹ * x) := by rw [hxz']
              _ = (g⁻¹ * z⁻¹) * x := by group
              _ = (z * g⁻¹) * x := by rw [hg'']
              _ = z * (g⁻¹ * x) := by group
          exact Subgroup.mem_centralizer_singleton_iff.mpr h2
        · group
    · rintro (hx | ⟨y, hy, rfl⟩)
      · exact hCN hx
      · exact N.mul_mem hgN (hCN hy)
  have hdisj : Disjoint (C : Set G) ((fun y : G => g * y) '' (C : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hxC ⟨y, hyC, rfl⟩
    refine hgC ?_
    have hge : g = (g * y) * y⁻¹ := by group
    rw [hge]
    exact C.mul_mem hxC (C.inv_mem hyC)
  have hcard : (N : Set G).ncard = 2 * (C : Set G).ncard := by
    rw [hunion, Set.ncard_union_eq hdisj,
      Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab)]
    ring
  calc Nat.card ↥N = (N : Set G).ncard := Nat.card_coe_set_eq (N : Set G)
    _ = 2 * (C : Set G).ncard := hcard
    _ = 2 * Nat.card ↥C := rfl

end Work.Hering.Step4
