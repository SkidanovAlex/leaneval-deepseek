import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Prove

theorem normalizerSubgroupOfEquiv {G : Type} [Group G] {N S : Subgroup G}
    (hSN : S ≤ N) (hNS : Subgroup.normalizer (S : Set G) ≤ N) :
    ∃ e : ↥(Subgroup.normalizer (S.subgroupOf N : Set ↥N)) ≃* ↥(Subgroup.normalizer (S : Set G)),
      (∀ x, (e x : G) = (x : G)) ∧
      (∀ y, ((e.symm y : ↥(Subgroup.normalizer (S.subgroupOf N : Set ↥N))) : G) = (y : G)) := by
  -- membership of an element of `↥N` in `S.subgroupOf N` is membership of its image in `S`
  have mem_sub : ∀ (n : ↥N), n ∈ (S.subgroupOf N : Set ↥N) ↔ (n : G) ∈ S := by
    intro n; exact Subgroup.mem_subgroupOf
  -- the underlying element of `G` of any `x ∈ N_N(S)` lies in `N_G(S)`
  have key1 : ∀ x : ↥(Subgroup.normalizer (S.subgroupOf N : Set ↥N)),
      ((x : ↥N) : G) ∈ Subgroup.normalizer (S : Set G) := by
    intro x
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hN : h ∈ N := hSN hh
      have hmem : (⟨h, hN⟩ : ↥N) ∈ (S.subgroupOf N : Set ↥N) := (mem_sub _).mpr hh
      have hx := (Subgroup.mem_set_normalizer_iff.mp x.2) (⟨h, hN⟩ : ↥N)
      have hconj : ((x : ↥N) * (⟨h, hN⟩ : ↥N) * (x : ↥N)⁻¹ : ↥N) ∈
          (S.subgroupOf N : Set ↥N) := hx.mp hmem
      rw [mem_sub] at hconj
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hconj
    · intro hh
      have hxN : ((x : ↥N) : G) ∈ N := (x : ↥N).2
      have hmemN : ((x : ↥N) : G) * h * (((x : ↥N) : G))⁻¹ ∈ N := hSN hh
      have hN : h ∈ N := by
        have heq : h = (((x : ↥N) : G))⁻¹ *
            (((x : ↥N) : G) * h * (((x : ↥N) : G))⁻¹) * ((x : ↥N) : G) := by group
        rw [heq]
        exact N.mul_mem (N.mul_mem (N.inv_mem hxN) hmemN) hxN
      have hiff := (Subgroup.mem_set_normalizer_iff.mp x.2) (⟨h, hN⟩ : ↥N)
      have hconj : ((x : ↥N) * (⟨h, hN⟩ : ↥N) * (x : ↥N)⁻¹ : ↥N) ∈
          (S.subgroupOf N : Set ↥N) := by
        rw [mem_sub]
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hh
      exact (mem_sub _).mp (hiff.mpr hconj)
  -- the converse: an element of `N_G(S)` (which lies in `N`) gives an element of `N_N(S)`
  have key2 : ∀ y : ↥(Subgroup.normalizer (S : Set G)),
      (⟨(y : G), hNS y.2⟩ : ↥N) ∈ Subgroup.normalizer (S.subgroupOf N : Set ↥N) := by
    intro y
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    have hy := (Subgroup.mem_set_normalizer_iff.mp y.2) (n : G)
    rw [mem_sub n, mem_sub _]
    rw [show (((⟨(y : G), hNS y.2⟩ : ↥N) * n * (⟨(y : G), hNS y.2⟩ : ↥N)⁻¹ : ↥N) : G)
          = (y : G) * (n : G) * (y : G)⁻¹ by simp [Subgroup.coe_mul]]
    exact hy
  let toFun : ↥(Subgroup.normalizer (S.subgroupOf N : Set ↥N)) →
      ↥(Subgroup.normalizer (S : Set G)) :=
    fun x => ⟨((x : ↥N) : G), key1 x⟩
  let invFun : ↥(Subgroup.normalizer (S : Set G)) →
      ↥(Subgroup.normalizer (S.subgroupOf N : Set ↥N)) :=
    fun y => ⟨⟨(y : G), hNS y.2⟩, key2 y⟩
  have left_inv : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have right_inv : Function.RightInverse invFun toFun := by
    intro y
    apply Subtype.ext
    rfl
  have map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y := by
    intro x y
    apply Subtype.ext
    simp [toFun, Subgroup.coe_mul]
  refine ⟨MulEquiv.mk (Equiv.mk toFun invFun left_inv right_inv) map_mul, ?_, ?_⟩
  · intro x
    rfl
  · intro y
    rfl

end Work.ThmF.Prove
