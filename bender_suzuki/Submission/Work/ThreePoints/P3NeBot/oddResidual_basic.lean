import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Basic properties of the odd residual `O^{2'}(G)`

For a finite group `G`, the odd residual

`Submission.Blueprint.oddResidual G = sInf {N : Subgroup G | N.Normal ∧ Odd N.index}`

is normal, has odd index, is contained in every normal subgroup of odd index, and contains
every involution of `G`.

The nontrivial point is that this intersection again has odd index.  Since `G` is finite the
collection of normal subgroups of odd index is closed under binary intersections (the diagonal
map `G → G ⧸ N₁ × G ⧸ N₂` has kernel `N₁ ⊓ N₂`, so `[G : N₁ ⊓ N₂]` divides the odd number
`[G : N₁] * [G : N₂]`), there is a member `N₀` of minimal order; minimality forces `N₀ ≤ N` for
every member `N`, so the intersection is the single subgroup `N₀`.  An involution `x ∉ N₀`
would produce an element of order `2` in the quotient `G ⧸ N₀`, whose order `[G : N₀]` is odd.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ThreePoints.P3NeBot

open Submission.Blueprint

/-- The intersection of two normal subgroups of odd index again has odd index.

Indeed the diagonal map `G →* G ⧸ N₁ × G ⧸ N₂` has kernel `N₁ ⊓ N₂`, so
`(N₁ ⊓ N₂).index = Nat.card f.range` divides `Nat.card (G ⧸ N₁ × G ⧸ N₂)`
`= N₁.index * N₂.index`, an odd number. -/
theorem odd_index_inf {G : Type} [Group G] [Finite G] {N₁ N₂ : Subgroup G}
    (h₁ : N₁.Normal) (h₂ : N₂.Normal) (ho₁ : Odd N₁.index) (ho₂ : Odd N₂.index) :
    Odd (N₁ ⊓ N₂).index := by
  haveI := h₁
  haveI := h₂
  let f : G →* (G ⧸ N₁) × (G ⧸ N₂) := (QuotientGroup.mk' N₁).prod (QuotientGroup.mk' N₂)
  have hker : f.ker = N₁ ⊓ N₂ := by
    ext x
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hidx : (N₁ ⊓ N₂).index = Nat.card f.range := by
    rw [← hker, Subgroup.index_ker]
  rw [hidx]
  refine Odd.of_dvd_nat ?_ (Subgroup.card_subgroup_dvd_card f.range)
  rw [Nat.card_prod, ← Subgroup.index_eq_card N₁, ← Subgroup.index_eq_card N₂]
  exact ho₁.mul ho₂

/-- Every involution lies in every normal subgroup of odd index: its image in the odd order
quotient `G ⧸ N` has order dividing both `2` and the odd number `[G : N]`, hence is trivial. -/
theorem involution_mem_of_odd_index {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (hN : N.Normal) (ho : Odd N.index) {x : G} (hx : x * x = 1) : x ∈ N := by
  haveI := hN
  have hq : QuotientGroup.mk' N x = 1 := by
    apply orderOf_eq_one_iff.mp
    have hdvd2 : orderOf (QuotientGroup.mk' N x) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rw [sq, ← map_mul, hx, map_one]
    have hodd : Odd (orderOf (QuotientGroup.mk' N x)) :=
      Odd.of_dvd_nat (by rw [← Subgroup.index_eq_card]; exact ho) (orderOf_dvd_natCard _)
    have hle : orderOf (QuotientGroup.mk' N x) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    obtain ⟨k, hk⟩ := hodd
    omega
  exact (QuotientGroup.eq_one_iff x).mp hq

/-- `O^{2'}(G)` is normal of odd index, is contained in every normal subgroup of odd index,
and contains every involution of `G`. -/
theorem oddResidual_basic {G : Type} [Group G] [Finite G] :
    (Submission.Blueprint.oddResidual G).Normal ∧
      Odd (Submission.Blueprint.oddResidual G).index ∧
      (∀ N : Subgroup G, N.Normal → Odd N.index → Submission.Blueprint.oddResidual G ≤ N) ∧
      (∀ x : G, x * x = 1 → x ∈ Submission.Blueprint.oddResidual G) := by
  set S : Set (Subgroup G) := {N | N.Normal ∧ Odd N.index} with hS
  have htop : (⊤ : Subgroup G) ∈ S :=
    ⟨Subgroup.normal_top, by rw [Subgroup.index_top]; exact odd_one⟩
  have hres : Submission.Blueprint.oddResidual G = sInf S := rfl
  -- a member of `S` of minimal order
  obtain ⟨N₀, hN₀S, hN₀min⟩ : ∃ N₀ ∈ S, ∀ N ∈ S, Nat.card N₀ ≤ Nat.card N := by
    have hne : ((fun N : Subgroup G => Nat.card N) '' S).Nonempty :=
      ⟨(fun N : Subgroup G => Nat.card N) ⊤, ⊤, htop, rfl⟩
    obtain ⟨N₀, hN₀S, hN₀eq⟩ := Nat.sInf_mem hne
    refine ⟨N₀, hN₀S, fun N hN => ?_⟩
    change (fun M : Subgroup G => Nat.card M) N₀ ≤ (fun M : Subgroup G => Nat.card M) N
    rw [hN₀eq]
    exact Nat.sInf_le ⟨N, hN, rfl⟩
  -- minimality forces `N₀ ≤ N` for every `N ∈ S`
  have hle_of_mem : ∀ N ∈ S, N₀ ≤ N := by
    intro N hN
    haveI : N₀.Normal := hN₀S.1
    haveI : N.Normal := hN.1
    have hmem : N₀ ⊓ N ∈ S :=
      ⟨Subgroup.normal_inf_normal N₀ N, odd_index_inf hN₀S.1 hN.1 hN₀S.2 hN.2⟩
    have hcard : Nat.card ↥(N₀ ⊓ N) = Nat.card ↥N₀ :=
      le_antisymm (Subgroup.card_le_of_le inf_le_left) (hN₀min _ hmem)
    have heq : N₀ ⊓ N = N₀ := Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcard.symm)
    calc N₀ = N₀ ⊓ N := heq.symm
      _ ≤ N := inf_le_right
  have hres_eq : Submission.Blueprint.oddResidual G = N₀ := by
    rw [hres]
    exact le_antisymm (sInf_le hN₀S) (le_sInf hle_of_mem)
  exact ⟨by rw [hres_eq]; exact hN₀S.1, by rw [hres_eq]; exact hN₀S.2,
    fun N hN1 hN2 => by rw [hres_eq]; exact hle_of_mem N ⟨hN1, hN2⟩,
    fun x hx => by rw [hres_eq]; exact involution_mem_of_odd_index hN₀S.1 hN₀S.2 hx⟩

end Work.ThreePoints.P3NeBot
