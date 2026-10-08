import Mathlib

namespace Work.BG

open Pointwise
open scoped commutatorElement

/-- **Auxiliary lemma.** If `B` normalizes `K` (equivalently `⁅B, K⁆ ≤ K`), then
`⁅B ⊔ K, B ⊔ K⁆ ≤ ⁅B, B⁆ ⊔ K`: the commutator of `B ⊔ K` with itself is contained in the
join of the commutator of `B` with itself and `K`.

Indeed every element of `B ⊔ K` is a product `b * k`, and the commutator
`⁅b₁ * k₁, b₂ * k₂⁆` expands into a product of terms, each of which lies either in `⁅B, B⁆`
or in `K` (using that `B` normalizes `K`). -/
lemma commutator_sup_le_of_le_normalizer {G : Type*} [Group G] (B K : Subgroup G)
    (hN : B ≤ Subgroup.normalizer (K : Set G)) :
    ⁅B ⊔ K, B ⊔ K⁆ ≤ ⁅B, B⁆ ⊔ K := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxk : x ∈ (↑B : Set G) * (↑K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right B K hN]; exact hx
  have hyk : y ∈ (↑B : Set G) * (↑K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right B K hN]; exact hy
  rw [Set.mem_mul] at hxk hyk
  obtain ⟨b₁, hb₁, k₁, hk₁, rfl⟩ := hxk
  obtain ⟨b₂, hb₂, k₂, hk₂, rfl⟩ := hyk
  show ⁅b₁ * k₁, b₂ * k₂⁆ ∈ ⁅B, B⁆ ⊔ K
  have hBK' : ⁅B, K⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_right.mp hN
  have hKB : ⁅K, B⁆ ≤ K := by rw [Subgroup.commutator_comm]; exact hBK'
  have hKK : ⁅K, K⁆ ≤ K := Subgroup.commutator_le_of_le le_rfl le_rfl
  -- conjugation by an element of `B` preserves `K`
  have conj : ∀ b ∈ B, ∀ z ∈ K, b * z * b⁻¹ ∈ K := fun b hb z hz =>
    (Subgroup.mem_normalizer_iff.mp (hN hb) z).mp hz
  -- `⁅k₁, b₂ * k₂⁆ ∈ K`
  have h1 : ⁅k₁, b₂ * k₂⁆ ∈ K := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hkb : ⁅k₁, b₂⁆ ∈ K := hKB (Subgroup.commutator_mem_commutator hk₁ hb₂)
    have hkk : ⁅k₁, k₂⁆ ∈ K := hKK (Subgroup.commutator_mem_commutator hk₁ hk₂)
    have hc : b₂ * ⁅k₁, k₂⁆ * b₂⁻¹ ∈ K := conj b₂ hb₂ _ hkk
    convert K.mul_mem hkb hc using 1
    group
  have hf1 : b₁ * ⁅k₁, b₂ * k₂⁆ * b₁⁻¹ ∈ K := conj b₁ hb₁ _ h1
  -- `⁅b₁, b₂ * k₂⁆ ∈ ⁅B, B⁆ ⊔ K`
  have h2 : ⁅b₁, b₂ * k₂⁆ ∈ ⁅B, B⁆ ⊔ K := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hbb : ⁅b₁, b₂⁆ ∈ ⁅B, B⁆ := Subgroup.commutator_mem_commutator hb₁ hb₂
    have hbk : ⁅b₁, k₂⁆ ∈ K := hBK' (Subgroup.commutator_mem_commutator hb₁ hk₂)
    have hc : b₂ * ⁅b₁, k₂⁆ * b₂⁻¹ ∈ K := conj b₂ hb₂ _ hbk
    have hp : ⁅b₁, b₂⁆ * (b₂ * ⁅b₁, k₂⁆ * b₂⁻¹) ∈ ⁅B, B⁆ ⊔ K :=
      Subgroup.mul_mem_sup hbb hc
    convert hp using 1
    group
  rw [commutatorElement_mul_left_eq_conj_mul]
  refine mul_mem ?_ h2
  exact Subgroup.mem_sup_right hf1

/- If `B` normalizes `K` and `B ⊓ K = ⊥`, then `B` meets the commutator of `B ⊔ K` with
itself exactly in `⁅B, B⁆`. -/
open Subgroup in
theorem inf_commutator_sup_self {G : Type*} [Group G] (B K : Subgroup G)
    (hBK : ⁅B, K⁆ ≤ K) (hinf : B ⊓ K = ⊥) :
    B ⊓ ⁅B ⊔ K, B ⊔ K⁆ = ⁅B, B⁆ := by
  have hN : B ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr hBK
  have key : ⁅B ⊔ K, B ⊔ K⁆ ≤ ⁅B, B⁆ ⊔ K :=
    commutator_sup_le_of_le_normalizer B K hN
  refine le_antisymm ?_ ?_
  · -- `B ⊓ ⁅B ⊔ K, B ⊔ K⁆ ≤ ⁅B, B⁆`
    refine (inf_le_inf_left B key).trans ?_
    intro x hx
    obtain ⟨hxB, hxX⟩ := hx
    have hBBle : ⁅B, B⁆ ≤ B := Subgroup.commutator_le_of_le le_rfl le_rfl
    have hle : ⁅B, B⁆ ≤ Subgroup.normalizer (K : Set G) := hBBle.trans hN
    -- decompose `x = y * z` with `y ∈ ⁅B, B⁆` and `z ∈ K`
    have hxX' : x ∈ (↑(⁅B, B⁆) : Set G) * (↑K : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right ⁅B, B⁆ K hle]; exact hxX
    rw [Set.mem_mul] at hxX'
    obtain ⟨y, hy, z, hz, hyz⟩ := hxX'
    have hzB : z ∈ B := by
      have h1 : y⁻¹ * x ∈ B := B.mul_mem (B.inv_mem (hBBle hy)) hxB
      have h2 : y⁻¹ * x = z := by rw [← hyz]; group
      rwa [h2] at h1
    have hzbot : z = 1 := by
      have hmem : z ∈ B ⊓ K := ⟨hzB, hz⟩
      rw [hinf] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hx_eq : x = y := by rw [← hyz, hzbot, mul_one]
    rw [hx_eq]; exact hy
  · -- `⁅B, B⁆ ≤ B ⊓ ⁅B ⊔ K, B ⊔ K⁆`
    refine le_inf ?_ ?_
    · exact Subgroup.commutator_le_of_le le_rfl le_rfl
    · exact Subgroup.commutator_mono le_sup_left le_sup_left

end Work.BG
