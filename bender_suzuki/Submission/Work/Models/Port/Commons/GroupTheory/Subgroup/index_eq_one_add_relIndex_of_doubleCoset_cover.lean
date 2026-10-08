import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_doubleCoset_mul
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.relIndex_mul_card_of_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem index_eq_one_add_relIndex_of_doubleCoset_cover {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (w : G)
    (hcover : ∀ g : G, g ∈ B ∨ ∃ b₁ b₂ : ↥B, g = (b₁ : G) * w * (b₂ : G))
    (hw : w ∉ B) :
    B.index = 1 + (B ⊓ B.map (MulAut.conj w).toMonoidHom).relIndex B := by
  haveI : Fintype G := Fintype.ofFinite G
  set N : Subgroup G := B ⊓ B.map (MulAut.conj w).toMonoidHom with hN
  set S : Set G := {y : G | ∃ a b : ↥B, y = (a : G) * w * (b : G)} with hS
  -- `1 ∈ N`
  have h1N : (1 : G) ∈ N := by
    rw [hN, Subgroup.mem_inf]
    exact ⟨B.one_mem, Subgroup.mem_map.mpr ⟨1, B.one_mem, by simp [MulAut.conj_apply]⟩⟩
  have hNpos : 0 < Nat.card ↥N :=
    Nat.card_pos_iff.mpr ⟨⟨1, h1N⟩, inferInstance⟩
  have hBpos : 0 < Nat.card ↥B :=
    Nat.card_pos_iff.mpr ⟨⟨1, B.one_mem⟩, inferInstance⟩
  -- `B` and `S` are disjoint
  have hdisj : Disjoint (B : Set G) S := by
    rw [Set.disjoint_left]
    intro g hgB hgS
    rw [hS] at hgS
    obtain ⟨b₁, b₂, rfl⟩ := hgS
    apply hw
    have hmem : (b₁ : G)⁻¹ * ((b₁ : G) * w * (b₂ : G)) * (b₂ : G)⁻¹ ∈ B :=
      B.mul_mem (B.mul_mem (B.inv_mem b₁.2) hgB) (B.inv_mem b₂.2)
    have heq : (b₁ : G)⁻¹ * ((b₁ : G) * w * (b₂ : G)) * (b₂ : G)⁻¹ = w := by group
    rwa [heq] at hmem
  -- `B ∪ S = G`
  have hunion : (B : Set G) ∪ S = Set.univ := by
    ext g
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rcases hcover g with h | h
    · exact Or.inl h
    · rw [hS]
      exact Or.inr h
  -- `|G| = |B| + |S|`
  have hcardG : Nat.card G = Nat.card ↥B + Nat.card ↥S := by
    have h := Set.ncard_union_eq hdisj
    rw [hunion] at h
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq] at h
    exact h
  -- `|S| * |N| = |B| * |B|`
  have hcardS : Nat.card ↥S * Nat.card ↥N = Nat.card ↥B * Nat.card ↥B := by
    rw [hS, hN]
    exact card_doubleCoset_mul B w
  -- `|B| = N.relIndex B * |N|`
  have hBN : N.relIndex B * Nat.card ↥N = Nat.card ↥B :=
    relIndex_mul_card_of_le (by rw [hN]; exact inf_le_left)
  -- `|S| = |B| * N.relIndex B`
  have hNS : Nat.card ↥S = Nat.card ↥B * N.relIndex B := by
    apply Nat.mul_right_cancel hNpos
    rw [hcardS, ← hBN]
    ring
  -- finish
  have key : B.index * Nat.card ↥B = (1 + N.relIndex B) * Nat.card ↥B := by
    rw [Subgroup.index_mul_card, hcardG, hNS]
    ring
  exact Nat.mul_right_cancel hBpos key

end Commons.GroupTheory.Subgroup
