import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open QuotientGroup

namespace Commons.GroupTheory.GroupAction

variable {G : Type*} [Group G]

/-- Action formula on representatives for the left coset action:
`g • (xB) = (gx)B`. -/
@[simp]
lemma coset_smul_mk (B : Subgroup G) (g x : G) : g • (x : G ⧸ B) = (g * x : G ⧸ B) := by
  simp [smul_eq_mul]

/-- The orbit structure of `B` on the left coset space `G ⧸ B` is governed by
the double cosets of `B`: two cosets whose representatives lie **outside** `B`
are in the same orbit of `B` whenever `G` is the union of `B` and the single
double coset `B·w·B`.

Concretely: if `u, v ∉ B` and `G = B ∪ B·w·B`, then `v` lies in the double
coset `B·u·B`. -/
lemma doubleCoset_of_not_mem (B : Subgroup G) (w : G)
    (hcov : ∀ g : G, g ∈ B ∨ ∃ b₁ b₂ : ↥B, g = (b₁ : G) * w * (b₂ : G))
    {u v : G} (hu : u ∉ B) (hv : v ∉ B) :
    ∃ b₁ b₂ : ↥B, v = (b₁ : G) * u * (b₂ : G) := by
  have hv' : ∃ b₁ b₂ : ↥B, v = (b₁ : G) * w * (b₂ : G) := (hcov v).resolve_left hv
  obtain ⟨β₁, β₂, hvβ⟩ := hv'
  have hu' : ∃ b₁ b₂ : ↥B, u = (b₁ : G) * w * (b₂ : G) := (hcov u).resolve_left hu
  obtain ⟨α₁, α₂, huα⟩ := hu'
  have hw : w = (α₁ : G)⁻¹ * u * (α₂ : G)⁻¹ := by
    rw [huα]
    group
  refine ⟨β₁ * α₁⁻¹, α₂⁻¹ * β₂, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hvβ, hw]
  group

/-- Bender's double-coset decomposition `G = B ∪ B·w·B` makes the left coset
action of `G` on `G ⧸ B` doubly transitive.

Given two distinct cosets `a₀B ≠ b₀B` and `c₀B ≠ d₀B`, the differences
`u = a₀⁻¹b₀` and `v = c₀⁻¹d₀` both lie outside `B`; the double-coset lemma
above then supplies `v = x₁·u·x₂` with `x₁, x₂ ∈ B`.  The single element
`g = c₀·x₁·a₀⁻¹` maps `a₀B` to `c₀B` (because `x₁ ∈ B` fixes the coset on the
right) and maps `b₀B` to `d₀B` (because `c₀⁻¹d₀ = x₁·a₀⁻¹b₀·x₂`).  By
`MulAction.is_two_pretransitive_iff` this is exactly 2-pretransitivity of the
left coset action. -/
theorem coset_multiplyPretransitive_two_of_two_doubleCosets {G : Type*} [Group G]
    (B : Subgroup G) (w : G)
    (hcov : ∀ g : G, g ∈ B ∨ ∃ b₁ b₂ : ↥B, g = (b₁ : G) * w * (b₂ : G)) :
    MulAction.IsMultiplyPretransitive G (G ⧸ B) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  induction c using QuotientGroup.induction_on with
  | _ c0 =>
  induction d using QuotientGroup.induction_on with
  | _ d0 =>
  induction a using QuotientGroup.induction_on with
  | _ a0 =>
  induction b using QuotientGroup.induction_on with
  | _ b0 =>
    -- the distinctness of cosets means the difference elements lie outside B
    have hu : a0⁻¹ * b0 ∉ B := by
      intro h
      apply hab
      rw [QuotientGroup.eq]
      exact h
    have hv : c0⁻¹ * d0 ∉ B := by
      intro h
      apply hcd
      rw [QuotientGroup.eq]
      exact h
    -- v = x₁ · u · x₂ with x₁, x₂ ∈ B
    obtain ⟨x₁, x₂, hvx⟩ := doubleCoset_of_not_mem B w hcov hu hv
    -- the desired element: move `a₀B` to `c₀B` and `b₀B` to `d₀B`
    refine ⟨c0 * (x₁ : G) * (a0 : G)⁻¹, ?_, ?_⟩
    · rw [coset_smul_mk]
      have hgrp : c0 * (x₁ : G) * (a0 : G)⁻¹ * a0 = c0 * (x₁ : G) := by group
      rw [hgrp]
      exact QuotientGroup.mk_mul_of_mem c0 x₁.2
    · rw [coset_smul_mk]
      rw [QuotientGroup.eq]
      have hmain : (c0 * (x₁ : G) * (a0 : G)⁻¹ * b0)⁻¹ * d0 = (x₂ : G) := by
        calc
          (c0 * (x₁ : G) * (a0 : G)⁻¹ * b0)⁻¹ * d0
              = b0⁻¹ * a0 * (x₁ : G)⁻¹ * c0⁻¹ * d0 := by group
          _ = b0⁻¹ * a0 * (x₁ : G)⁻¹ * (c0⁻¹ * d0) := by group
          _ = b0⁻¹ * a0 * (x₁ : G)⁻¹ *
                ((x₁ : G) * (a0⁻¹ * b0) * (x₂ : G)) := by rw [hvx]
          _ = (x₂ : G) := by group
      rw [hmain]
      exact x₂.2

end Commons.GroupTheory.GroupAction