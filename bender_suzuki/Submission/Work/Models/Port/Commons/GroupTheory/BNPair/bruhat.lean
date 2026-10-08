import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.BNPair

open MulAction

/-- In the coset space `G ⧸ B`, the class of `x` is the class of `1` iff `x ∈ B`. -/
lemma quotient_mk_one_iff {G : Type*} [Group G] (B : Subgroup G) (x : G) :
    (QuotientGroup.mk x : G ⧸ B) = QuotientGroup.mk (1 : G) ↔ x ∈ B := by
  rw [QuotientGroup.eq]
  simp

/-- `G` acts on `G ⧸ B` by left multiplication. -/
lemma smul_quotient_mk {G : Type*} [Group G] (B : Subgroup G) (g x : G) :
    g • (QuotientGroup.mk x : G ⧸ B) = QuotientGroup.mk (g * x) := rfl

/-- **Bruhat decomposition**, rank-one form.  If a group `G` acts `2`-pretransitively on the
coset space `G ⧸ B` and `w ∉ B`, then `G = B ∪ B w B`.  (This is the rank-one Bruhat
decomposition attached to a saturated BN-pair of rank one.) -/
theorem bruhat {G : Type*} [Group G] (B : Subgroup G) (w : G) (hw : w ∉ B)
    [MulAction.IsMultiplyPretransitive G (G ⧸ B) 2] :
    ∀ g : G, g ∈ B ∨ ∃ b₁ b₂ : ↥B, g = (b₁ : G) * w * (b₂ : G) := by
  intro g
  by_cases hg : g ∈ B
  · exact Or.inl hg
  · right
    have h2 : ∀ {a b c d : G ⧸ B}, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d :=
      (MulAction.is_two_pretransitive_iff (G := G) (α := G ⧸ B)).mp inferInstance
    have hpw : (QuotientGroup.mk (1:G) : G ⧸ B) ≠ w • (QuotientGroup.mk (1:G) : G ⧸ B) := by
      intro hcontra
      apply hw
      rw [smul_quotient_mk, mul_one] at hcontra
      exact (quotient_mk_one_iff B w).mp hcontra.symm
    have hpg : (QuotientGroup.mk (1:G) : G ⧸ B) ≠ g • (QuotientGroup.mk (1:G) : G ⧸ B) := by
      intro hcontra
      apply hg
      rw [smul_quotient_mk, mul_one] at hcontra
      exact (quotient_mk_one_iff B g).mp hcontra.symm
    obtain ⟨h, hhp, hhw⟩ := h2 hpw hpg
    have hhB : h ∈ B := by
      rw [smul_quotient_mk, mul_one] at hhp
      exact (quotient_mk_one_iff B h).mp hhp
    have hbB : (h * w)⁻¹ * g ∈ B := by
      rw [smul_smul] at hhw
      simp only [smul_quotient_mk, mul_one] at hhw
      exact (QuotientGroup.eq).mp hhw
    refine ⟨⟨h, hhB⟩, ⟨(h*w)⁻¹ * g, hbB⟩, ?_⟩
    group

end Commons.GroupTheory.BNPair