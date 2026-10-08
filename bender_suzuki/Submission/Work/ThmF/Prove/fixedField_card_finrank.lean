import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Prove

/-- An element is fixed by an algebra automorphism `σ` iff it lies in the `⟨σ⟩`-fixed field:
being fixed by `σ` is the same as being fixed by every power of `σ`. -/
private theorem mem_fixedPoints_iff_mem_fixedField_zpowers {p : ℕ} [Fact p.Prime] {F : Type}
    [Field F] [Algebra (ZMod p) F] (σ : F ≃ₐ[ZMod p] F) (x : F) :
    x ∈ Function.fixedPoints σ ↔ x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := by
  rw [IntermediateField.mem_fixedField_iff, Subgroup.forall_mem_zpowers, Function.mem_fixedPoints]
  constructor
  · intro hx m
    have hmem : x ∈ MulAction.fixedBy F σ := by
      rw [MulAction.mem_fixedBy, AlgEquiv.smul_def]; exact hx.eq
    have := MulAction.mem_fixedBy_zpow hmem m
    rwa [MulAction.mem_fixedBy, AlgEquiv.smul_def] at this
  · intro h
    show (⇑σ) x = x
    simpa using h 1

theorem fixedField_card_finrank (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Fintype F]
    [CharP F p] [Algebra (ZMod p) F] (σ : F ≃ₐ[ZMod p] F) :
    Nat.card (Function.fixedPoints σ) =
        p ^ Module.finrank (ZMod p) (IntermediateField.fixedField (Subgroup.zpowers σ)) ∧
      Module.finrank (ZMod p) (IntermediateField.fixedField (Subgroup.zpowers σ)) * orderOf σ =
        Module.finrank (ZMod p) F := by
  have : Module.Finite (ZMod p) F := Module.Finite.of_finite
  refine ⟨?_, ?_⟩
  · -- `F` is a finite field of characteristic `p`, so `Nat.card K = p ^ finrank K`; the fixed
    -- points of `σ` are exactly the elements of the fixed field `K = F ^ ⟨σ⟩`.
    rw [FiniteField.pow_finrank_eq_natCard p
      (IntermediateField.fixedField (Subgroup.zpowers σ))]
    exact Nat.card_congr
      (Equiv.subtypeEquivRight (fun x => mem_fixedPoints_iff_mem_fixedField_zpowers σ x))
  · -- Tower law: `[F : 𝔽_p] = [F : K] * [K : 𝔽_p]` and (Artin) `[F : K] = |⟨σ⟩| = orderOf σ`.
    have hcard : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) F = orderOf σ := by
      rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
    have htower := Module.finrank_mul_finrank (ZMod p)
      (IntermediateField.fixedField (Subgroup.zpowers σ)) F
    rw [hcard] at htower
    exact htower

end Work.ThmF.Prove
