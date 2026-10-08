import Mathlib
import Submission.Work.ThreePoints.ThmC.app3_1_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.AppXIShadow

/-- If `K ⊴ F` acts trivially on `Ω`, `A ⊴ F` and `⁅A,A⁆ ≤ K`, then the commutator subgroup of
`A ⊔ K` lies in `K`: indeed `(A ⊔ K)/K ≅ A/(A ⊓ K)` is abelian because `⁅A,A⁆ ≤ A ⊓ K`.
Hence every commutator `x * y * x⁻¹ * y⁻¹` of two elements of `A ⊔ K` lies in `K`, and therefore
fixes every point of `Ω`. -/
theorem app3C_commutator_fixes {F Ω : Type} [Group F] [MulAction F Ω] {K A : Subgroup F}
    (hK : K.Normal) (hA : A.Normal) (hder : ⁅A, A⁆ ≤ K)
    (hKfix : K ≤ Work.ThreePoints.ThmC.actKer F Ω) :
    ∀ x ∈ A ⊔ K, ∀ y ∈ A ⊔ K, ∀ ω : Ω, (x * y * x⁻¹ * y⁻¹) • ω = ω := by
  haveI : K.Normal := hK
  haveI : A.Normal := hA
  -- The commutator subgroup of `A ⊔ K` is `⁅A,A⁆ ⊔ ⁅A,K⁆ ⊔ ⁅K,A⁆ ⊔ ⁅K,K⁆`, all four pieces
  -- of which lie in the normal subgroup `K` (the last three by normality of `K`).
  have hmain : ⁅A ⊔ K, A ⊔ K⁆ ≤ K := by
    rw [Subgroup.commutator_sup_right A K (A ⊔ K)]
    rw [Subgroup.commutator_sup_left A A K]
    rw [Subgroup.commutator_sup_left K A K]
    exact sup_le (sup_le hder (Subgroup.commutator_le_right A K))
      (sup_le (Subgroup.commutator_le_left K A) (Subgroup.commutator_le_left K K))
  intro x hx y hy ω
  -- the element commutator lies in `⁅A ⊔ K, A ⊔ K⁆ ≤ K`, hence in the kernel of the action.
  have hmemK := hmain (Subgroup.commutator_mem_commutator hx hy)
  rw [commutatorElement_def] at hmemK
  exact Work.ThreePoints.ThmC.mem_actKer.mp (hKfix hmemK) ω

end Work.AppXIShadow
