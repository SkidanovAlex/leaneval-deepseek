import Mathlib
import Submission.Work.Cohomology.Compat.prodSphereDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `A1set p q ∩ B1set p q` is contractible

The two sets `A1set p q = (Sᵖ \ {Nₚ}) × Sᵍ` and `B1set p q = Sᵖ × (Sᵍ \ {N_q})` (both inside
`Yset p q = (Sᵖ × Sᵍ) \ {(Nₚ, N_q)}`) meet in

  `(Sᵖ \ {Nₚ}) × (Sᵍ \ {N_q})`,

a product of two punctured spheres.  Each punctured sphere is contractible
(`contractible_compl_sphN`), hence so is the product, and the intersection is homeomorphic to
it: the inclusion `↥(Yset p q) → ↥(PSph p q)` is an embedding whose preimage of
`(Sᵖ \ {Nₚ}) ×ˢ (Sᵍ \ {N_q})` is exactly `A1set p q ∩ B1set p q`.
-/

set_option linter.style.haveILetI false

open scoped Topology

namespace Work.Cohomology.Compat

/-- The intersection `A1set p q ∩ B1set p q` is the product `(Sᵖ \ {Nₚ}) × (Sᵍ \ {N_q})` of two
punctured spheres, hence contractible. -/
theorem contractible_A1set_inter_B1set (p q : ℕ) :
    ContractibleSpace ↥(A1set p q ∩ B1set p q) := by
  let s : Set ↥(sphSet (p+1)) := {x | x ≠ sphN p}
  let t : Set ↥(sphSet (q+1)) := {y | y ≠ sphN q}
  haveI hs : ContractibleSpace ↥s := contractible_compl_sphN p
  haveI ht : ContractibleSpace ↥t := contractible_compl_sphN q
  -- The intersection is the preimage of `s ×ˢ t` under the (injective) inclusion `Yset p q → PSph p q`.
  have hset : A1set p q ∩ B1set p q
      = (Subtype.val : ↥(Yset p q) → ↥(PSph p q)) ⁻¹' (s ×ˢ t) := by
    ext z
    simp [A1set, B1set, s, t, Set.mem_prod]
  -- Every point of `s ×ˢ t` lies in the complement of the base point.
  have hsub : (s ×ˢ t) ⊆ Set.range (Subtype.val : ↥(Yset p q) → ↥(PSph p q)) := by
    rintro w ⟨h1, _h2⟩
    exact ⟨⟨w, by
      rw [Yset]; simp only [Set.mem_ofPred_eq]
      intro h; exact h1 (congrArg Prod.fst h)⟩, rfl⟩
  have e : ↥(A1set p q ∩ B1set p q) ≃ₜ ↥s × ↥t :=
    (Homeomorph.setCongr hset).trans
      ((Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsub).trans
        (Homeomorph.Set.prod s t))
  exact e.contractibleSpace

end Work.Cohomology.Compat
