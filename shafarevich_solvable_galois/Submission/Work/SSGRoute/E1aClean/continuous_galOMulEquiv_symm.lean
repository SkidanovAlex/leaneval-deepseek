import Mathlib
import Submission.Work.SSGRoute.E1aClean.BaseChangeInstances
import Submission.Work.SSGRoute.E1aClean.BaseChangeE1c
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the inverse of the `Ω`-side base-change dictionary

`galOMulEquiv L : Gal(Ω/↥L) ≃* (LOmega L).fixingSubgroup` (`E1aClean/BaseChangeInstances.lean`)
identifies the absolute Galois group of the base-changed extension with the fixing subgroup of
`LOmega L` inside `Gal(Ω/k)`.  Both sides carry a Krull topology: the fixing subgroup as a
subspace of `Gal(Ω/k)` (`krullTopology k Ω`), the group `Gal(Ω/↥L)` as `krullTopology ↥L Ω`.
The underlying map of the group isomorphism is the identity on the underlying functions, and the
two topologies agree; here we record the direction needed downstream, namely that the inverse
`(galOMulEquiv L).symm` is continuous.

The proof is a continuity-at-one argument.  A basic Krull neighbourhood of `1` in `Gal(Ω/↥L)`
is the fixing subgroup of a finite intermediate field `E/↥L`; this is continuous because `E`,
viewed over `k` (which is finite over `k` since `E` is finite over `↥L` and `L ⊆ K` is finite
over `k`), is again a finite extension of `k`, and fixing `E` over `k` implies fixing it over
`↥L`. -/

open scoped Topology

namespace Work.SSGRoute.E1aClean

open IntermediateField

theorem continuous_galOMulEquiv_symm {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    (L : IntermediateField k K) :
    Continuous ((galOMulEquiv L).symm : (LOmega L).fixingSubgroup → Ω ≃ₐ[↥L] Ω) := by
  -- It suffices to check continuity of the group homomorphism at `1`.
  refine continuous_of_continuousAt_one (f := (galOMulEquiv L).symm) ?_
  rw [ContinuousAt, map_one]
  rw [Filter.tendsto_def]
  intro s hs
  -- A basic neighbourhood of `1` in `Gal(Ω/↥L)` is the fixing subgroup of a finite `E/↥L`.
  rw [krullTopology_mem_nhds_one_iff ↥L Ω s] at hs
  obtain ⟨E, hEfin, hEsub⟩ := hs
  refine Filter.mem_of_superset ?_ (fun τ hτ => hEsub hτ)
  -- `E` re-read over `k` is finite over `k`, hence a basic Krull neighbourhood of `1` in `Gal(Ω/k)`.
  have hU : ((E.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) ∈ 𝓝 (1 : Ω ≃ₐ[k] Ω) := by
    rw [krullTopology_mem_nhds_one_iff k Ω]
    haveI := hEfin
    haveI : FiniteDimensional k ↥E := FiniteDimensional.trans k ↥L ↥E
    exact ⟨E.restrictScalars k, this, subset_rfl⟩
  -- Pull it back along the continuous coercion of the fixing subgroup.
  have hT : Subtype.val ⁻¹' ((E.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) ∈
      𝓝 (1 : (LOmega L).fixingSubgroup) := by
    have hc : ContinuousAt (Subtype.val : (LOmega L).fixingSubgroup → Ω ≃ₐ[k] Ω) 1 :=
      continuous_subtype_val.continuousAt
    exact hc.preimage_mem_nhds hU
  refine Filter.mem_of_superset hT ?_
  intro τ hτ
  simp only [Set.mem_preimage] at hτ
  -- Elements of `(LOmega L).fixingSubgroup` fixing `E` over `k` fix `E` over `↥L`.
  refine (IntermediateField.mem_fixingSubgroup_iff E ((galOMulEquiv L).symm τ)).mpr ?_
  intro x hx
  rw [show ((galOMulEquiv L).symm τ : Ω ≃ₐ[↥L] Ω) x = (τ : Ω ≃ₐ[k] Ω) x from rfl]
  exact (IntermediateField.mem_fixingSubgroup_iff (E.restrictScalars k) (τ : Ω ≃ₐ[k] Ω)).mp hτ x hx

end Work.SSGRoute.E1aClean
