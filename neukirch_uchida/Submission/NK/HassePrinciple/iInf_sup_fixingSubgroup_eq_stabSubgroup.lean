import Mathlib
import Submission.NK.BrauerHasse.Profinite
import Submission.NK.HassePrinciple.Defs
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring

open scoped Topology Pointwise

set_option linter.style.haveILetI false

universe u

namespace NK.HassePrinciple

/-- **Closed subgroups are the intersections `⋂ᵢ (H ⊔ Nᵢ)` over a cofinal family of open normal
subgroups.**  Let `G` be a topological group, `H ≤ G` a *closed* subgroup and `{N i}` a family of
normal subgroups which is cofinal in the neighbourhood filter of `1` (every neighbourhood of `1`
contains some `N i`).  Then `⋂ᵢ (H ⊔ Nᵢ) = H`.

The inclusion `H ≤ ⋂ᵢ (H ⊔ Nᵢ)` is trivial.  For the converse let `x ∈ ⋂ᵢ (H ⊔ Nᵢ)`; since
`Nᵢ` is normal, `H ⊔ Nᵢ = Nᵢ * H`, so `x = n * h` with `n ∈ Nᵢ`, `h ∈ H`, and then
`h / x = n⁻¹ ∈ Nᵢ`.  As the `Nᵢ` are cofinal among the neighbourhoods of `1`, this shows that
every neighbourhood of `x` meets `H`, i.e. `x ∈ closure H = H`. -/
theorem iInf_sup_eq_of_isClosed {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : Type*} (H : Subgroup G) (hH : IsClosed (H : Set G)) (N : ι → Subgroup G)
    (hN : ∀ i, (N i).Normal) (hB : ∀ U ∈ 𝓝 (1 : G), ∃ i, (N i : Set G) ⊆ U) :
    (⨅ i, H ⊔ N i) = H := by
  refine le_antisymm (fun x hx => ?_) (le_iInf fun i => le_sup_left)
  have hxcl : x ∈ closure (H : Set G) := by
    rw [mem_closure_iff_nhds_one]
    intro U hU
    obtain ⟨i, hi⟩ := hB U hU
    have hxi : x ∈ H ⊔ N i := (iInf_le (fun i => H ⊔ N i) i) hx
    haveI : (N i).Normal := hN i
    have hxi' : x ∈ N i ⊔ H := by rwa [sup_comm] at hxi
    have hmem : x ∈ ((N i : Subgroup G) * (H : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (N i) H Subgroup.le_normalizer_of_normal]
      exact hxi'
    obtain ⟨n, hn, h, hh, hxh⟩ := hmem
    refine ⟨h, hh, ?_⟩
    rw [← hxh]
    have hdiv : h / (n * h) = n⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hdiv]
    exact hi (inv_mem hn)
  rwa [hH.closure_eq] at hxcl

theorem iInf_sup_fixingSubgroup_eq_stabSubgroup {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (A : ValuationSubring K') : (⨅ L : FiniteGaloisIntermediateField K K', (NK.BrauerHasse.stabSubgroup A ⊔ L.fixingSubgroup : Subgroup Gal(K'/K))) = NK.BrauerHasse.stabSubgroup A := by
  haveI : IsGalois K K' := IsSepClosure.isGalois
  refine iInf_sup_eq_of_isClosed (NK.BrauerHasse.stabSubgroup A)
    (Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A)
    (fun L : FiniteGaloisIntermediateField K K' => (L : IntermediateField K K').fixingSubgroup)
    (fun L => inferInstance) ?_
  intro U hU
  rw [krullTopology_mem_nhds_one_iff_of_normal K K'] at hU
  obtain ⟨E, hEfin, hEnorm, hEsub⟩ := hU
  refine ⟨{ toIntermediateField := E
            finiteDimensional := hEfin
            isGalois := { to_isSeparable :=
                            Algebra.IsSeparable.of_algHom K K' (IntermediateField.val E)
                          to_normal := hEnorm } }, ?_⟩
  simpa using hEsub

end NK.HassePrinciple
