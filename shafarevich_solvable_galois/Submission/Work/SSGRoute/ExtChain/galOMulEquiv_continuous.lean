import Mathlib
import Submission.Work.SSGRoute.E1aClean.BaseChangeInstances
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the level-change group isomorphism `Gal(Ω/↥L) ≃* ↥((LΩ).fixingSubgroup)`

`E1aClean.galOMulEquiv L : (Ω ≃ₐ[↥L] Ω) ≃* (E1aClean.LOmega L).fixingSubgroup` identifies the
absolute Galois group of the base-changed field `L ≤ K` with the fixing subgroup of `LOmega L`
inside `Gal(Ω/k)`.  It is the identity on underlying functions; both sides carry Krull topologies
(`Gal(Ω/↥L)` its own, `↥((LOmega L).fixingSubgroup)` the subspace topology of `Gal(Ω/k)`).

Both directions of that identification are continuous:

* `continuous_galOIncl` / `galOMulEquiv_continuous` (forward, `Gal(Ω/↥L) → ↥((LΩ).fixingSubgroup)`):
  a `1`-neighbourhood of the subspace topology contains `Gal(Ω/F) ∩ ↥((LOmega L).fixingSubgroup)`
  with `F/k` finite, and `IntermediateField.adjoin ↥L (F : Set Ω)` is finite over `↥L` (rank
  argument via `IntermediateField.adjoin_rank_le_of_isAlgebraic_right`), so
  `Gal(Ω/adjoin ↥L F)` lies in the preimage;
* `galOMulEquiv_symm_continuous` (the inverse, `↥((LΩ).fixingSubgroup) → Gal(Ω/↥L)`): a
  `1`-neighbourhood of `Gal(Ω/↥L)` is `E.fixingSubgroup` with `E/↥L` finite, and `E` contains
  `algebraMap ↥L Ω`, so the preimage in the subgroup is the trace of `Gal(Ω/E.restrictScalars k)`,
  open in `Gal(Ω/k)` because `E` is finite over `k` by the tower `k ⊆ ↥L ⊆ E`.

These two statements are the two possible instantiations of the hypothesis `Continuous Φ.symm` of
`PT.h1TransferAddHom` in the E1a level-change square: which one is needed depends on which side
of the square is transported into the other's group.
-/

namespace Work.SSGRoute.ExtChain

open IntermediateField
open scoped Topology

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K]

/-- **Continuity of the inclusion `Gal(Ω/↥L) → Gal(Ω/k)`**, i.e. of `galOIncl L`. -/
theorem continuous_galOIncl (L : IntermediateField k K) :
    Continuous (fun σ : Ω ≃ₐ[↥L] Ω => Work.SSGRoute.E1aClean.galOIncl L σ) := by
  let f : (Ω ≃ₐ[↥L] Ω) →* (Ω ≃ₐ[k] Ω) := Work.SSGRoute.E1aClean.galOIncl L
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, f.map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff k Ω] at hU
  obtain ⟨F, hFfin, hFU⟩ := hU
  haveI : FiniteDimensional k F := hFfin
  let E : IntermediateField ↥L Ω := IntermediateField.adjoin ↥L (F : Set Ω)
  have hEfin : FiniteDimensional ↥L E := by
    have hle := IntermediateField.adjoin_rank_le_of_isAlgebraic_right (F := k) (E := ↥L)
      (K := Ω) F
    have hfin : Module.rank k ↥F < Cardinal.aleph0 := Module.rank_lt_aleph0 k ↥F
    have hlt : Module.rank ↥L ↥E < Cardinal.aleph0 := lt_of_le_of_lt hle hfin
    haveI : Module.Free ↥L ↥E := Module.Free.of_divisionRing _ _
    exact Module.rank_lt_aleph0_iff.mp hlt
  have hopen : IsOpen (E.fixingSubgroup : Set (Ω ≃ₐ[↥L] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen E
  refine Filter.mem_of_superset (hopen.mem_nhds (by simp)) ?_
  intro σ hσ
  have hfix : ∀ y ∈ (E : Set Ω), σ y = y :=
    (IntermediateField.mem_fixingSubgroup_iff (K := E) σ).mp hσ
  apply hFU
  exact (IntermediateField.mem_fixingSubgroup_iff (K := F) (Work.SSGRoute.E1aClean.galOIncl L σ)).mpr
    (fun y hy => hfix y (IntermediateField.subset_adjoin ↥L (F : Set Ω) hy))

/-- **Continuity of `E1aClean.galOMulEquiv L`** (the direction `Gal(Ω/↥L) → ↥((LΩ).fixingSubgroup)`;
the underlying function is the identity on elements of `Ω`). -/
theorem galOMulEquiv_continuous (L : IntermediateField k K) :
    Continuous (Work.SSGRoute.E1aClean.galOMulEquiv L :
      (Ω ≃ₐ[↥L] Ω) → ↥((Work.SSGRoute.E1aClean.LOmega L).fixingSubgroup)) :=
  (continuous_galOIncl L).subtype_mk
    (fun σ => Work.SSGRoute.E1aClean.galOIncl_mem_fixingSubgroup L σ)

/-- **Continuity of `(E1aClean.galOMulEquiv L).symm`** (the direction
`↥((LΩ).fixingSubgroup) → Gal(Ω/↥L)`). -/
theorem galOMulEquiv_symm_continuous (L : IntermediateField k K) :
    Continuous ((Work.SSGRoute.E1aClean.galOMulEquiv L).symm :
      ↥((Work.SSGRoute.E1aClean.LOmega L).fixingSubgroup) → Ω ≃ₐ[↥L] Ω) := by
  let f : ↥((Work.SSGRoute.E1aClean.LOmega L).fixingSubgroup) →* (Ω ≃ₐ[↥L] Ω) :=
    (Work.SSGRoute.E1aClean.galOMulEquiv L).symm
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, f.map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff ↥L Ω] at hU
  obtain ⟨N, hNfin, hNU⟩ := hU
  haveI : FiniteDimensional ↥L N := hNfin
  have hMfin : FiniteDimensional k (N.restrictScalars k) :=
    FiniteDimensional.trans k ↥L ↥N
  have hopen : IsOpen ((N.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen (N.restrictScalars k)
  have hmem : (Subtype.val ⁻¹' ((N.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω))) ∈
      𝓝 (1 : ↥((Work.SSGRoute.E1aClean.LOmega L).fixingSubgroup)) :=
    (hopen.preimage continuous_subtype_val).mem_nhds (by simp)
  refine Filter.mem_of_superset hmem ?_
  intro x hx
  show (Work.SSGRoute.E1aClean.galOMulEquiv L).symm x ∈ U
  apply hNU
  have hx' : (x : Ω ≃ₐ[k] Ω) ∈ (N.restrictScalars k).fixingSubgroup := hx
  have hx'' : ∀ y ∈ (N : Set Ω), (x : Ω ≃ₐ[k] Ω) y = y :=
    (IntermediateField.mem_fixingSubgroup_iff (K := N.restrictScalars k) (x : Ω ≃ₐ[k] Ω)).mp hx'
  exact (IntermediateField.mem_fixingSubgroup_iff (K := N)
      ((Work.SSGRoute.E1aClean.galOMulEquiv L).symm x : Ω ≃ₐ[↥L] Ω)).mpr
    (fun y hy => hx'' y hy)

end Work.SSGRoute.ExtChain
