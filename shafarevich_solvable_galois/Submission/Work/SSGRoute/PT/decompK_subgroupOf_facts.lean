import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.PT.KrullCorrespondence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` subgroup of a decomposition group is open of finite index

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K/k` a *finite* Galois
subextension and `A` a finite place of `Ω` over `k`.  Write

* `G_k = Ω ≃ₐ[k] Ω` (Krull topology), `D_A = decomp k A` the decomposition group of `A`;
* `G_K = K.fixingSubgroup` the open (since `K/k` is finite) normal subgroup of `G_k`
  fixing `K`.

The subgroup `G_K ⊓ D_A` is the level-`K` part of the decomposition group; these facts are
used pervasively when `D_A ⊓ G_K` is treated as a local Galois group.

Because `G_K` is **open** in `G_k`, its trace on any subgroup — in particular on `D_A` — is
open for the subspace topology, and because `G_K` has **finite index** in `G_k`, its trace on
`D_A` has finite index in `D_A` (the natural map `D_A/(G_K ⊓ D_A) → G_k/G_K` is injective).
Consequently the quotient `D_A ⧸ (G_K ⊓ D_A)` is finite.

Note that `G_K ⊓ D_A` need not be open in `G_k` — the decomposition group `D_A` is only closed,
not open — but the statement is about openness inside `D_A`, where `Subgroup.subgroupOf`
computes the trace via `Subtype.val`.
-/

namespace Work.SSGRoute.PT

theorem decompK_subgroupOf_facts
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    IsOpen (((K.fixingSubgroup ⊓ SSGRoute.decomp k A).subgroupOf
        (SSGRoute.decomp k A)) : Set ↥(SSGRoute.decomp k A))
      ∧ (((K.fixingSubgroup ⊓ SSGRoute.decomp k A).subgroupOf
        (SSGRoute.decomp k A))).FiniteIndex
      ∧ Nonempty (Fintype (↥(SSGRoute.decomp k A) ⧸
        ((K.fixingSubgroup ⊓ SSGRoute.decomp k A).subgroupOf (SSGRoute.decomp k A)))) := by
  -- `G_K = K.fixingSubgroup` is open in `G_k` (finiteness of `K/k`).
  have hKopen : IsOpen ((K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen K
  -- ... and has finite index in `G_k`: `[G_k : G_K] = [K : k]`.
  have hKfin : K.fixingSubgroup.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, ← IntermediateField.finrank_eq_fixingSubgroup_index Ω K]
    exact (Module.finrank_pos (R := k) (M := ↥K)).ne'
  -- Inside `D_A`, the trace of `G_K` and of `G_K ⊓ D_A` agree.
  have hsub : ((K.fixingSubgroup ⊓ SSGRoute.decomp k A).subgroupOf (SSGRoute.decomp k A))
      = (K.fixingSubgroup.subgroupOf (SSGRoute.decomp k A)) :=
    Subgroup.ext (fun x => by simp [Subgroup.mem_subgroupOf])
  have hfinSub : (K.fixingSubgroup.subgroupOf (SSGRoute.decomp k A)).FiniteIndex :=
    @Subgroup.instFiniteIndex_subgroupOf (Ω ≃ₐ[k] Ω) _ K.fixingSubgroup (SSGRoute.decomp k A) hKfin
  refine ⟨?_, ?_, ?_⟩
  · -- Openness: the trace is the preimage of the open `G_K` under `D_A ↪ G_k`.
    have hpre : IsOpen ((fun x : ↥(SSGRoute.decomp k A) => (x : Ω ≃ₐ[k] Ω)) ⁻¹'
        (K.fixingSubgroup : Set (Ω ≃ₐ[k] Ω))) :=
      hKopen.preimage continuous_subtype_val
    have heq : (((K.fixingSubgroup ⊓ SSGRoute.decomp k A).subgroupOf
          (SSGRoute.decomp k A)) : Set ↥(SSGRoute.decomp k A)) =
        ((fun x : ↥(SSGRoute.decomp k A) => (x : Ω ≃ₐ[k] Ω)) ⁻¹'
          (K.fixingSubgroup : Set (Ω ≃ₐ[k] Ω))) := by
      ext x; simp [Subgroup.mem_subgroupOf]
    rw [heq]; exact hpre
  · rw [hsub]; exact hfinSub
  · -- Finite index gives a `Fintype` on the quotient.
    rw [hsub]
    exact ⟨@Subgroup.fintypeQuotientOfFiniteIndex (↥(SSGRoute.decomp k A))
      (inferInstance : Group ↥(SSGRoute.decomp k A))
      (K.fixingSubgroup.subgroupOf (SSGRoute.decomp k A)) hfinSub⟩

end Work.SSGRoute.PT
