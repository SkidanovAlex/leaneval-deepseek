import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.FrobLiftDefs
import Submission.Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
import Submission.Work.SSGRoute.frobS_nonempty
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Existence of a Frobenius lift at a finite place

For a number field `k`, an algebraic closure `Ω` and a finite place `A` of `Ω`, there is an element
`σ ∈ D_A = Work.SSGRoute.decomp k A` generating `D_A ⧸ (D_A ⊓ V)` for every open subgroup
`V ≤ G_k` containing the inertia subgroup `I_A`; that is, `Work.SSGRoute.IsFrobLift k A σ` holds.

## Proof

Index the relevant open subgroups of `G_k` by the finite normal intermediate fields `L ⊆ Ω`
(`Work.SSGRoute.FrobIndex`): put `frobV A L = I_A ⊔ G_L`, an open subgroup of `G_k` containing
`I_A`, and `frobK A L = D_A ⊓ frobV A L`, an open normal subgroup of `D_A`.  The set
`Work.SSGRoute.frobS A L ⊆ D_A` consists of the elements generating `D_A ⧸ frobK A L`.

* `Work.SSGRoute.frobS_nonempty` — each `frobS A L` is nonempty, because `D_A ⧸ frobK A L` is
  cyclic (`Work.SSGRoute.decomp_inertia_quotient_cyclic`).
* `Work.SSGRoute.frobS_isClosed` — each `frobS A L` is closed: it is a union of cosets of the open
  subgroup `frobK A L`, and so is its complement.
* `Work.SSGRoute.frobS_frobSup_subset` — the family is directed for reverse inclusion.

Since `D_A` is compact (it is closed in the compact Krull-topological group `G_k`), the sets
`frobS A L` have a common element `σ ∈ D_A`.  Finally, an arbitrary open `V ≥ I_A` contains the
fixing subgroup `G_M` of some finite normal `M ⊆ Ω`
(`Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le`), so that
`frobV A M = I_A ⊔ G_M ≤ V`; generation modulo the smaller `frobK A M` implies generation modulo
`D_A ⊓ V`, as required.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false

theorem exists_isFrobLift
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ σ : Ω ≃ₐ[k] Ω, Work.SSGRoute.IsFrobLift k A σ := by
  classical
  haveI : IsGalois k Ω := inferInstance
  -- the decomposition group is compact, being closed in the compact group `G_k`
  haveI hDcp : CompactSpace ↥(SSGRoute.decomp k A) :=
    isCompact_iff_compactSpace.mp
      (Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A).isCompact
  haveI hIn : Nonempty (FrobIndex k Ω) := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  -- the family `frobS A L` is directed for reverse inclusion
  have hdir : Directed (· ⊇ ·) (fun i : FrobIndex k Ω => frobS A i) := by
    intro i j
    exact ⟨frobSup i j, fun a ha => (frobS_frobSup_subset A i j ha).1,
      fun a ha => (frobS_frobSup_subset A i j ha).2⟩
  have hne : ∀ i : FrobIndex k Ω, (frobS A i).Nonempty := fun i => frobS_nonempty k Ω A hA i
  have hcl : ∀ i : FrobIndex k Ω, IsClosed (frobS A i) := fun i => frobS_isClosed A i
  have hcp : ∀ i : FrobIndex k Ω, IsCompact (frobS A i) := fun i => (hcl i).isCompact
  -- compactness: a common element of all the `frobS A L`
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun i : FrobIndex k Ω => frobS A i) hdir hne hcp hcl
  have hσi : ∀ i : FrobIndex k Ω, σ ∈ frobS A i := fun i => Set.mem_iInter.mp hσ i
  refine ⟨(σ : Ω ≃ₐ[k] Ω), σ.2, ?_⟩
  intro V hVopen hIV δ hδ
  -- an open `V ≥ I_A` contains the fixing subgroup of a finite normal level
  obtain ⟨M, hMfin, hMnorm, hMV⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le (U := k) (L := Ω) V hVopen
  haveI := hMfin
  haveI := hMnorm
  let i : FrobIndex k Ω := ⟨M, hMfin, hMnorm⟩
  obtain ⟨m, hm⟩ := (hσi i) ⟨δ, hδ⟩
  refine ⟨m, ?_⟩
  -- `δ⁻¹ * σ^m ∈ frobK A i ≤ frobV A i ≤ V`
  have hmemV : (((⟨δ, hδ⟩ : ↥(decomp k A))⁻¹ * σ ^ m : ↥(decomp k A)) : Ω ≃ₐ[k] Ω)
      ∈ frobV A i := by
    rw [frobK, Subgroup.mem_subgroupOf] at hm
    exact hm
  have hcoe : (((⟨δ, hδ⟩ : ↥(decomp k A))⁻¹ * σ ^ m : ↥(decomp k A)) : Ω ≃ₐ[k] Ω)
      = δ⁻¹ * (σ : Ω ≃ₐ[k] Ω) ^ m := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
  rw [hcoe] at hmemV
  exact sup_le hIV hMV hmemV

end Work.SSGRoute
