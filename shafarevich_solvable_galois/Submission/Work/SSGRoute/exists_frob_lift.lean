import Mathlib
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.FrobLiftDefs
import Submission.Work.SSGRoute.decomp_mod_inertia_cyclic
import Submission.Work.SSGRoute.FrobLiftSetup
import Submission.Work.SSGRoute.FrobLiftSetup2
import Submission.Work.SSGRoute.frobS_nonempty
import Submission.Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open _root_.SSGRoute

namespace Work.SSGRoute

/-- **Existence of a Frobenius lift** (`IsFrobLift k A σ`).

ROUTE. By `Work.SSGRoute.decomp_mod_inertia_cyclic`, for every open subgroup `V ≤ Ω ≃ₐ[k] Ω`
containing `I_A = inertiaSub k Ω A` the quotient `D_A ⧸ (D_A ⊓ V)` is cyclic, with a generator
`g_V` depending on `V`.  The element `σ` demanded here must work for all `V` at once, which is a
compactness argument over the directed family of these quotients.

Recommended formalisation.  Index the family by the open *normal* subgroups `N ⊴ G_k` and put
`V_N := I_A · N` (the product taken in `G_k`; it is a subgroup since `N` is normal, it is open, it
contains `I_A`, and `⋂_N (I_A · N) = I_A` because for `g ∉ I_A` there is an open normal `N` with
`gN ∩ I_A = ∅`, so that `g ∉ I_A·N`).  For such `V_N` the subgroup `D_A ⊓ V_N` is normal in `D_A`
(both `I_A` and `N` are normalised by `D_A`), and the set
`S_N := {x : Ω ≃ₐ[k] Ω | x ∈ D_A ∧ ∀ δ ∈ D_A, ∃ m : ℤ, δ⁻¹ * x^m ∈ V_N}`
is `π⁻¹` of the set of generators of the finite cyclic group `D_A ⧸ (D_A ⊓ V_N)`, hence a union of
cosets of the open subgroup `D_A ⊓ V_N`, hence clopen.  `S_N` is nonempty by
`decomp_mod_inertia_cyclic` applied to `W := V_N ⊓ decomp k A` (its hypothesis is `I_A ≤ V_N`),
and the sets `S_N` have the finite intersection property because `S_{N ⊓ N'} ⊆ S_N ∩ S_{N'}` for
`D_A ⊓ V_{N ⊓ N'} ≤ D_A ⊓ V_N`.  Since `D_A = decomp k A` is compact (it is closed in
`Ω ≃ₐ[k] Ω`, which is compact for the Krull topology), `IsCompact.inter_iInter_nonempty` gives
`σ` in the intersection.

Finally transport to an arbitrary open `V ≥ I_A`: choosing an open normal `N ≤ V` gives
`I_A · N ≤ V`, and generation modulo the smaller subgroup `D_A ⊓ (I_A · N)` implies generation
modulo `D_A ⊓ V`. -/
theorem exists_frob_lift (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ σ : Ω ≃ₐ[k] Ω, IsFrobLift k A σ := by
  classical
  haveI : IsGalois k Ω := inferInstance
  -- `D_A` is compact, being closed in the compact group `G_k`
  haveI hDcp : CompactSpace ↥(decomp k A) :=
    isCompact_iff_compactSpace.mp
      (Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A).isCompact
  haveI hIn : Nonempty (FrobIndex k Ω) := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  -- the family `frobS A L` is directed (downwards), nonempty, closed
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
  -- an open subgroup `V ≥ I_A` contains the fixing subgroup of a finite normal level
  obtain ⟨M, hMfin, hMnorm, hMV⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le (U := k) (L := Ω) V hVopen
  haveI := hMfin
  haveI := hMnorm
  let i : FrobIndex k Ω := ⟨M, hMfin, hMnorm⟩
  obtain ⟨m, hm⟩ := (hσi i) ⟨δ, hδ⟩
  refine ⟨m, ?_⟩
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
