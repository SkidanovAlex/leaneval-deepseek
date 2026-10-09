import Mathlib
import Submission.Work.SSGRoute.ZConstruction.levelK_canonicalBilinear
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The transport (place-independence) of the canonical level-`K` pairing: first step

The canonical family `levelKCanonFamily` of `levelK_canonicalBilinear.lean` is a function of the
*subgroup* `H ≤ G_K`.  It is assembled from the canonical pairing at a place `A` with
`H = levelKLocalGroup k Ω K A`, and for the family to be well defined — and in particular for the
product formula `∑_{A ∈ T'} F_{H_A}[a][b] = 0`, whose summands are indexed by *places* — two places
`A`, `A'` with `levelKLocalGroup k Ω K A = levelKLocalGroup k Ω K A'` must give the same form on it.

This file proves the *first step* of that transport: the two places have the same decomposition
group over `↥K`.  The canonical isomorphism `decompEquiv_fok` (whose existence is `K.fixingSubgroup
≃* Gal(Ω/↥K)`, carrying the stabiliser of `A` in `G_K` to the stabiliser of `A` in `Gal(Ω/↥K)`)
makes `decomp (k := ↥K) A` the image of `H_A = decomp k A ⊓ K.fixingSubgroup` under that
isomorphism, so equal `H`'s have equal `decomp (k := ↥K)`'s.

What remains for the full transport is the compatibility of the two *chosen* transports — the model
identification `mupH1locLcHoms`, the local Galois transport `LT_lcHoms_levelK_localGalois` and the
Kummer dictionary `mupKummerEquiv` — which is also what would identify the two completions (the
primes `NeukirchUchida.primeOf A` and `NeukirchUchida.primeOf A'`) and the two local Artin maps
`mupRec A`, `mupRec A'`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K]

/-- **First step of the transport: two places with the same level-`K` local group have the same
decomposition group over `↥K`** (hence, up to the canonical identification, the same completion).

The map is the canonical equivalence `K.fixingSubgroup ≃* Gal(Ω/↥K)`
(`IntermediateField.fixingSubgroupEquiv`); the dictionary between its membership and the
stabiliser of `A` in `G_k` is `fixingSubgroupEquiv_mem_decomp`. -/
theorem decomp_levelK_eq_of_localGroup_eq (A A' : ValuationSubring Ω)
    (h : levelKLocalGroup k Ω K A = levelKLocalGroup k Ω K A') :
    SSGRoute.decomp (k := ↥K) A = SSGRoute.decomp (k := ↥K) A' := by
  have hA : ∀ σ : Ω ≃ₐ[k] Ω, (σ ∈ K.fixingSubgroup) →
      (σ ∈ levelKLocalGroup k Ω K A ↔ σ ∈ SSGRoute.decomp k A) := by
    intro σ hσ
    simp only [levelKLocalGroup, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hσ⟩⟩
  have hA' : ∀ σ : Ω ≃ₐ[k] Ω, (σ ∈ K.fixingSubgroup) →
      (σ ∈ levelKLocalGroup k Ω K A' ↔ σ ∈ SSGRoute.decomp k A') := by
    intro σ hσ
    simp only [levelKLocalGroup, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hσ⟩⟩
  ext y
  obtain ⟨τ, rfl⟩ := (IntermediateField.fixingSubgroupEquiv K).surjective y
  rw [show ((IntermediateField.fixingSubgroupEquiv K) τ) ∈ SSGRoute.decomp (k := ↥K) A ↔
      (τ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A from
    fixingSubgroupEquiv_mem_decomp k Ω K A (τ : Ω ≃ₐ[k] Ω) τ.2,
    show ((IntermediateField.fixingSubgroupEquiv K) τ) ∈ SSGRoute.decomp (k := ↥K) A' ↔
      (τ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A' from
    fixingSubgroupEquiv_mem_decomp k Ω K A' (τ : Ω ≃ₐ[k] Ω) τ.2,
    ← hA (τ : Ω ≃ₐ[k] Ω) τ.2, ← hA' (τ : Ω ≃ₐ[k] Ω) τ.2, h]

end

end Work.SSGRoute.ZConstruction
