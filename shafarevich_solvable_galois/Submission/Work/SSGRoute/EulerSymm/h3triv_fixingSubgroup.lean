import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.PT.H3Transfer
import Submission.Work.SSGRoute.PTembedding.h3_triv_subsingleton_decomp
import Submission.Work.SSGRoute.PTembedding.homeomorph_fixedField_fixingSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base case of the local `H³`-vanishing at a finite level containing `ζ_p`

For a finite-dimensional intermediate field `L` of `Ω/k` containing a primitive `p`-th root of
unity `ζ`, the third cohomology of the subgroup

`U = (L.fixingSubgroup).subgroupOf (decomp k A) = Gal(Ω/L) ∩ D_A`

of the decomposition group `D_A = decomp k A` vanishes with trivial coefficients `𝔽_p`:

`Subsingleton (H³(U, 𝔽_p))`.

This is the `p`-Sylow datum's `hbase` input.  The proof is a transport of the corresponding
statement at the *base field* `L`, namely
`PTembedding.h3_triv_subsingleton_decomp p ↥L Ω ζ hζ hζL A hA`
(`H³(decomp ↥L A, 𝔽_p) = 0`, which uses `ζ ∈ L` to identify `μ_p ≅ 𝔽_p`), along the canonical
isomorphism `decomp ↥L A ≃* U` induced by `IntermediateField.fixingSubgroupEquiv L`
(a homeomorphism by `PTembedding.isHomeomorph_fixingSubgroupEquiv`).
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.EulerSymm

open Work.SSGRoute
open scoped Pointwise

/-- `IsFinPlace` is inherited by larger base fields: if a place of `Ω` is finite over `k`, it is
finite over every intermediate field of `Ω/k`. -/
theorem isFinPlace_of_le {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (F : IntermediateField k Ω) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    SSGRoute.IsFinPlace ↥F A := by
  intro htop
  apply hA
  rw [IsScalarTower.algebraMap_eq k ↥F Ω,
    ← ValuationSubring.comap_comap A (algebraMap ↥F Ω) (algebraMap k ↥F), htop]
  ext x
  simp [ValuationSubring.mem_comap]

/-- **The base case of the local `H³`-vanishing.**  If `L` is a finite-dimensional intermediate
field of `Ω/k` containing a primitive `p`-th root of unity `ζ`, then the third cohomology of
`Gal(Ω/L) ∩ D_A` with trivial coefficients `𝔽_p` vanishes. -/
theorem h3triv_subsingleton_fixingSubgroup
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (L : IntermediateField k Ω) [FiniteDimensional k L]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p)
      ↥((L.fixingSubgroup).subgroupOf (SSGRoute.decomp k A))) := by
  classical
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  haveI hAlgL : Algebra.IsAlgebraic ↥L Ω :=
    Algebra.IsAlgebraic.tower_top (K := k) (L := ↥L) (A := Ω)
  haveI hAlgClL : IsAlgClosure ↥L Ω := ⟨IsAlgClosure.isAlgClosed k, hAlgL⟩
  haveI hGalL : IsGalois ↥L Ω := IsAlgClosure.isGalois ↥L Ω
  haveI hIntL : Algebra.IsIntegral ↥L Ω :=
    Algebra.isAlgebraic_iff_isIntegral.mp (Algebra.IsSeparable.isAlgebraic ↥L Ω)
  haveI hT2 : T2Space (Ω ≃ₐ[↥L] Ω) := krullTopology_t2
  haveI hCompD : CompactSpace ↥(SSGRoute.decomp k A) :=
    isCompact_iff_compactSpace.mp
      (Work.SSGRoute.HS.isClosed_decomp (k := k) (Ω := Ω) A).isCompact
  -- ## the base case at the base field `L`
  have hζL' : ζ ∈ (⊥ : IntermediateField ↥L Ω) :=
    IntermediateField.mem_bot.mpr ⟨⟨ζ, hζL⟩, rfl⟩
  have hbase : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p)
      ↥(SSGRoute.decomp ↥L A)) :=
    Work.SSGRoute.PTembedding.h3_triv_subsingleton_decomp p ↥L Ω ζ hζ hζL' A
      (isFinPlace_of_le L A hA)
  -- ## the canonical isomorphism `Gal(Ω/L) ≃* Gal(Ω/↥L)`
  let e : ↥(L.fixingSubgroup) ≃* (Ω ≃ₐ[↥L] Ω) := IntermediateField.fixingSubgroupEquiv L
  have he : IsHomeomorph (e : ↥(L.fixingSubgroup) → (Ω ≃ₐ[↥L] Ω)) :=
    Work.SSGRoute.PTembedding.isHomeomorph_fixingSubgroupEquiv L
  have hcoe : ∀ x : ↥(L.fixingSubgroup),
      ((e x : Ω ≃ₐ[↥L] Ω) : Ω → Ω) = ((x : Ω ≃ₐ[k] Ω) : Ω → Ω) := fun x => rfl
  have hsmul : ∀ (x : ↥(L.fixingSubgroup)) (s : Ω),
      (e x : Ω ≃ₐ[↥L] Ω) • s = (x : Ω ≃ₐ[k] Ω) • s := fun x s => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def]
    exact congrFun (hcoe x) s
  have key : ∀ x : ↥(L.fixingSubgroup),
      (e x : Ω ≃ₐ[↥L] Ω) • A = (x : Ω ≃ₐ[k] Ω) • A := by
    intro x
    apply SetLike.ext
    intro y
    rw [ValuationSubring.mem_smul_pointwise_iff_exists,
      ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, hxs⟩
      exact ⟨s, hs, by rw [← hsmul x s]; exact hxs⟩
    · rintro ⟨s, hs, hxs⟩
      exact ⟨s, hs, by rw [hsmul x s]; exact hxs⟩
  -- ## the comparison isomorphism
  let U : Subgroup ↥(SSGRoute.decomp k A) :=
    (L.fixingSubgroup).subgroupOf (SSGRoute.decomp k A)
  let toF : ↥U → ↥(L.fixingSubgroup) := fun u => ⟨(u : Ω ≃ₐ[k] Ω), u.2⟩
  have htoF : Continuous toF := by
    change Continuous fun u : ↥U =>
      (⟨(u : Ω ≃ₐ[k] Ω), u.2⟩ : ↥(L.fixingSubgroup))
    exact Continuous.subtype_mk
      (f := fun u : ↥U => ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω))
      (continuous_subtype_val.comp continuous_subtype_val) (fun u => u.2)
  have hmem_e : ∀ u : ↥U, e (toF u) ∈ SSGRoute.decomp ↥L A := by
    intro u
    have hkey := key (toF u)
    rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff, hkey]
    exact MulAction.mem_stabilizer_iff.mp (u : ↥(SSGRoute.decomp k A)).2
  have hmem_symm : ∀ v : ↥(SSGRoute.decomp ↥L A),
      (e.symm v : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A := by
    intro v
    rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff]
    have hkey := key (e.symm v)
    simp only [MulEquiv.apply_symm_apply] at hkey
    exact hkey.symm.trans (MulAction.mem_stabilizer_iff.mp v.2)
  let ψf : ↥U → ↥(SSGRoute.decomp ↥L A) := fun u => ⟨e (toF u), hmem_e u⟩
  have hψfmul : ∀ u w : ↥U, ψf (u * w) = ψf u * ψf w := by
    intro u w
    refine Subtype.ext ?_
    have h : toF (u * w) = toF u * toF w := Subtype.ext rfl
    have h2 : e (toF (u * w)) = e (toF u) * e (toF w) := by rw [h, map_mul]
    exact h2
  let ψ : ↥U →* ↥(SSGRoute.decomp ↥L A) :=
    { toFun := ψf
      map_one' := Subtype.ext (by
        change e (toF (1 : ↥U)) = (1 : Ω ≃ₐ[↥L] Ω)
        rw [show toF (1 : ↥U) = 1 from Subtype.ext rfl, map_one])
      map_mul' := hψfmul }
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro u w huw
      have h1 : toF u = toF w := by
        have hc : (ψ u : Ω ≃ₐ[↥L] Ω) = (ψ w : Ω ≃ₐ[↥L] Ω) :=
          congrArg (fun x : ↥(SSGRoute.decomp ↥L A) => (x : Ω ≃ₐ[↥L] Ω)) huw
        exact e.injective hc
      have h2 : ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω)
          = ((w : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) := by
        have hc : ((toF u : ↥(L.fixingSubgroup)) : Ω ≃ₐ[k] Ω)
            = ((toF w : ↥(L.fixingSubgroup)) : Ω ≃ₐ[k] Ω) :=
          congrArg (fun x : ↥(L.fixingSubgroup) => (x : Ω ≃ₐ[k] Ω)) h1
        exact hc
      exact Subtype.ext (Subtype.ext h2)
    · intro v
      refine ⟨⟨⟨(e.symm v : Ω ≃ₐ[k] Ω), hmem_symm v⟩, (e.symm v).2⟩, ?_⟩
      refine Subtype.ext ?_
      show e (toF (⟨⟨(e.symm v : Ω ≃ₐ[k] Ω), hmem_symm v⟩, (e.symm v).2⟩ : ↥U))
        = (v : Ω ≃ₐ[↥L] Ω)
      rw [show toF (⟨⟨(e.symm v : Ω ≃ₐ[k] Ω), hmem_symm v⟩, (e.symm v).2⟩ : ↥U) = e.symm v
        from Subtype.ext rfl, MulEquiv.apply_symm_apply]
  let Φ : ↥U ≃* ↥(SSGRoute.decomp ↥L A) := MulEquiv.ofBijective ψ hψbij
  have hΦcont : Continuous (Φ : ↥U → ↥(SSGRoute.decomp ↥L A)) := by
    change Continuous ψf
    change Continuous fun u : ↥U =>
      (⟨e (toF u), hmem_e u⟩ : ↥(SSGRoute.decomp ↥L A))
    exact Continuous.subtype_mk (he.continuous.comp htoF) (fun u => hmem_e u)
  haveI hUcomp : CompactSpace ↥U := by
    have hcl : IsClosed ((U : Set ↥(SSGRoute.decomp k A))) := by
      change IsClosed (Subtype.val ⁻¹' (L.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :
        Set ↥(SSGRoute.decomp k A))
      exact (IntermediateField.fixingSubgroup_isClosed L).preimage continuous_subtype_val
    exact isCompact_iff_compactSpace.mp hcl.isCompact
  have hΦ : IsHomeomorph (Φ : ↥U → ↥(SSGRoute.decomp ↥L A)) :=
    (isHomeomorph_iff_continuous_bijective).mpr ⟨hΦcont, Φ.bijective⟩
  -- ## transport the vanishing
  exact ⟨fun a b => (Work.SSGRoute.PT.h3Transfer Φ hΦ (AddEquiv.refl (Work.SSGRoute.Triv p))
    (fun _ _ => rfl)).injective (hbase.elim _ _)⟩

end Work.SSGRoute.EulerSymm
