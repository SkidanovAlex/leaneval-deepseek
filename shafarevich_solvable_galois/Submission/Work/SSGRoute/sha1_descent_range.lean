import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.sha1_descent_H1
import Submission.Work.SSGRoute.sha1_descent_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The range of the Hasse descent `Ш¹(k,M) ↪ H¹(Gal(K/k), M)`

`sha1_descent_decomp.lean` shows that the local conditions of `Z1loc` are *equivalent* to the
finite-level conditions: a `Gal(K/k)`-cocycle `ψ` is the descent of an element of `Z1loc` iff it is a
coboundary on the image `(decomp k A).map (res k K)` of every decomposition group and on the image
of `zpowers σ` for every involution `σ`.  Here we package this as a description of the *image* of the
Hasse descent

  `sha1DescentHom : Ш¹(k,M) →+ H¹(Gal(K/k), M)`  (injective, `sha1_descent_H1.lean`),

which is node `E1b` of `DESIGN_EXT.md` phrased in the cocycle language.  The condition is
well defined on the class (adding a coboundary `d⁰ m` shifts both sides by the coboundary of the
same `m`), so the `∃ ψ` formulation does not overcount.
-/

set_option linter.ambiguousOpen false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open SSGRoute

/-- **The range of the Hasse descent.**  A class `y ∈ H¹(Gal(K/k), M)` lies in the image of
`Ш¹(k,M) →+ H¹(Gal(K/k), M)` if and only if it is represented by a cocycle which is a coboundary on
the image of every decomposition group (at the finite places of `k`) and on the image of every
involution. -/
theorem sha1_descent_range (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    Set.range (sha1DescentHom p k Ω K M) =
      {y : Work.GroupCohomology.H1 (K ≃ₐ[k] K) M |
        ∃ ψ : Work.GroupCohomology.Z1 (K ≃ₐ[k] K) M,
          Work.GroupCohomology.H1π (K ≃ₐ[k] K) M ψ = y ∧
          (∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
            SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
              ((SSGRoute.decomp k A).map (SSGRoute.res k K)) ψ.1) ∧
          (∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
            SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
              ((Subgroup.zpowers σ).map (SSGRoute.res k K)) ψ.1)} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
      (p := (B1top p k Ω K M).comap (Z1loc p k Ω K M).subtype) x
    refine ⟨descentZ1 p k Ω K M z, ?_, isCoboundaryOn_map_descentZ1 p k Ω K z⟩
    rw [sha1DescentHom_mk, descentHom_apply]
  · rintro ⟨ψ, hψy, hloc, hinf⟩
    have hψ : SSGRoute.IsCocycleOn (MonoidHom.id (K ≃ₐ[k] K)) ⊤ ψ.1 :=
      (isCocycleOn_iff_mem_Z1 (MonoidHom.id (K ≃ₐ[k] K)) ψ.1).mpr ψ.2
    obtain ⟨z, hz⟩ := (exists_descent_iff p k Ω K ψ.1 hψ).mpr ⟨hloc, hinf⟩
    have hz' : z.1 = ψ.1 ∘ SSGRoute.res k K := by
      rw [descentZ1_comp_res p k Ω K M z, hz]
    have hdes : descentZ1 p k Ω K M z = ψ := descentZ1_eq_of p k Ω K M z ψ hz'
    exact ⟨Submodule.Quotient.mk z, by
      rw [sha1DescentHom_mk, descentHom_apply, hdes, hψy]⟩

/-- **Naturality of the range description.**  The subgroup of `H¹(Gal(K/k), ·)` described above is
natural in the coefficient module: a `Gal(K/k)`-equivariant `𝔽_p`-linear map `f : M → N` carries the
range of the Hasse descent at `M` into the range at `N`.  (For the converse one would need `f`
injective; the direction proved here is the one used by the naturality clause of node `E1b`.)
-/
theorem sha1_descent_range_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N] [Finite N]
    (f : M →ₗ[ZMod p] N) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    {y : Work.GroupCohomology.H1 (K ≃ₐ[k] K) M} (hy : y ∈ Set.range (sha1DescentHom p k Ω K M)) :
    Work.GroupCohomology.mapH1 (K ≃ₐ[k] K) f.toAddMonoidHom hf y
      ∈ Set.range (sha1DescentHom p k Ω K N) := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨Sha1Map p k Ω K M N f hf x, sha1DescentHom_natural p k Ω K M N f hf x⟩

end Work.SSGRoute
