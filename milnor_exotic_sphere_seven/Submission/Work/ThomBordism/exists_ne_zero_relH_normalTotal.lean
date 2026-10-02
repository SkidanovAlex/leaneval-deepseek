import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.ThomBordism.nonempty_chartedSpace_normalTotal
import Submission.Work.ThomBordism.thomPairTopHomologyIsoV2
import Submission.Work.ThomBordism.nonempty_thomClass_normalBundle
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Tubular.totalSpace_mapFibre_homeo
import Submission.Work.Tubular.nonempty_thomClass_of_bundleIso
import Submission.Work.Tubular.LocalDegreeAll
import Submission.Work.Tubular.ThomComparison

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.ThomBordism

open CategoryTheory

/-- **The Thom group of a rank-`k` real bundle over a closed oriented smooth `8`-manifold is
non-trivial.**  For a real bundle `Z` of rank `k ≥ 1` over a closed connected oriented smooth
`8`-manifold carrying an integral Thom class, the relative homology `H_{k+8}(Z, Z∖0; ℤ)` of the Thom
pair is infinite cyclic (`Work.ThomBordism.thomPairTopHomologyIsoV2`), hence has a non-zero
element.

This is the abstract form of the non-vanishing statement for the Thom group, in the coordinate fibre
`Fin k → ℝ` used by `Work.Tubular`. -/
theorem exists_ne_zero_relHomology_thom {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type}
    (hk : 1 ≤ k) (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι)
    [PathConnectedSpace V.pt] (hZ : Nonempty (Work.Thom.ThomClass Z k)) :
    ∃ z : (Work.Cohomology.relChains (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z)).homology (k + 8), z ≠ 0 := by
  classical
  obtain ⟨e⟩ := Work.ThomBordism.thomPairTopHomologyIsoV2 (hk := hk) Z hZ
  let f : (Work.Cohomology.relChains (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z)).homology (k + 8) ≃ₗ[ℤ] ℤ := e.toLinearEquiv
  refine ⟨f.symm 1, fun h => ?_⟩
  have h1 : (1 : ℤ) = 0 := by
    calc (1 : ℤ) = f (f.symm 1) := (f.apply_symm_apply 1).symm
      _ = f 0 := by rw [h]
      _ = 0 := map_zero f
  exact one_ne_zero h1

/-- **The top relative homology of the Thom pair of the normal bundle is non-zero.**  For the normal
bundle `ν = NormalTotal E` of an embedded closed oriented smooth `8`-manifold there is a non-zero
class in `H_{8+k}(ν, ν∖0)`: the group is the Thom group of the (rank `k ≥ 1`) normal bundle, which is
isomorphic to `H_8(V) ≅ ℤ`; concretely the class of the closed disc bundle relative to its boundary. -/
theorem exists_ne_zero_relH_normalTotal {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    ∃ z : (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)).homology (8 + k), z ≠ 0 := by
  classical
  haveI hpc : PathConnectedSpace V.pt := Work.Tubular.pathConnectedSpace_of_man8 V
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion (V := V) (k := k)
    E.e (E.smooth.of_le (by simp)) E.injective_mfderiv
  -- the Euclidean normal bundle of the embedding, and its identification with the concrete model
  let nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k)
    (Work.ThomBordism.PontryaginThom.CoverIdx V k) :=
    Work.Tubular.normalBundle E ND
  let φ : nu.TotalSpace ≃ₜ Work.Tubular.NormalTotal E := Work.Tubular.eucNormalHomeomorph E ND
  have hlen : ∀ p : nu.TotalSpace,
      Work.Thom.fibreNorm nu p ≠ 0 ↔ Work.Tubular.normalNorm E (φ p) ≠ 0 := by
    intro p
    rw [Work.Tubular.fibreNorm_eq_normalNorm, Work.Tubular.eucNormalHomeomorph_apply]
  have hZ : Nonempty (Work.Thom.ThomClass nu k) :=
    Work.ThomBordism.nonempty_thomClass_normalBundle hk E ND
  -- change of the model fibre to the coordinate fibre `Fin k → ℝ`
  obtain ⟨eL⟩ : Nonempty (Work.Tubular.Euc k ≃L[ℝ] (Fin k → ℝ)) :=
    ⟨ContinuousLinearEquiv.ofFinrankEq (by simp)⟩
  let Z₁ : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ)
    (Work.ThomBordism.PontryaginThom.CoverIdx V k) :=
    Work.TangentClasses.RealBundle.mapFibre eL nu
  obtain ⟨hψ, -, hψnorm, -⟩ := Work.Tubular.totalSpace_mapFibre_homeo eL nu
  let ψ₁ : Z₁.TotalSpace ≃ₜ Work.Tubular.NormalTotal E := hψ.symm.trans φ
  have hZ1 : Nonempty (Work.Thom.ThomClass Z₁ k) :=
    Work.Tubular.nonempty_thomClass_of_bundleIso (Work.Tubular.bundleIsoMapFibre eL nu)
      (Classical.choice hZ)
  have hlen1 : ∀ p : Z₁.TotalSpace,
      Work.Thom.fibreNorm Z₁ p ≠ 0 ↔ Work.Tubular.normalNorm E (ψ₁ p) ≠ 0 := by
    intro p
    show Work.Thom.fibreNorm Z₁ p ≠ 0 ↔ Work.Tubular.normalNorm E (φ (hψ.symm p)) ≠ 0
    have h3 : (Work.Thom.fibreNorm Z₁ p ≠ 0) ↔ (Work.Thom.fibreNorm nu (hψ.symm p) ≠ 0) := by
      have h4 := hψnorm (hψ.symm p)
      rw [hψ.apply_symm_apply] at h4
      exact not_congr h4
    exact h3.trans (hlen (hψ.symm p))
  -- the non-zero class of the Thom group of the abstract bundle
  obtain ⟨y, hy⟩ := exists_ne_zero_relHomology_thom (V := V) (k := k) (hk := hk) Z₁ hZ1
  -- the two removed sets correspond
  have hAB : ∀ p : Z₁.TotalSpace, p ∈ Work.Thom.zeroComplement Z₁ ↔
      ψ₁ p ∈ Work.Tubular.normalNonzero E := by
    intro p
    have hone : (p ∈ Work.Thom.zeroComplement Z₁) ↔ Work.Thom.fibreNorm Z₁ p ≠ 0 := by
      rw [Work.Thom.mem_zeroComplement, Work.Thom.fibreNorm, norm_ne_zero_iff]
    rw [Work.Tubular.mem_normalNonzero]
    exact hone.trans (hlen1 p)
  have hw : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.subtypeIncl (TopCat.of Z₁.TotalSpace) (Work.Thom.zeroComplement Z₁))
      (TopCat.ofHom ψ₁)
      = CategoryTheory.CategoryStruct.comp (TopCat.ofHom (ψ₁.subtype hAB))
        (Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)) := by
    apply TopCat.ext
    intro a
    rfl
  -- the induced map on relative homology is an isomorphism
  haveI hiso := Work.Tubular.isIso_relChainsMapOf_homeoSub
    (X := TopCat.of Z₁.TotalSpace) (Y := TopCat.of (Work.Tubular.NormalTotal E))
    (A := Work.Thom.zeroComplement Z₁) (B := Work.Tubular.normalNonzero E) ψ₁ hAB hw (k + 8)
  let g := HomologicalComplex.homologyMap
    (Work.Cohomology.relChainsMapOf (TopCat.of Z₁.TotalSpace)
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Thom.zeroComplement Z₁)
      (Work.Tubular.normalNonzero E) (TopCat.ofHom ψ₁) (TopCat.ofHom (ψ₁.subtype hAB)) hw)
    (k + 8)
  have hz : g.hom y ≠ 0 := by
    intro h
    exact hy ((ModuleCat.mono_iff_injective g).mp inferInstance (by simpa using h))
  -- the two degrees `8 + k` and `k + 8` are equal; transport the class along `eqToHom`
  have hF : (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)).homology (k + 8)
      = (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)).homology (8 + k) :=
    congrArg (fun n => (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)).homology n) (Nat.add_comm k 8)
  refine ⟨(CategoryTheory.eqToHom hF).hom (g.hom y), ?_⟩
  intro hcast
  exact hz ((ModuleCat.mono_iff_injective (CategoryTheory.eqToHom hF)).mp inferInstance
    (by simpa using hcast))

end Work.ThomBordism
