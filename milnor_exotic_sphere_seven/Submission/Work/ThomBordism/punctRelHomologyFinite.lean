import Mathlib
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing
import Submission.Work.ThomBordism.finiteHomologyThomPair
import Submission.Work.ThomBordism.compactHomologyFinite
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.localCohomology
import Submission.Work.ThomBordism.chartedSpaceTotalSpace
import Submission.Work.Tubular.ThomComparison
import Submission.Work.ThomBordism.Grassmann.Torsion.mvFiniteness
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Tubular.normalTotalIso
import Submission.Work.Tubular.totalSpace_mapFibre_homeo
import Submission.Work.ThomBordism.relChains_zeroComplement_finite

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## Finiteness of the relative homology of `(ν, ν∖0)`

The model bundle `Z₁ = nu.mapFibre eL` over `V.pt` with fibre `Fin k → ℝ` has finitely generated
relative homology in the pair `(Z₁.TotalSpace, zeroComplement Z₁)` by
`Work.ThomBordism.finiteHomologyThomPair`; the homeomorphism of pairs onto
`(NormalTotal E, normalNonzero E)` transports the finiteness. -/
private theorem finite_normalNonzero (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (j : ℕ) :
    Module.Finite ℤ ((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)).homology j) := by
  classical
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv
  let nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k)
      (Work.ThomBordism.PontryaginThom.CoverIdx V k) := Work.Tubular.normalBundle E ND
  let φ : nu.TotalSpace ≃ₜ Work.Tubular.NormalTotal E := Work.Tubular.eucNormalHomeomorph E ND
  obtain ⟨eL⟩ : Nonempty (Work.Tubular.Euc k ≃L[ℝ] (Fin k → ℝ)) :=
    ⟨ContinuousLinearEquiv.ofFinrankEq (by simp)⟩
  let Z₁ : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ)
      (Work.ThomBordism.PontryaginThom.CoverIdx V k) := nu.mapFibre eL
  obtain ⟨hψ, hψproj, hψnorm, hψzero⟩ := Work.Tubular.totalSpace_mapFibre_homeo eL nu
  let ψ : Z₁.TotalSpace ≃ₜ Work.Tubular.NormalTotal E := hψ.symm.trans φ
  haveI hmodel : Module.Finite ℤ ((Work.Cohomology.relChains (TopCat.of Z₁.TotalSpace)
      (Work.Thom.zeroComplement Z₁)).homology j) :=
    Work.ThomBordism.finiteHomologyThomPair Z₁ j
  have hlen1 : ∀ p : Z₁.TotalSpace, (Work.Thom.fibreNorm Z₁ p ≠ 0) ↔
      (Work.Tubular.normalNorm E (ψ p) ≠ 0) := by
    intro p
    have h3 : (Work.Thom.fibreNorm Z₁ p ≠ 0) ↔ (Work.Thom.fibreNorm nu (hψ.symm p) ≠ 0) := by
      have h4 := hψnorm (hψ.symm p)
      rw [hψ.apply_symm_apply] at h4
      exact not_congr h4
    have h5 : (Work.Thom.fibreNorm nu (hψ.symm p) ≠ 0) ↔
        (Work.Tubular.normalNorm E (φ (hψ.symm p)) ≠ 0) := by
      rw [Work.Tubular.fibreNorm_eq_normalNorm, Work.Tubular.eucNormalHomeomorph_apply]
    exact h3.trans h5
  have hAB : ∀ p : Z₁.TotalSpace, p ∈ Work.Thom.zeroComplement Z₁ ↔
      ψ p ∈ Work.Tubular.normalNonzero E := by
    intro p
    have hone : (p ∈ Work.Thom.zeroComplement Z₁) ↔ Work.Thom.fibreNorm Z₁ p ≠ 0 := by
      rw [Work.Thom.mem_zeroComplement, Work.Thom.fibreNorm, norm_ne_zero_iff]
    rw [Work.Tubular.mem_normalNonzero]
    exact hone.trans (hlen1 p)
  have hw : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.subtypeIncl (TopCat.of Z₁.TotalSpace) (Work.Thom.zeroComplement Z₁))
      (TopCat.ofHom ψ)
      = CategoryTheory.CategoryStruct.comp
        (TopCat.ofHom (ψ.subtype hAB))
        (Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)) := by
    apply TopCat.ext
    intro a
    rfl
  let cZ : (Work.Cohomology.relChains (TopCat.of Z₁.TotalSpace) (Work.Thom.zeroComplement Z₁)) ⟶
      (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)) :=
    Work.Cohomology.relChainsMapOf (TopCat.of Z₁.TotalSpace)
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Thom.zeroComplement Z₁)
      (Work.Tubular.normalNonzero E)
      (TopCat.ofHom ψ) (TopCat.ofHom (ψ.subtype hAB)) hw
  haveI hiso : IsIso (HomologicalComplex.homologyMap cZ j) :=
    Work.Tubular.isIso_relChainsMapOf_homeoSub (X := TopCat.of Z₁.TotalSpace)
      (Y := TopCat.of (Work.Tubular.NormalTotal E)) (A := Work.Thom.zeroComplement Z₁)
      (B := Work.Tubular.normalNonzero E) ψ hAB hw j
  exact Module.Finite.equiv (Work.Cohomology.redH0_linEquivOfIso
    (CategoryTheory.asIso (HomologicalComplex.homologyMap cZ j)))

/-! ## Finiteness of the relative homology of `(ν, ν∖{x₀})`

This is the local homology of the `(8+k)`-dimensional manifold `ν = NormalTotal E` at the point
`x₀` of the zero section: `ℤ` in degree `8+k` and zero otherwise
(`Work.Cohomology.localHomology_charted`). -/
private theorem finite_punctNormal (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) (j : ℕ) :
    Module.Finite ℤ ((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
      {p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.PuncturedDiscPair.basePt E x}).homology j) := by
  classical
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv
  obtain ⟨hChb⟩ := Work.ThomBordism.chartedSpaceTotalSpace hk (Work.Tubular.normalBundle E ND)
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + k)))
      (Work.Tubular.normalBundle E ND).TotalSpace := hChb
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + k))) (Work.Tubular.NormalTotal E) :=
    Homeomorph.chartedSpace (Work.Tubular.eucNormalHomeomorph E ND)
  rcases eq_or_ne j (8 + k) with hj | hj
  · subst hj
    obtain ⟨e⟩ := (Work.Cohomology.localHomology_charted (8 + k) (by omega)
      (Work.Tubular.NormalTotal E) (Work.Tubular.PuncturedDiscPair.basePt E x) (8 + k)).1 rfl
    exact Module.Finite.equiv (Work.Cohomology.redH0_linEquivOfIso e).symm
  · have hz := (Work.Cohomology.localHomology_charted (8 + k) (by omega)
      (Work.Tubular.NormalTotal E) (Work.Tubular.PuncturedDiscPair.basePt E x) j).2 hj
    haveI : Subsingleton ↥((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        {p : Work.Tubular.NormalTotal E |
          p ≠ Work.Tubular.PuncturedDiscPair.basePt E x}).homology j) :=
      ModuleCat.subsingleton_of_isZero hz
    exact Module.Finite.of_surjective (0 : ℤ →ₗ[ℤ] ↥((Work.Cohomology.relChains
        (TopCat.of (Work.Tubular.NormalTotal E))
        {p : Work.Tubular.NormalTotal E |
          p ≠ Work.Tubular.PuncturedDiscPair.basePt E x}).homology j))
      (fun y => ⟨0, by rw [map_zero]; exact Subsingleton.elim 0 y⟩)

theorem punctRelHomologyFinite {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    ∀ j : ℕ, Module.Finite ℤ
      ↥((Work.Cohomology.relChains (TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
        (Work.Tubular.PuncturedDiscPair.PunctRel E x)).homology j) := by
  classical
  intro j
  let X : TopCat := TopCat.of (Work.Tubular.NormalTotal E)
  let A : Set X := Work.Tubular.normalNonzero E
  let B : Set X := {p : X | p ≠ Work.Tubular.PuncturedDiscPair.basePt E x}
  have hAB : A ⊆ B := by
    intro p hp
    show p ≠ Work.Tubular.PuncturedDiscPair.basePt E x
    intro h
    exact (Work.Tubular.mem_normalNonzero).mp hp
      (h ▸ Work.Tubular.PuncturedDiscPair.normalNorm_basePt E x)
  have hAfin : Module.Finite ℤ ((Work.Cohomology.relChains X A).homology j) :=
    finite_normalNonzero hk E j
  have hBfin : Module.Finite ℤ ((Work.Cohomology.relChains X B).homology (j + 1)) :=
    finite_punctNormal hk E x (j + 1)
  have hS := Work.Cohomology.relChains_triple_shortExact X A B hAB
  have hex := hS.homology_exact₁ (j + 1) j (by simp [ComplexShape.down])
  have hker := CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hex
  have hX₁ : Module.Finite ℤ
      ((CategoryTheory.Limits.cokernel (Work.Cohomology.inclChainsSub X A B hAB)).homology j) :=
    Work.ThomBordism.Grassmann.Torsion.moduleFinite_of_exact_pair
      (hS.δ (j + 1) j (by simp [ComplexShape.down])).hom
      (HomologicalComplex.homologyMap (Work.Cohomology.tripleShort X A B hAB).f j).hom
      hker hBfin hAfin
  obtain ⟨e⟩ := Work.Cohomology.coker_inclChainsSub_homology_iso hAB j
  exact Module.Finite.equiv (Work.Cohomology.redH0_linEquivOfIso e)

end

end Work.ThomBordism
