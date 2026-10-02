import Mathlib
import Submission.Work.ThomBordism.relCohThomPairNormalTotal_iso_int
import Submission.Work.ThomBordism.relKronH_kernel_eq_torsion
import Submission.Work.ThomBordism.thomPairTopHomologyIsoV2
import Submission.Work.Tubular.relKronecker_chain
import Submission.Work.Tubular.Defs
import Submission.Work.ThomBordism.relHomAux
import Submission.Work.Tubular.totalSpace_mapFibre_homeo
import Submission.Work.ThomBordism.finiteHomologyThomPair

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false


open CategoryTheory

section SmulInstances

-- The `ℤ`-module structure rather than the additive `zsmul` is the action for which the
-- universal-coefficient statements are phrased.
attribute [local instance 100] ZSMul.toSMul

/-- **A non-zero element of a `ℤ`-module isomorphic to `ℤ` is not torsion.**  Transporting along a
linear equivalence to `ℤ`, a multiple `N • x` vanishes only if `x` does, using that `ℤ` is a domain.
The statement is phrased for the *module* action, which is the one appearing in
`Work.ThomBordism.relKronH_kernel_eq_torsion`. -/
private lemma smul_ne_zero_of_linearEquiv_int {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] ℤ) {x : M} (hx : x ≠ 0) : ∀ N : ℕ, 0 < N → (N : ℤ) • x ≠ 0 := by
  intro N _ h
  apply hx
  have h1 : e ((N : ℤ) • x) = 0 := by rw [h, map_zero]
  have h4 : (N : ℤ) • (e x) = 0 := by simpa only [map_smul] using h1
  have h2 : e x = 0 := by
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 (by omega)
    · exact h5
  exact e.injective (by rw [h2, map_zero])

end SmulInstances

namespace Work.ThomBordism

noncomputable section

theorem normalTotal_relKronH_kernel_bot {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    ∀ b : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E),
      (∀ z, Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (8 + k) b z = 0) → b = 0 := by
  classical
  intro b hb
  by_contra hbne
  haveI hpc : PathConnectedSpace V.pt := Work.Tubular.pathConnectedSpace_of_man8 V
  -- The top relative cohomology of the Thom pair is `ℤ`, so `b ≠ 0` is not torsion.
  obtain ⟨eℤ⟩ := Work.ThomBordism.relCohThomPairNormalTotal_iso_int (V := V) (k := k) E
  let eLℤ : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) ≃ₗ[ℤ] ℤ := Work.Cohomology.redH0_linEquivOfIso eℤ
  have hnt := smul_ne_zero_of_linearEquiv_int eLℤ hbne
  -- The Euclidean normal bundle of the embedding, in the two fibre models.
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion (V := V) (k := k)
    E.e (E.smooth.of_le (by simp)) E.injective_mfderiv
  let nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k)
      (Work.ThomBordism.PontryaginThom.CoverIdx V k) := Work.Tubular.normalBundle E ND
  let φ : nu.TotalSpace ≃ₜ Work.Tubular.NormalTotal E := Work.Tubular.eucNormalHomeomorph E ND
  obtain ⟨eL⟩ : Nonempty (Work.Tubular.Euc k ≃L[ℝ] (Fin k → ℝ)) :=
    ⟨ContinuousLinearEquiv.ofFinrankEq (by simp)⟩
  let Z₁ : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ)
      (Work.ThomBordism.PontryaginThom.CoverIdx V k) := nu.mapFibre eL
  obtain ⟨hψ, -, hψnorm, -⟩ := Work.Tubular.totalSpace_mapFibre_homeo eL nu
  let ψ₁ : Z₁.TotalSpace ≃ₜ Work.Tubular.NormalTotal E := hψ.symm.trans φ
  -- the identification of the two removed sets
  have hlen : ∀ p : nu.TotalSpace, Work.Thom.fibreNorm nu p ≠ 0 ↔
      Work.Tubular.normalNorm E (φ p) ≠ 0 := by
    intro p
    rw [Work.Tubular.fibreNorm_eq_normalNorm, Work.Tubular.eucNormalHomeomorph_apply]
  have hlen1 : ∀ p : Z₁.TotalSpace, Work.Thom.fibreNorm Z₁ p ≠ 0 ↔
      Work.Tubular.normalNorm E (ψ₁ p) ≠ 0 := by
    intro p
    have h3 : (Work.Thom.fibreNorm Z₁ p ≠ 0) ↔ (Work.Thom.fibreNorm nu (hψ.symm p) ≠ 0) := by
      have h4 := hψnorm (hψ.symm p)
      rw [hψ.apply_symm_apply] at h4
      exact not_congr h4
    exact h3.trans (hlen (hψ.symm p))
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
      = CategoryTheory.CategoryStruct.comp
        (TopCat.ofHom (ψ₁.subtype hAB))
        (Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)) := by
    apply TopCat.ext
    intro a
    rfl
  -- finiteness of the relative homology one degree below, transported from the model pair
  haveI hfinModel : Module.Finite ℤ ((Work.Cohomology.relChains (TopCat.of Z₁.TotalSpace)
      (Work.Thom.zeroComplement Z₁)).homology ((8 + k) - 1)) :=
    Work.ThomBordism.finiteHomologyThomPair Z₁ ((8 + k) - 1)
  let cZ : (Work.Cohomology.relChains (TopCat.of Z₁.TotalSpace)
        (Work.Thom.zeroComplement Z₁)) ⟶
      (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)) :=
    Work.Cohomology.relChainsMapOf (TopCat.of Z₁.TotalSpace)
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Thom.zeroComplement Z₁)
      (Work.Tubular.normalNonzero E)
      (TopCat.ofHom ψ₁)
      (TopCat.ofHom (ψ₁.subtype hAB)) hw
  haveI hiso : IsIso (HomologicalComplex.homologyMap cZ ((8 + k) - 1)) :=
    Work.Tubular.isIso_relChainsMapOf_homeoSub (X := TopCat.of Z₁.TotalSpace)
      (Y := TopCat.of (Work.Tubular.NormalTotal E)) (A := Work.Thom.zeroComplement Z₁)
      (B := Work.Tubular.normalNonzero E) ψ₁ hAB hw ((8 + k) - 1)
  have hfin : Module.Finite ℤ ((Work.Cohomology.relChains
      (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)).homology ((8 + k) - 1)) :=
    Module.Finite.equiv (Work.Cohomology.redH0_linEquivOfIso
      (CategoryTheory.asIso (HomologicalComplex.homologyMap cZ ((8 + k) - 1))))
  -- a non-torsion class is detected by some relative homology class
  obtain ⟨β, hβ⟩ := Work.ThomBordism.relKronH_kernel_eq_torsion
    (X := TopCat.of (Work.Tubular.NormalTotal E)) (A := Work.Tubular.normalNonzero E)
    (n := 8 + k) hfin b hnt
  exact hβ (hb β)

end

end Work.ThomBordism
