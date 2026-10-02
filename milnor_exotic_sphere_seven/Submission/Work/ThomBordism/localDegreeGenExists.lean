import Mathlib
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.ThomBordism.localDegreeSpan
import Submission.Work.ThomBordism.gaussClassifyingNDPad
import Submission.Work.ThomBordism.thomClassPullbackBundleComapRank
import Submission.Work.ThomBordism.thomClassNaturalityBundleIso
import Submission.Work.ThomBordism.tubeThomRepOfEmbeddingOdd
import Submission.Work.Tubular.nonempty_thomClass_of_bundleIso
import Submission.Work.Tubular.totalSpace_mapFibre_homeo
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Tubular.NormalThom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A generator of `H^k(ν, ν∖0)` implementing the local degree (unconditional form)

The local-degree class of the Thom pair of the normal bundle of an embedded manifold exists, is a
generator of the (free, rank one) relative cohomology `H^k(ν, ν∖0)` and implements the local degree
of the fundamental class of the member w.r.t. the tube collapse class.

The geometric input is only the *existence of the Thom class* of the normal bundle: the normal
bundle of a closed oriented smooth `8`-manifold embedded in `ℝ^{8+k}` is oriented (the orientation
is the complement of the tangent orientation in the ambient space), which in this workspace is
carried by the Gauss map into the oriented Grassmannian `OG k 10`
(`Work.ThomBordism.gaussClassifyingNDPad`) together with the positivity of the transition
determinants of the tautological oriented bundle (`det_coordChangeO_pos`), hence
`Work.Tubular.exists_normalThomClass`.

The rest is bookkeeping: transport along the homeomorphism of pairs
`eucNormalHomeomorph : ν ≅ NormalTotal E` and along the change of the model fibre
`Euc k ≃L[ℝ] (Fin k → ℝ)`, and then apply `Work.ThomBordism.localDegreeSpan`, which produces the
generator and the local-degree identity in one step.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Topology

namespace Work.ThomBordism

open Work.Tubular Work.TangentClasses
open Work.ThomBordism.PontryaginThom

noncomputable section

theorem localDegreeGenExists {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (hε : 0 < ε) (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y.ofLp j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) :
    ∃ U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E),
      Submodule.span ℤ ({U} : Set _) = ⊤ ∧
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U := by
  classical
  obtain ⟨ND⟩ := exists_normalData_of_immersion E.e (E.smooth.of_le (by simp))
    E.injective_mfderiv
  -- the Euclidean normal bundle of the embedding, and its identification with the concrete model
  let nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) (CoverIdx V k) :=
    Work.Tubular.normalBundle E ND
  let φ : nu.TotalSpace ≃ₜ Work.Tubular.NormalTotal E :=
    Work.Tubular.eucNormalHomeomorph E ND
  have hproj : ∀ p : nu.TotalSpace, Work.Tubular.NormalTotal.proj (φ p) = p.1 := fun p => rfl
  have hlen : ∀ p : nu.TotalSpace,
      Work.Thom.fibreNorm nu p ≠ 0 ↔ Work.Tubular.normalNorm E (φ p) ≠ 0 := by
    intro p
    rw [Work.Tubular.fibreNorm_eq_normalNorm, Work.Tubular.eucNormalHomeomorph_apply]
  have hvec : ∀ x : V.pt,
      Work.Tubular.NormalTotal.vec (φ (Work.Thom.zeroSection nu x)) = 0 := by
    intro x
    show Work.Tubular.insCLM E ND ((Work.Tubular.normalBundle E ND).indexAt x) x
      (0 : Work.Tubular.Euc k) = 0
    exact map_zero _
  -- the Thom class of `nu`, from the Gauss classifying data
  obtain ⟨gauss, ⟨eGauss⟩⟩ := Work.ThomBordism.gaussClassifyingNDPad E hk ND
  have hZ : Nonempty (Work.Thom.ThomClass nu k) :=
    Work.Tubular.exists_normalThomClass (k := k) hk
      (G := Work.ThomBordism.Grassmann.OG k 10)
      (κ := Work.ThomBordism.Grassmann.ChartIdx k 10)
      (γ := Work.ThomBordism.Grassmann.tautologicalBundle k 10)
      (fun i j x =>
        Work.ThomBordism.Grassmann.det_coordChangeO_pos i j
          (x : Work.ThomBordism.Grassmann.OG k 10) x.2)
      gauss eGauss
  -- change of the model fibre to the coordinate fibre `Fin k → ℝ`
  obtain ⟨eL⟩ : Nonempty (Work.Tubular.Euc k ≃L[ℝ] (Fin k → ℝ)) :=
    ⟨ContinuousLinearEquiv.ofFinrankEq (by simp)⟩
  let Z₁ : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) (CoverIdx V k) :=
    Work.TangentClasses.RealBundle.mapFibre eL nu
  obtain ⟨hψ, hψproj, hψnorm, hψzero⟩ := Work.Tubular.totalSpace_mapFibre_homeo eL nu
  let ψ₁ : Z₁.TotalSpace ≃ₜ Work.Tubular.NormalTotal E := hψ.symm.trans φ
  have hZ1 : Nonempty (Work.Thom.ThomClass Z₁ k) :=
    Work.Tubular.nonempty_thomClass_of_bundleIso (Work.Tubular.bundleIsoMapFibre eL nu)
      (Classical.choice hZ)
  have hproj1 : ∀ p : Z₁.TotalSpace, Work.Tubular.NormalTotal.proj (ψ₁ p) = p.1 := by
    intro p
    show Work.Tubular.NormalTotal.proj (φ (hψ.symm p)) = p.1
    rw [hproj]
    have hh := hψproj (hψ.symm p)
    rw [hψ.apply_symm_apply] at hh
    exact hh.symm
  have hlen1 : ∀ p : Z₁.TotalSpace,
      Work.Thom.fibreNorm Z₁ p ≠ 0 ↔ Work.Tubular.normalNorm E (ψ₁ p) ≠ 0 := by
    intro p
    show Work.Thom.fibreNorm Z₁ p ≠ 0 ↔ Work.Tubular.normalNorm E (φ (hψ.symm p)) ≠ 0
    have h3 : (Work.Thom.fibreNorm Z₁ p ≠ 0) ↔ (Work.Thom.fibreNorm nu (hψ.symm p) ≠ 0) := by
      have h4 := hψnorm (hψ.symm p)
      rw [hψ.apply_symm_apply] at h4
      exact not_congr h4
    exact h3.trans (hlen (hψ.symm p))
  have hvec1 : ∀ x : V.pt,
      Work.Tubular.NormalTotal.vec (ψ₁ (Work.Thom.zeroSection Z₁ x)) = 0 := by
    intro x
    show Work.Tubular.NormalTotal.vec (φ (hψ.symm (Work.Thom.zeroSection Z₁ x))) = 0
    have hzz : hψ.symm (Work.Thom.zeroSection Z₁ x) = Work.Thom.zeroSection nu x := by
      rw [← hψ.injective.eq_iff, hψ.apply_symm_apply, hψzero]
    rw [hzz]
    exact hvec x
  -- the box condition in the coordinate fibre of the sphere bundle
  have hbox' : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R := by
    intro y hy i
    simpa using hbox y hy i
  obtain ⟨Ugen, hUgen_span, hUgen⟩ :=
    Work.ThomBordism.localDegreeSpan (V := V) (k := k) (E := E) hk Z₁ ψ₁ hproj1 hlen1 hvec1
      hZ1 q hU hR hbox' g hg hg2
  exact ⟨Ugen, hUgen_span, hUgen⟩

end

end Work.ThomBordism
