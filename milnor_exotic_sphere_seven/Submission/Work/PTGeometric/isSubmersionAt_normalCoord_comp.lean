import Mathlib
import Submission.Work.Tubular.Transversality
import Submission.Work.ThomBordism.Transversality.TransverseSard.LocalRep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `ℓ ∘ normalCoord` is a submersion at the zero section

The tubular neighbourhood theorem (`Work.Tubular.TubeChart`) provides a normal coordinate
`normalCoord E C : ℝ^{8+k} → ℝ^{8+k}` whose zero locus is the image of `V`, and the transversality
datum `Work.Tubular.TubeTransversality` says that its derivative at `E.e x` has image exactly the
normal space `ν_x = T_x^⊥`.  Composing with a linear map `ℓ : ℝ^{8+k} → ℝ^k` whose restriction to
`ν_x` is an isomorphism makes that derivative surjective, and hence the composite a submersion at
`E.e x` (the chart-level normal form
`Work.ThomBordism.Transversality.TransverseSard.isSubmersionAt_of_surjective_fderiv_localRep`).

This is the TUBULAR input used by the collapse-end smoothness in `Work.PTGeometric`
(see `README.md` §20.5, item 3).
-/

open scoped Manifold ContDiff Topology
open Function

namespace Work.PTGeometric

open Work.Tubular

noncomputable section

theorem isSubmersionAt_normalCoord_comp {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (hT : Work.Tubular.TubeTransversality E ε C)
    (x : V.pt) :
    ∃ ℓ : Work.Tubular.Euc (8 + k) →L[ℝ] EuclideanSpace ℝ (Fin k),
      (∀ z ∈ Work.Tubular.normalSpace E x, ℓ z = 0 → z = 0) ∧
      Manifold.IsSubmersionAt (modelWithCornersSelf ℝ (Work.Tubular.Euc (8 + k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => ℓ (Work.Tubular.normalCoord E C y)) (E.e x) := by
  set ν : Submodule ℝ (Euc (8 + k)) := normalSpace E x with hν
  have hfr : Module.finrank ℝ ν = k := by
    rw [hν, finrank_normalSpace]
    omega
  let eL : ν ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := ν) (F := EuclideanSpace ℝ (Fin k))
      (by rw [hfr, finrank_euclideanSpace_fin])
  let ℓ : Euc (8 + k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    eL.toContinuousLinearMap.comp ν.orthogonalProjectionOnto
  have hℓ_apply : ∀ z : Euc (8 + k), ℓ z = eL.toContinuousLinearMap (ν.orthogonalProjectionOnto z) :=
    fun z => rfl
  refine ⟨ℓ, ?_, ?_⟩
  · -- the kernel of `ℓ` meets `ν` trivially
    intro z hz hz0
    have h1 : ℓ z = eL.toContinuousLinearMap ⟨z, hz⟩ := by
      rw [hℓ_apply z, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨z, hz⟩]
    rw [h1] at hz0
    have h2 : eL ⟨z, hz⟩ = 0 := hz0
    have h3 : (⟨z, hz⟩ : ν) = 0 := LinearEquiv.map_eq_zero_iff eL.toLinearEquiv |>.1 h2
    simpa using congrArg Subtype.val h3
  · -- the composite is a submersion at `E.e x`
    have hnc0 : normalCoord E C (E.e x) = 0 :=
      (normalCoord_eq_zero_iff E C (C.mem_openTube x)).mpr ⟨x, rfl⟩
    have hfx : (fun y => ℓ (normalCoord E C y)) (E.e x) = 0 := by
      simp [hnc0]
    have hcd : ContDiffOn ℝ ∞ (normalCoord E C) C.openTube :=
      (contMDiffOn_iff_contDiffOn).mp (contMDiffOn_normalCoord E C)
    have hdiff : DifferentiableAt ℝ (normalCoord E C) (E.e x) :=
      (hcd.contDiffAt (C.openTube_isOpen.mem_nhds (C.mem_openTube x))).differentiableAt (by simp)
    have hderiv : fderiv ℝ (fun y => ℓ (normalCoord E C y)) (E.e x)
        = ℓ.comp (fderiv ℝ (normalCoord E C) (E.e x)) := by
      have h1 : HasFDerivAt (normalCoord E C) (fderiv ℝ (normalCoord E C) (E.e x)) (E.e x) :=
        hdiff.hasFDerivAt
      have h2 : HasFDerivAt (fun y => ℓ (normalCoord E C y))
          (ℓ.comp (fderiv ℝ (normalCoord E C) (E.e x))) (E.e x) :=
        (ContinuousLinearMap.hasFDerivAt ℓ).comp (E.e x) h1
      exact h2.fderiv
    have hrange : (fderiv ℝ (normalCoord E C) (E.e x)).toLinearMap.range = ν := by
      rw [hν, ← hT.mfderiv_range x, mfderiv_eq_fderiv]
      rfl
    have hsurj : Function.Surjective (ℓ.comp (fderiv ℝ (normalCoord E C) (E.e x))) := by
      intro w
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (show ((eL.symm w : ν) : Euc (8 + k)) ∈
        (fderiv ℝ (normalCoord E C) (E.e x)).toLinearMap.range from by
          rw [hrange]; exact (eL.symm w).2)
      refine ⟨z, ?_⟩
      show ℓ ((fderiv ℝ (normalCoord E C) (E.e x)) z) = w
      have hz' : (fderiv ℝ (normalCoord E C) (E.e x)) z = ((eL.symm w : ν) : Euc (8 + k)) := hz
      rw [hz']
      show eL.toContinuousLinearMap (ν.orthogonalProjectionOnto ((eL.symm w : ν) : Euc (8 + k)))
        = w
      rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (eL.symm w)]
      show eL (eL.symm w) = w
      exact eL.apply_symm_apply w
    have hxi : E.e x ∉ (modelWithCornersSelf ℝ (Euc (8 + k))).boundary (Euc (8 + k)) := by
      rw [ModelWithCorners.Boundaryless.boundary_eq_empty]
      simp
    have hVx : ((chartAt (Euc (8 + k)) (E.e x)).extend
        (modelWithCornersSelf ℝ (Euc (8 + k)))) (E.e x) ∈ C.openTube := by
      show E.e x ∈ C.openTube
      exact C.mem_openTube x
    have htarget : ((chartAt (Euc (8 + k)) (E.e x)).extend
        (modelWithCornersSelf ℝ (Euc (8 + k)))).target = Set.univ := by
      rw [OpenPartialHomeomorph.extend_target']
      simp [chartAt_self_eq]
    have hVsub : C.openTube ⊆ ((chartAt (Euc (8 + k)) (E.e x)).extend
        (modelWithCornersSelf ℝ (Euc (8 + k)))).target := by
      rw [htarget]
      exact fun _ _ => trivial
    have hrep : (fun v : Euc (8 + k) => (fun y => ℓ (normalCoord E C y))
        (((chartAt (Euc (8 + k)) (E.e x)).extend
          (modelWithCornersSelf ℝ (Euc (8 + k)))).symm v))
        = (fun v : Euc (8 + k) => ℓ (normalCoord E C v)) := by
      funext v
      rfl
    have hf : ContDiffOn ℝ ∞ (fun v => (fun y => ℓ (normalCoord E C y))
        (((chartAt (Euc (8 + k)) (E.e x)).extend
          (modelWithCornersSelf ℝ (Euc (8 + k)))).symm v)) C.openTube := by
      rw [hrep]
      simpa only [Function.comp_def] using
        (ContDiffOn.comp (s := C.openTube) (t := Set.univ)
          ((ContinuousLinearMap.contDiff ℓ).contDiffOn (s := Set.univ)) hcd
          (fun _ _ => Set.mem_univ _))
    have hsurj' : Function.Surjective (fderiv ℝ (fun v => (fun y => ℓ (normalCoord E C y))
        (((chartAt (Euc (8 + k)) (E.e x)).extend
          (modelWithCornersSelf ℝ (Euc (8 + k)))).symm v))
        (((chartAt (Euc (8 + k)) (E.e x)).extend
          (modelWithCornersSelf ℝ (Euc (8 + k)))) (E.e x))) := by
      show Function.Surjective (fderiv ℝ (fun v : Euc (8 + k) => ℓ (normalCoord E C v))
        (E.e x))
      rw [hderiv]
      exact hsurj
    exact Work.ThomBordism.Transversality.TransverseSard.isSubmersionAt_of_surjective_fderiv_localRep
      (modelWithCornersSelf ℝ (Euc (8 + k)))
      (IsManifold.chart_mem_maximalAtlas (H := Euc (8 + k))
        (I := modelWithCornersSelf ℝ (Euc (8 + k))) (E.e x))
      (mem_chart_source (Euc (8 + k)) (E.e x)) hxi hfx C.openTube_isOpen hVx hVsub hf hsurj'

end

end Work.PTGeometric
