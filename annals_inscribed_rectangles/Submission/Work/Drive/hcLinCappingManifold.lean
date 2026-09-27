import Mathlib
import Submission.Work.Drive.hcRotation
import Submission.Work.Drive.linCapping
import Submission.Work.Drive.planeClassDeriv_eq_mfderiv

/-!
# `hc` for a presentation with its projective class perturbed, in the manifold form

`Submission/Work/Drive/hcLinCapping.lean` transports the counting engine's chart-form conditions along
a perturbation of the projective class, but only when the perturbation is the *same* for the three
chains (its `hV` equivalence needs the three base chart coordinates to coincide, which is exactly the
triple-point hypothesis for a common perturbation).  The engine's **immersion** condition `hc`, on the
other hand, is a *pointwise* statement and transfers chain by chain, with an *arbitrary*
perturbation `A k` on the `k`-th chain.

This file proves that per-chain transfer in the manifold form:

* `Work.Drive.injective_mfderiv_projMap` — the differential of a projectivised linear automorphism of
  `ℝP³` is injective (the analogue, for `linCapping`, of
  `Work.Drive.injective_mfderiv_projRot` of `hcRotation.lean`);
* `Work.Drive.cls_linCapping_eq` — the class map of `linCapping A ∘ P` is the class map of `P`
  composed with `Projectivization.map A`;
* `Work.Drive.injective_mfderiv_cls_linCapping` — `hc` for `linCapping A ∘ P` from `hc` for `P`;
* `Work.Drive.mdifferentiableAt_cls_of_contMDiff` — the smoothness input of the previous line, from
  `ContMDiff (𝓡 2) (𝓡 4) Ctop P` alone;
* `Work.Drive.planeClassDeriv_injective_of_linCapping` — **the engine-facing form**: the engine's
  immersion condition `Work.Drive.planeClassDeriv` for the perturbed presentation
  `fun j y => linCapping (A j) (P j y)` follows from the same condition for `P`, through the
  chart-free identification `Work.Drive.planeClassDeriv_injective_iff`.

In particular, with `Work.Drive.contMDiff_linCapping` (`linCapping.lean`) this discharges `hc` for the
three perturbed rotated planes of the design's triple from the *proved* `hc` for the rotated planes
(`Work.Drive.injective_mfderiv_cls_rotPresentation`, session 36, via the same chain rule).
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology LinearAlgebra.Projectivization

attribute [local instance] Work.Drive.projCharted
attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-! ## 1. The projectivised linear automorphism of `ℝP³` is an immersion -/

/-- The inverse law of the projectivised linear automorphism: `Projectivization.map A.symm` is a left
inverse of `Projectivization.map A`. -/
theorem projMap_symm_comp (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    Projectivization.map (A.symm : Eucl 3 →ₗ[ℝ] Eucl 3) A.symm.injective
      ∘ Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective = id := by
  funext p
  rw [Function.comp_apply]
  induction p using Projectivization.ind with
  | h a ha =>
    rw [Projectivization.map_mk, Projectivization.map_mk]
    exact (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, by
      rw [one_smul]
      exact (A.symm_apply_apply a).symm⟩

/-- **The differential of a projectivised linear automorphism of `ℝP³` is injective.**  The proof is
the same as for the rotation (`Work.Drive.injective_mfderiv_projRot`): `Projectivization.map A.symm` is
a left inverse, so the chain rule exhibits the differential of the identity as the composite. -/
theorem injective_mfderiv_projMap (A : Eucl 3 ≃L[ℝ] Eucl 3) (q : Projectivization ℝ (Eucl 3)) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3)
      A.injective) q) := by
  have hmd : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective) q :=
    (contMDiffAt_projMap A q).mdifferentiableAt (by simp)
  have hmd' : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Projectivization.map (A.symm : Eucl 3 →ₗ[ℝ] Eucl 3) A.symm.injective)
      (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective q) :=
    (contMDiffAt_projMap A.symm _).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) q hmd' hmd
  have hid : (Projectivization.map (A.symm : Eucl 3 →ₗ[ℝ] Eucl 3) A.symm.injective
      ∘ Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective) = id := projMap_symm_comp A
  have hcomp' : ContinuousLinearMap.id ℝ _ =
      (mfderiv (𝓡 3) (𝓡 3) (Projectivization.map (A.symm : Eucl 3 →ₗ[ℝ] Eucl 3) A.symm.injective)
        (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective q)).comp
        (mfderiv (𝓡 3) (𝓡 3) (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective) q) := by
    rw [← hcomp, hid, mfderiv_id]
  intro u v huv
  have key : ∀ w : TangentSpace (𝓡 3) q,
      (mfderiv (𝓡 3) (𝓡 3) (Projectivization.map (A.symm : Eucl 3 →ₗ[ℝ] Eucl 3) A.symm.injective)
        (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective q))
        ((mfderiv (𝓡 3) (𝓡 3) (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective) q) w)
        = w := fun w => (congrArg (fun L => L w) hcomp').symm
  exact (key u).symm.trans (by rw [huv]; exact key v)

/-! ## 2. The class map of a class-perturbed presentation -/

/-- The class map of `linCapping A ∘ P` is the class map of `P` composed with the projectivised
linear automorphism `Projectivization.map A`. -/
theorem cls_linCapping_eq (A : Eucl 3 ≃L[ℝ] Eucl 3)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    (fun y : EuclideanSpace ℝ (Fin 2) => (cappingSpaceHomeoProj (linCapping A (P y))).2)
      = Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective
          ∘ (fun y : EuclideanSpace ℝ (Fin 2) => (cappingSpaceHomeoProj (P y)).2) := by
  funext y
  exact congrArg Prod.snd (cappingSpaceHomeoProj_linCapping A (P y))

/-- **The immersion condition `hc` transfers to a class-perturbed presentation.** -/
theorem injective_mfderiv_cls_linCapping (A : Eucl 3 ≃L[ℝ] Eucl 3)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (y : EuclideanSpace ℝ (Fin 2))
    (hcls : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (P y')).2) y)
    (hbase : Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (P y')).2) y)) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (linCapping A (P y'))).2) y) := by
  rw [cls_linCapping_eq A P]
  have hcomp := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3) y
    (g := Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective)
    (f := fun y' => (cappingSpaceHomeoProj (P y')).2)
    ((contMDiffAt_projMap A _).mdifferentiableAt (by simp)) hcls
  rw [hcomp]
  show Function.Injective (fun w : TangentSpace (𝓡 2) y =>
    (mfderiv (𝓡 3) (𝓡 3) (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective)
        ((fun y' => (cappingSpaceHomeoProj (P y')).2) y))
      ((mfderiv (𝓡 2) (𝓡 3) (fun y' => (cappingSpaceHomeoProj (P y')).2) y) w))
  intro u v huv
  exact hbase (injective_mfderiv_projMap A ((fun y' => (cappingSpaceHomeoProj (P y')).2) y) huv)

/-- **The smoothness input of the previous line**, from the smoothness of the presentation alone: the
class map `y ↦ (cappingSpaceHomeoProj (P y)).2` is `C^∞` where `P` is. -/
theorem mdifferentiableAt_cls_of_contMDiff {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hP : ContMDiff (𝓡 2) (𝓡 4) Ctop P) (y : EuclideanSpace ℝ (Fin 2)) :
    MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (P y')).2) y := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.halfLineProjectiveCharted
  have hG : ContMDiffAt (𝓡 2) (𝓡 4) Work.Drive.Ctop
      (fun w => Work.Drive.cappingSpaceHomeoProj (P w)) y := by
    have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin 2)) (H' := EuclideanSpace ℝ (Fin 2)) (𝓡 2)
      (M := Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := Work.Drive.CappingSpace) (n := Work.Drive.Ctop)
      Work.Drive.cappingSpaceHomeoProj.symm P Set.univ y
    exact hiff.mp (hP.contMDiffAt)
  exact (((Work.Drive.contMDiffAt_halfLineProjective_iff
    (fun w => Work.Drive.cappingSpaceHomeoProj (P w)) y).mp hG).2).mdifferentiableAt (by simp)

/-! ## 3. The engine-facing form: `hc` for the perturbed plane presentations -/

/-- **The engine's immersion condition `hc` for the perturbed presentations, per chain.**  With the
chart-free identification `Work.Drive.planeClassDeriv_injective_iff`, the transport above gives the
condition in the exact form in which the transversality engine
(`Work.Drive.meet3Generic_trans_clampedSweeps`) consumes it, with a *different* perturbation
`A k` on each chain. -/
theorem planeClassDeriv_injective_of_linCapping (A : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hbase : Function.Injective (Work.Drive.planeClassDeriv c ψ P k x)) :
    Function.Injective (Work.Drive.planeClassDeriv c ψ
      (fun j y => Work.Drive.linCapping (A j) (P j y)) k x) := by
  have hP' : ∀ j, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop
      (fun y => Work.Drive.linCapping (A j) (P j y)) :=
    fun j => (Work.Drive.contMDiff_linCapping (A j)).comp (hP j)
  rw [Work.Drive.planeClassDeriv_injective_iff c ψ
    (fun j y => Work.Drive.linCapping (A j) (P j y)) hP' k x]
  exact Work.Drive.injective_mfderiv_cls_linCapping (A k) (P k)
    (Work.Drive.mk2 (x k 0) (x k 1))
    (Work.Drive.mdifferentiableAt_cls_of_contMDiff (hP k) _)
    ((Work.Drive.planeClassDeriv_injective_iff c ψ P hP k x).mp hbase)

/-! ## 4. The one-stop form for the design's perturbed rotated planes -/

/-- **`hc` for the perturbed rotated plane** `linCapping A ∘ rotPresentation Q w`, from the immersion
of the *disk* presentation of the chart's plane.  This composes the rotation transport of session 36
(`Work.Drive.injective_mfderiv_cls_rotPresentation_of_diskImmersion`) with the class-perturbation
transport above, and it is the form in which the design's three chains
`clampedSweep (c k) ψ (linCapping (A k) ∘ rotPresentation Q (u k))` receive their immersion
hypothesis — the chart's disk presentation being immersive (`h0`, `h1`, `hf`, `hf_inj`) is the only
geometric input. -/
theorem injective_mfderiv_cls_linCapping_rotPresentation (Q : ℂ → CappingSpace)
    (A : Eucl 3 ≃L[ℝ] Eucl 3) (w : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2))
    (h0 : y 0 ∈ Set.Ioo (0 : ℝ) 1) (h1 : y 1 ∈ Set.Ioo (0 : ℝ) 1)
    (hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (cappingSpaceHomeoProj (Q z)).2) (sqDisk (foldBox y)))
    (hf_inj : Function.Injective (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (cappingSpaceHomeoProj (Q z)).2) (sqDisk (foldBox y)))) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (linCapping A (rotPresentation Q w y'))).2) y) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective w
  rw [← ht]
  have hfold : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) foldBox :=
    contDiff_iff_contDiffAt.mpr fun y =>
      contMDiffAt_iff_contDiffAt.mp (foldBox_contMDiff y)
  have hgd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox y)) :=
    sqDisk_contDiff.comp hfold
  have hg : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℂ))
      (fun y : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox y)) y :=
    (contMDiffAt_iff_contDiffAt.mpr (hgd.contDiffAt)).mdifferentiableAt (by simp)
  have hcls : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y := by
    have h := hf.comp y hg
    simpa only [Function.comp_def, diskPlane_apply] using h
  have hclsRot : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (rotPresentation Q ((t : ℝ) : UnitAddCircle) y')).2) y := by
    rw [cls_rotPresentation_eq Q t]
    exact (mdifferentiableAt_projRot_aux t _).comp y hcls
  exact injective_mfderiv_cls_linCapping A
    (rotPresentation Q ((t : ℝ) : UnitAddCircle)) y hclsRot
    (injective_mfderiv_cls_rotPresentation_of_diskImmersion Q ((t : ℝ) : UnitAddCircle)
      y h0 h1 hf hf_inj)

end

end Work.Drive
