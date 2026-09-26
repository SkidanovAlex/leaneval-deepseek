import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs

/-!
# Bridges: from general position to the box slicing

This file collects the (unconditional) glue of the chapter:

* `transverseSphere_of_isCircleUnion` — a compact set which is locally an arc and is a finite
  disjoint union of simple closed curves (`Work.Smooth.Morse.IsCircleUnion`) is a transversality
  witness in the sense of `Work.Topology.SphereSlicing.TransverseSphere`;
* `transverseSphere_of_compact_isLocalArc` — the same with the classification of compact
  `1`-manifolds (`Work.Smooth.Morse.CompactOneManifoldInput`) supplying the circles;
* `transverseSphere_empty`, `sphereSlicing_empty` — the empty surface is in general position, and
  has an (empty) slicing; these are what handles the levels `s < 0`, at which the box sphere is
  empty;
* `BoxSphere_eq_empty_of_neg`, `BoxSphere_zero_eq_singleton` — the box spheres of level `s < 0`
  (empty) and `s = 0` (the centre);
* `aeSliced_of_aeTransverseBox` — **the reduction of the target to the general position of the box
  spheres**: `AeTransverseBox ψ c σ` together with the classical slicing input `SliceInput` of the
  surface gives `Work.BoxShrink.AeSliced ψ c σ`, hence `Work.BoxShrink.AeSlicedAll`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped Topology

namespace Work.Smooth.BoxGeneric

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **From a finite disjoint union of simple closed curves to a transversality witness.**  If `Z`
is a `Work.Smooth.Morse.IsCircleUnion` of the surface, `Z ⊆ S`, and `S ∩ F ⊆ Z`, then `S` meets
the surface in general position in the sense of
`Work.Topology.SphereSlicing.TransverseSphere`. -/
theorem transverseSphere_of_isCircleUnion {ψ : Submission.Diffeo} {Z S : Set R3}
    (h : Work.Smooth.Morse.IsCircleUnion ψ Z) (hZS : Z ⊆ S)
    (hcov : S ∩ (Work.Smooth.Morse.torus ψ).carrier ⊆ Z) :
    Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ) S := by
  obtain ⟨n, γ, hsimple, hdisj, hZ⟩ := h
  refine ⟨Fin n, inferInstance, γ, hsimple, hdisj, ?_, ?_⟩
  · intro i t
    apply hZS
    rw [hZ]
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨t, rfl⟩⟩
  · intro x hxS hxcar
    have hxZ : x ∈ Z := hcov ⟨hxS, hxcar⟩
    rw [hZ] at hxZ
    simpa only [Set.mem_iUnion, Set.mem_range] using hxZ

/-- **A compact set which is locally an arc is in general position** (granted the classification of
compact `1`-manifolds). -/
theorem transverseSphere_of_compact_isLocalArc {ψ : Submission.Diffeo} {S : Set R3}
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hcomp : IsCompact (S ∩ (Work.Smooth.Morse.torus ψ).carrier))
    (harc : Work.Smooth.Morse.IsLocalArc ψ (S ∩ (Work.Smooth.Morse.torus ψ).carrier)) :
    Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ) S :=
  transverseSphere_of_isCircleUnion (hclass _ hcomp harc) inter_subset_left subset_rfl

/-- **The empty set meets any surface in general position.** -/
theorem transverseSphere_empty (P : Work.CoreTopology.ParamTorus) :
    Work.Topology.SphereSlicing.TransverseSphere P (∅ : Set R3) := by
  refine ⟨Fin 0, inferInstance, Fin.elim0, ?_, ?_, ?_, ?_⟩
  · intro i; exact i.elim0
  · intro i; exact i.elim0
  · intro i; exact i.elim0
  · intro x hx; exact absurd hx (Set.notMem_empty x)

/-- **The empty set has an (empty) slicing.** -/
theorem nonempty_sphereSlicing_empty (P : Work.CoreTopology.ParamTorus) :
    Nonempty (Work.InnermostDisk.SphereSlicing P (∅ : Set R3)) :=
  ⟨{ ι := Fin 0
     fintype := inferInstance
     c := Fin.elim0
     simple := fun i => i.elim0
     disjoint := fun i => i.elim0
     mem := fun i => i.elim0
     covers := fun γ h => absurd (h 0) (Set.notMem_empty _)
     disc := Fin.elim0
     disc_inj := fun i => i.elim0
     disc_boundary := fun i => i.elim0
     disc_mem := fun i => i.elim0
     rank := Fin.elim0
     inside := fun i => i.elim0
     inside_subset := fun i => i.elim0
     covers_interior := fun i => i.elim0 }⟩

/-- The box sphere of a negative level is empty. -/
theorem BoxSphere_eq_empty_of_neg {s : ℝ} (hs : s < 0) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Work.Topology.SphereSlicing.BoxSphere s c σ = ∅ := by
  ext y
  simp only [Work.Topology.SphereSlicing.mem_BoxSphere, Set.mem_empty_iff_false, iff_false]
  intro h
  have := Submission.boxNorm_nonneg c σ y
  linarith

/-- The box sphere of level zero is the centre. -/
theorem BoxSphere_zero_eq_singleton (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Work.Topology.SphereSlicing.BoxSphere 0 c σ = {c} := by
  ext y
  simp only [Work.Topology.SphereSlicing.mem_BoxSphere, Set.mem_singleton_iff]
  exact boxNorm_eq_zero_iff c σ y

/-- **The box spheres are in general position for almost every level.**  This is
`AeTransverseBox`; it is the geometric content of the target. -/
theorem aeTransverseBox_iff (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    AeTransverseBox ψ c σ ↔
      ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
          {y : R3 | Submission.boxNorm c σ y = s} := Iff.rfl

/-- **The target from the general position of the box spheres.**  If the box spheres are in general
position for almost every level, then so are the slicings: at every level `s` which is positive and
at which the box sphere is transverse, the classical slicing input
(`Work.Topology.SphereSlicing.SliceInput`, i.e. the Jordan–Schoenflies input of the sibling
subchapter) produces a `Work.InnermostDisk.SphereSlicing` of the box sphere.

Levels `s < 0` are handled separately: the box sphere is then empty and carries the empty
slicing, so the only level thrown away is `s = 0`. -/
theorem aeSliced_of_aeTransverseBox (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (h : AeTransverseBox ψ c σ)
    (hS : Work.Topology.SphereSlicing.SliceInput (Work.Smooth.Morse.torus ψ)) :
    Work.BoxShrink.AeSliced ψ c σ := by
  rw [Work.BoxShrink.AeSliced]
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [h, hne] with s hs hsne
  rcases lt_or_gt_of_ne hsne with hsneg | hspos
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact BoxSphere_eq_empty_of_neg hsneg c σ
    rw [hbox]
    exact nonempty_sphereSlicing_empty _
  · exact ⟨(Work.Topology.SphereSlicing.nonempty_sphereSlicing_of_sliceInput hS
      (Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere hspos c σ) hs).some⟩

end

end Work.Smooth.BoxGeneric
