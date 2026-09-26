import Submission.Work.Smooth.Schoenflies.ConvexRel
import Submission.Work.Smooth.Plane.Convex

/-!
# Repair of the convexity form of planar Jordan–Schoenflies

The sibling chapter `Submission/Work/Smooth/Plane` proves the *convexity form of planar
Jordan–Schoenflies* — a simple closed curve lying in a convex planar set `D ⊆ ℝ³` bounds an embedded
disc contained in `D` (`Work.Smooth.Plane.exists_spanningDisc_of_convex_planar`,
`Work.Smooth.Plane.exists_spanningDisc_of_closedCurve`) — from its classical input
`Work.Smooth.Plane.PlaneJordanInput`, which is **false** as stated
(`Work.Smooth.Schoenflies.not_planeJordanInput`: the predicate
`Work.Smooth.Plane.NullHomotopicAvoiding` is vacuous).

The corrected input `Work.Smooth.Schoenflies.PlaneJordanInputRel` however is a **theorem**, because
the planar Jordan–Schoenflies theorem of this chapter
(`Work.Smooth.Schoenflies.classicalInput`, i.e. `PlaneHypothesis`) holds unconditionally, and the
sibling chapter's argument transfers verbatim to the corrected predicate (`PlaneJordanDataRel.e_mem_of_convex`).

This file therefore proves the convexity form with **no input at all**:

* `planeJordanInputRel : PlaneJordanInputRel` — the corrected classical input, unconditionally;
* `exists_spanningDisc_of_convex_planar_rel` — the `ℝ³` convexity form;
* `exists_spanningDisc_of_closedCurve_rel` — its `Work.CoreTopology.ClosedCurve` form, which is the
  shape needed for the `disc` field of a planar slicing datum.

Applying these in place of the sibling chapter's theorems (and replacing the predicate
`Work.Smooth.Plane.NullHomotopicAvoiding` by `Work.Smooth.Schoenflies.NullHomotopicRel` throughout)
restores the whole planar chapter.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Schoenflies

noncomputable section

/-- **The corrected classical input of the planar chapter, unconditionally.**  Every continuous
`2π`-periodic simple closed plane curve has a corrected Jordan datum — the planar
Jordan–Schoenflies theorem (`classicalInput`) supplies the spanning disc, and the hard direction of
the Jordan curve theorem is `not_nullHomotopicRel_of_mem_V`. -/
theorem planeJordanInputRel : PlaneJordanInputRel := by
  intro c hc hper hinj
  let γ : Work.Smooth.Jordan.PlaneCurve := ⟨c, hc, hper⟩
  have hs : γ.IsSimple := hinj
  obtain ⟨h⟩ := classicalInput γ hs
  have := nonempty_planeJordanDataRel_of_planeSchoenflies h
  simpa [γ] using this

/-- **The convexity form of planar Jordan–Schoenflies in `ℝ³`, unconditional.**  Let `D ⊆ ℝ³` be a
convex subset of the coordinate plane `{y | y (σ 2) = h}` and let `c` be a simple closed curve lying
in `D` (in the sense of `Work.Smooth.Plane.IsSimpleClosedCurveIn`).  Then `c` bounds an embedded disc
whose image is contained in `D`.

This is the corrected form of `Work.Smooth.Plane.exists_spanningDisc_of_convex_planar` (whose
`PlaneJordanInput` hypothesis is false): the projected curve `planeProj σ ∘ c` has a corrected Jordan
datum `planeJordanInputRel`, and `PlaneJordanDataRel.e_mem_of_convex` puts the whole disc of that
datum inside the convex set. -/
theorem exists_spanningDisc_of_convex_planar_rel (σ : Equiv.Perm (Fin 3)) {h : ℝ} {D : Set R3}
    (hD : Convex ℝ D) (hplane : ∀ y ∈ D, y (σ 2) = h) {c : ℝ → R3}
    (hc : Work.Smooth.Plane.IsSimpleClosedCurveIn D c) :
    ∃ e : C(Work.InnermostDisk.Disc, R3), Function.Injective e ∧
      (∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) = c θ) ∧
      ∀ z : Work.InnermostDisk.Disc, e z ∈ D := by
  have hγcont : Continuous fun t : ℝ => Work.Smooth.Plane.planeProj σ (c t) :=
    (Work.Smooth.Plane.continuous_planeProj σ).comp hc.2.1
  have hγper : Function.Periodic (fun t : ℝ => Work.Smooth.Plane.planeProj σ (c t))
      (2 * Real.pi) := by
    intro t
    show Work.Smooth.Plane.planeProj σ (c (t + 2 * Real.pi)) = Work.Smooth.Plane.planeProj σ (c t)
    rw [hc.2.2.1 t]
  have hγinj : Set.InjOn (fun t : ℝ => Work.Smooth.Plane.planeProj σ (c t))
      (Set.Ico 0 (2 * Real.pi)) := by
    intro t ht s hs heq
    exact hc.2.2.2 ht hs (Work.Smooth.Plane.planeProj_injOn σ
      (hplane (c t) (hc.1 t)) (hplane (c s) (hc.1 s)) heq)
  obtain ⟨hJ⟩ := planeJordanInputRel (fun t : ℝ => Work.Smooth.Plane.planeProj σ (c t))
    hγcont hγper hγinj
  have hD'conv : Convex ℝ (Work.Smooth.Plane.planeProj σ '' D) :=
    Work.Smooth.Plane.planeProj_image_convex σ hD
  have hmem' : ∀ t : ℝ, Work.Smooth.Plane.planeProj σ (c t)
      ∈ Work.Smooth.Plane.planeProj σ '' D := fun t => ⟨c t, hc.1 t, rfl⟩
  have key : ∀ z : Work.InnermostDisk.Disc, hJ.e z ∈ Work.Smooth.Plane.planeProj σ '' D :=
    fun z => hJ.e_mem_of_convex hD'conv hγcont hγper hmem' z
  refine ⟨⟨fun z => Work.Smooth.Plane.planeLift σ h (hJ.e z),
      (Work.Smooth.Plane.continuous_planeLift σ h).comp hJ.e.continuous⟩,
    fun z z' hzz' => hJ.inj (Work.Smooth.Plane.planeLift_injective σ h hzz'), ?_, ?_⟩
  · intro θ
    have h1 : hJ.e (Work.CoreTopology.circlePoint θ)
        = Work.Smooth.Plane.planeProj σ (c θ) := hJ.boundary θ
    show Work.Smooth.Plane.planeLift σ h (hJ.e (Work.CoreTopology.circlePoint θ)) = c θ
    rw [h1, Work.Smooth.Plane.planeLift_planeProj σ (hplane (c θ) (hc.1 θ))]
  · intro z
    obtain ⟨y, hyD, hyz⟩ := key z
    show Work.Smooth.Plane.planeLift σ h (hJ.e z) ∈ D
    rw [← hyz, Work.Smooth.Plane.planeLift_planeProj σ (hplane y hyD)]
    exact hyD

/-- **The convexity form in the vocabulary of `Work.CoreTopology.ClosedCurve`**, unconditional: a
simple closed curve of a parametrised torus whose image lies in a convex subset `D` of a coordinate
plane bounds an embedded disc contained in `D`.  This is the corrected form of
`Work.Smooth.Plane.exists_spanningDisc_of_closedCurve`, the statement which supplies the `disc`
field of a planar slicing datum. -/
theorem exists_spanningDisc_of_closedCurve_rel (σ : Equiv.Perm (Fin 3)) {h : ℝ} {D : Set R3}
    (hD : Convex ℝ D) (hplane : ∀ y ∈ D, y (σ 2) = h)
    {P : Work.CoreTopology.ParamTorus} {c : Work.CoreTopology.ClosedCurve P}
    (hsimple : Work.CoreTopology.IsSimple P c) (hmem : ∀ t : ℝ, c.γ t ∈ D) :
    ∃ e : C(Work.InnermostDisk.Disc, R3), Function.Injective e ∧
      (∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) = c.γ θ) ∧
      ∀ z : Work.InnermostDisk.Disc, e z ∈ D :=
  exists_spanningDisc_of_convex_planar_rel σ hD hplane ⟨hmem, c.cont, c.periodic, hsimple⟩

end

end Work.Smooth.Schoenflies
