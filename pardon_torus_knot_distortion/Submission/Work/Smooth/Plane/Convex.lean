import Mathlib
import Submission.Work.Smooth.Plane.Jordan

/-!
# The convexity form of planar Jordan–Schoenflies

This file proves the form of the planar Jordan–Schoenflies theorem which Pardon's planar
innermost argument needs: **a simple closed curve contained in a convex planar region `D` bounds an
embedded disc contained in `D`**.

The proof is remarkably cheap, and does not need the winding-number/degree machinery which the
general planar separation theory would use (the *alternative* route through that machinery — the
statement that a convex set is simply connected, in the degree form `Λ (2π) = Λ 0` for any lift of
the normalised loop — is recorded in
`Work.Smooth.Plane.Convex.lift_eq_of_notMem_convex`).  Jordan–Schoenflies supplies an embedded disc `e`
spanning the curve; the classical Jordan curve theorem (in the homotopy form recorded by
`Work.Smooth.Plane.PlaneJordanData.inside_not_nullHomotopic`) says that a point of the *interior* of
that disc cannot be contracted away from the curve.  But if such a point `x` were outside the
convex set `D`, then the curve — whose trace lies in `D` — could be contracted inside `D` to a
point of `D`, through loops avoiding `x`: convexity alone gives the straight-line homotopy

`H (s, t) = (1 - s) • c (2π t) + s • c 0`,

which stays in `D`, hence avoids `x ∉ D`.  So no interior point of the disc lies outside `D`, and
the boundary of the disc is the curve itself, which lies in `D`: the whole disc is contained in
`D`.

## Main results

* `nullHomotopicAvoiding_of_convex` — the straight-line homotopy: a loop with trace in a convex set
  `D` is null-homotopic in the complement of any point outside `D` (no separation theorem is
  needed);
* `PlaneJordanData.e_mem_of_convex` — the convexity form for a `PlaneJordanData` in `ℂ`: the whole
  spanning disc lies in `D`;
* `exists_spanningDisc_of_convex_planar` — the same statement in `ℝ³`, for a convex subset `D` of a
  coordinate plane `{y | y (σ 2) = h}`, in terms of `Work.Smooth.Plane.IsSimpleClosedCurveIn`;
* `exists_spanningDisc_of_closedCurve` — the `Work.CoreTopology.ClosedCurve` form, which supplies
  the `disc` field of a planar slicing datum.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Plane

noncomputable section

/-! ## The straight-line homotopy in a convex set -/

/-- **A loop with trace in a convex set is null-homotopic away from any point outside it.**

If `D ⊆ ℂ` is convex, `x ∉ D` and the continuous loop `c` has its trace in `D`, then `c` is
null-homotopic in `ℂ ∖ {x}`: the straight-line homotopy `H (s,t) = (1-s) • c (2π t) + s • c 0`
stays in the convex set `D` (whose points are all different from `x`) and contracts the loop to the
constant loop at `c 0`.

(No separation theorem is needed: convexity alone gives the homotopy.  This is the planar analogue
of the fact that a convex set is "simply connected".) -/
theorem nullHomotopicAvoiding_of_convex {D : Set ℂ} (hD : Convex ℝ D) {x : ℂ} (hx : x ∉ D)
    {c : ℝ → ℂ} (hc : Continuous c) (hmem : ∀ t : ℝ, c t ∈ D) : NullHomotopicAvoiding c x := by
  have haux : ∀ p : ArcInterval × ArcInterval,
      (1 - (p.1 : ℝ)) • c (2 * Real.pi * (p.2 : ℝ)) + (p.1 : ℝ) • c 0 ∈ D := by
    intro p
    refine hD (hmem _) (hmem 0) ?_ ?_ ?_
    · exact sub_nonneg.mpr p.1.2.2
    · exact p.1.2.1
    · ring
  refine ⟨⟨fun p : ArcInterval × ArcInterval =>
      (1 - (p.1 : ℝ)) • c (2 * Real.pi * (p.2 : ℝ)) + (p.1 : ℝ) • c 0, ?_⟩,
    fun p hpx => hx (hpx ▸ haux p), ?_, ?_⟩
  · fun_prop
  · intro t
    simp
  · intro t
    simp

/-! ## The convexity form in `ℂ` -/

/-- **Planar Jordan–Schoenflies, convexity form, in `ℂ`.**

Let `c` be a simple closed plane curve with trace in a convex set `D ⊆ ℂ`, and let
`h : PlaneJordanData c` be the classical Jordan datum for it (a spanning embedded disc `h.e`
together with the fact that its interior points cannot be contracted away from the curve).  Then
the whole disc lies in `D`.

Indeed, if an interior point `z` of the disc were outside `D`, the straight-line homotopy of
`nullHomotopicAvoiding_of_convex` would contract `c` away from `h.e z`, contradicting
`h.inside_not_nullHomotopic`; and the boundary of the disc is the curve, which lies in `D` by
hypothesis. -/
theorem PlaneJordanData.e_mem_of_convex {c : ℝ → ℂ} (h : PlaneJordanData c) {D : Set ℂ}
    (hD : Convex ℝ D) (hc : Continuous c) (hmem : ∀ t : ℝ, c t ∈ D)
    (z : Work.InnermostDisk.Disc) : h.e z ∈ D := by
  rcases lt_or_eq_of_le (by simpa using Metric.mem_closedBall.mp z.2 : ‖(z : ℂ)‖ ≤ 1) with hz | hz
  · by_contra hxD
    exact h.inside_not_nullHomotopic z hz (nullHomotopicAvoiding_of_convex hD hxD hc hmem)
  · obtain ⟨θ, hθ⟩ := exists_circlePoint_eq_of_norm_eq_one hz
    rw [← hθ, h.boundary θ]
    exact hmem θ

/-! ## The convexity form in `ℝ³` -/

/-- **Planar Jordan–Schoenflies, convexity form, in `ℝ³`.**

Let `D ⊆ ℝ³` be a convex subset of the coordinate plane `{y | y (σ 2) = h}` and let `c` be a simple
closed curve lying in `D` (in the sense of `IsSimpleClosedCurveIn`).  Then `c` bounds an embedded
disc whose image is contained in `D`.

This is the *convexity form of planar Jordan–Schoenflies*: the classical input `PlaneJordanInput`
(for the projected curve only), combined with `PlaneJordanData.e_mem_of_convex`, the fact that
`planeProj σ` is a bijection from the plane `{y (σ 2) = h}` onto `ℂ` with inverse `planeLift σ h`,
and the convexity of `planeProj σ '' D`. -/
theorem exists_spanningDisc_of_convex_planar (hinput : PlaneJordanInput)
    (σ : Equiv.Perm (Fin 3)) {h : ℝ} {D : Set R3} (hD : Convex ℝ D)
    (hplane : ∀ y ∈ D, y (σ 2) = h) {c : ℝ → R3} (hc : IsSimpleClosedCurveIn D c) :
    ∃ e : C(Work.InnermostDisk.Disc, R3), Function.Injective e ∧
      (∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) = c θ) ∧
      ∀ z : Work.InnermostDisk.Disc, e z ∈ D := by
  have hγcont : Continuous fun t : ℝ => planeProj σ (c t) :=
    (continuous_planeProj σ).comp hc.2.1
  have hγper : Function.Periodic (fun t : ℝ => planeProj σ (c t)) (2 * Real.pi) := by
    intro t
    show planeProj σ (c (t + 2 * Real.pi)) = planeProj σ (c t)
    rw [hc.2.2.1 t]
  have hγinj : Set.InjOn (fun t : ℝ => planeProj σ (c t)) (Set.Ico 0 (2 * Real.pi)) := by
    intro t ht s hs heq
    exact hc.2.2.2 ht hs (planeProj_injOn σ (hplane (c t) (hc.1 t)) (hplane (c s) (hc.1 s)) heq)
  obtain ⟨hJ⟩ := hinput (fun t : ℝ => planeProj σ (c t)) hγcont hγper hγinj
  have hD'conv : Convex ℝ (planeProj σ '' D) := planeProj_image_convex σ hD
  have hmem' : ∀ t : ℝ, planeProj σ (c t) ∈ planeProj σ '' D :=
    fun t => ⟨c t, hc.1 t, rfl⟩
  have key : ∀ z : Work.InnermostDisk.Disc, hJ.e z ∈ planeProj σ '' D :=
    fun z => hJ.e_mem_of_convex hD'conv hγcont hmem' z
  refine ⟨⟨fun z => planeLift σ h (hJ.e z), (continuous_planeLift σ h).comp hJ.e.continuous⟩,
    fun z z' hzz' => hJ.inj (planeLift_injective σ h hzz'), ?_, ?_⟩
  · intro θ
    have h1 : hJ.e (Work.CoreTopology.circlePoint θ) = planeProj σ (c θ) := hJ.boundary θ
    show planeLift σ h (hJ.e (Work.CoreTopology.circlePoint θ)) = c θ
    rw [h1, planeLift_planeProj σ (hplane (c θ) (hc.1 θ))]
  · intro z
    obtain ⟨y, hyD, hyz⟩ := key z
    show planeLift σ h (hJ.e z) ∈ D
    rw [← hyz, planeLift_planeProj σ (hplane y hyD)]
    exact hyD

/-- **The convexity form in the vocabulary of `Work.CoreTopology.ClosedCurve`.**

A *simple* closed curve of a parametrised torus (in the sense of `Work.CoreTopology.IsSimple`)
whose image lies in a convex subset `D` of a coordinate plane bounds an embedded disc contained in
`D`.  This is the form of `exists_spanningDisc_of_convex_planar` which supplies the `disc` field of
a planar slicing datum `Work.Smooth.Plane.PlaneSliceData`. -/
theorem exists_spanningDisc_of_closedCurve (hinput : PlaneJordanInput) (σ : Equiv.Perm (Fin 3))
    {h : ℝ} {D : Set R3} (hD : Convex ℝ D) (hplane : ∀ y ∈ D, y (σ 2) = h)
    {P : Work.CoreTopology.ParamTorus} {c : Work.CoreTopology.ClosedCurve P}
    (hsimple : Work.CoreTopology.IsSimple P c) (hmem : ∀ t : ℝ, c.γ t ∈ D) :
    ∃ e : C(Work.InnermostDisk.Disc, R3), Function.Injective e ∧
      (∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) = c.γ θ) ∧
      ∀ z : Work.InnermostDisk.Disc, e z ∈ D :=
  exists_spanningDisc_of_convex_planar hinput σ hD hplane ⟨hmem, c.cont, c.periodic, hsimple⟩

end

end Work.Smooth.Plane
