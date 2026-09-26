import Mathlib
import Submission.Smooth
import Submission.Box
import Submission.Work.CoreTopology.All
import Submission.Work.InnermostDisk.All
import Submission.Work.SurgeryInvariance.All
import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.convex_PBox

/-!
# The planar innermost-disc chapter: vocabulary

This file sets up the objects of the *planar* innermost-disc / cut-and-paste chapter of Pardon's
proof, the chapter in which the ambient object is a plane slice of Pardon's box rather than a
sphere.

## The setting

`F = P.carrier` is the surface of a parametrised torus `P` (in the application the smoothly
embedded torus `ψ(F_standard)` of the challenge, `ψ : Submission.Diffeo`), and `D ⊆ ℝ³` is a
**convex planar region**: a convex set contained in a plane.  In the application

`D = PardonSlice s c σ u = PBox s c σ ∩ {y | y (σ 2) = c (σ 2) + u}`,

the slice of Pardon's box `Submission.PBox s c σ` by the cutting plane
`{y | y (σ 2) = c (σ 2) + u}` — the region by which the double-bubble core
`Work.BoxShrink.CruxCore` cuts the box.  Both `PBox s c σ` and the plane are convex, so `D` is
convex (`convex_PardonSlice`), and it lies in the cutting plane
(`isConvexPlanar_PardonSlice`).

## The main definitions

* `IsPlanar D` — `D` is contained in a plane, i.e. in a level set `{x | f x = a}` of a nonzero
  continuous linear functional;
* `IsConvexPlanar D` — `Convex ℝ D ∧ IsPlanar D`;
* `PardonSlice s c σ u` — the slice of Pardon's box by the cutting plane;
* `planeProj σ`, `planeLift σ h` — the coordinates `σ 0`, `σ 1` identify the plane
  `{y | y (σ 2) = h}` with `ℂ`: `planeProj` is the projection onto `ℂ`, `planeLift` its inverse on
  the plane.  This is the chart through which the *planar* Jordan–Schoenflies theorem of
  `Work.Smooth.Plane.Jordan` (stated in `ℂ`) is transported to the plane of `ℝ³` in which `D`
  lies.

## Conventions

* `R3 = LeanEval.KnotTheory.PardonDistortion.R3 = EuclideanSpace ℝ (Fin 3)`;
* `Disc = Work.InnermostDisk.Disc = Metric.closedBall (0 : ℂ) 1` is the model `2`-disc, with
  boundary circle `Work.CoreTopology.circlePoint`;
* a loop of `F` is a `Work.CoreTopology.ClosedCurve P`, `IsEssential` means "nonzero winding
  vector" and `IsSimple` means "injective on `[0, 2π)`".
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Plane

noncomputable section

/-- The closed unit interval `[0, 1]`: the parameter space of the arcs of `F ∩ D`, and one of the
two parameters of a homotopy. -/
abbrev ArcInterval : Type := Set.Icc (0 : ℝ) 1

/-! ## Planar and convex planar subsets of `ℝ³` -/

/-- **A planar subset of `ℝ³`**: a set contained in a plane, i.e. in a level set of a nonzero
continuous linear functional.  (The functional is the normal direction of the plane; the
condition `f ≠ 0` excludes the degenerate case in which the "level set" would be all of `ℝ³`.) -/
def IsPlanar (D : Set R3) : Prop :=
  ∃ (f : R3 →L[ℝ] ℝ) (_ : f ≠ 0) (a : ℝ), ∀ x ∈ D, f x = a

/-- **A convex planar region of `ℝ³`**: a convex set contained in a plane.  This is the ambient
object of the planar innermost-disc argument: it plays the role that the sphere `S` plays in
`Work.InnermostDisk`. -/
def IsConvexPlanar (D : Set R3) : Prop := Convex ℝ D ∧ IsPlanar D

theorem IsConvexPlanar.convex {D : Set R3} (h : IsConvexPlanar D) : Convex ℝ D := h.1

theorem IsConvexPlanar.planar {D : Set R3} (h : IsConvexPlanar D) : IsPlanar D := h.2

/-- A hyperplane `{x | f x = a}` of a nonzero functional is planar. -/
theorem isPlanar_hyperplane {f : R3 →L[ℝ] ℝ} (hf : f ≠ 0) (a : ℝ) : IsPlanar {x : R3 | f x = a} :=
  ⟨f, hf, a, fun _ hx => hx⟩

/-- The whole space is *not* a planar subset of `ℝ³`. -/
theorem not_isPlanar_univ : ¬ IsPlanar (Set.univ : Set R3) := by
  rintro ⟨f, hf, a, h⟩
  refine hf (ContinuousLinearMap.ext fun x => ?_)
  show f x = 0
  simpa [h x (Set.mem_univ x), h 0 (Set.mem_univ 0)] using map_zero f

/-- A subset of a planar set is planar. -/
theorem IsPlanar.mono {D E : Set R3} (hD : IsPlanar D) (hED : E ⊆ D) : IsPlanar E := by
  obtain ⟨f, hf, a, ha⟩ := hD
  exact ⟨f, hf, a, fun x hx => ha x (hED hx)⟩

/-- A *convex* subset of a convex planar region is convex planar (only the planarity is
inherited; convexity of the subset is a hypothesis). -/
theorem IsConvexPlanar.of_convex_subset {D E : Set R3} (hE : Convex ℝ E) (hD : IsConvexPlanar D)
    (hED : E ⊆ D) : IsConvexPlanar E :=
  ⟨hE, hD.2.mono hED⟩

/-- The intersection of two convex planar regions lying in a common plane is convex planar. -/
theorem IsConvexPlanar.inter {D E : Set R3} (hD : IsConvexPlanar D) (hE : IsConvexPlanar E) :
    IsConvexPlanar (D ∩ E) := by
  obtain ⟨f, hf, a, ha⟩ := hD.2
  exact ⟨hD.1.inter hE.1, f, hf, a, fun x hx => ha x hx.1⟩

/-! ## The slice of Pardon's box by the cutting plane -/

/-- **The planar slice of Pardon's box**: the box `Submission.PBox s c σ` cut by the plane
`{y | y (σ 2) = c (σ 2) + u}` — the plane region `D` by which the double-bubble core
`Work.BoxShrink.CruxCore` cuts the box. -/
def PardonSlice (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Submission.PBox s c σ ∩ {y : R3 | y (σ 2) = c (σ 2) + u}

theorem mem_PardonSlice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ PardonSlice s c σ u ↔ y ∈ Submission.PBox s c σ ∧ y (σ 2) = c (σ 2) + u := Iff.rfl

theorem PardonSlice_subset_PBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    PardonSlice s c σ u ⊆ Submission.PBox s c σ := inter_subset_left

theorem PardonSlice_subset_plane (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    PardonSlice s c σ u ⊆ {y : R3 | y (σ 2) = c (σ 2) + u} := inter_subset_right

/-- The cutting plane `{y | y (σ 2) = c (σ 2) + u}` is planar. -/
theorem isPlanar_cuttingPlane (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    IsPlanar {y : R3 | y (σ 2) = c (σ 2) + u} := by
  refine ⟨EuclideanSpace.proj (σ 2), ?_, c (σ 2) + u, fun y hy => ?_⟩
  · intro hf
    have h := congrArg (fun (g : R3 →L[ℝ] ℝ) => g (EuclideanSpace.single (σ 2) (1 : ℝ))) hf
    rw [PiLp.proj_apply] at h
    simp [EuclideanSpace.single] at h
  · simpa using hy

/-- **The slice of Pardon's box is convex**: it is the intersection of the box `PBox s c σ`, which
is convex, with the cutting plane. -/
theorem convex_PardonSlice (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Convex ℝ (PardonSlice s c σ u) := by
  refine (Work.Topology.SphereSlicing.convex_PBox s c σ).inter ?_
  intro x hx y hy a b ha hb hab
  have hx' : x (σ 2) = c (σ 2) + u := hx
  have hy' : y (σ 2) = c (σ 2) + u := hy
  show (a • x + b • y) (σ 2) = c (σ 2) + u
  have : (a • x + b • y) (σ 2) = a * x (σ 2) + b * y (σ 2) := rfl
  rw [this, hx', hy', ← add_mul, hab, one_mul]

/-- **The slice of Pardon's box is a convex planar region.** -/
theorem isConvexPlanar_PardonSlice (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    IsConvexPlanar (PardonSlice s c σ u) :=
  ⟨convex_PardonSlice s c σ u, (isPlanar_cuttingPlane c σ u).mono (PardonSlice_subset_plane s c σ u)⟩

/-- **The decomposition of Pardon's box by the cutting plane**: the box is the union of its two
open halves cut out by the plane `{y | y (σ 2) = c (σ 2) + u}` and of the closed slice
`PardonSlice s c σ u` in the plane.

This is the set-theoretic content of the decomposition
`F ∩ PBox s c σ = F ∩ H₊ ∪ F ∩ H₋ ∪ (F ∩ D)` used by the double-bubble core
`Work.BoxShrink.CruxCore`: intersecting both sides with `F` gives that decomposition. -/
theorem PBox_eq_halves_union_slice (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Submission.PBox s c σ =
      {y : R3 | y ∈ Submission.PBox s c σ ∧ y (σ 2) < c (σ 2) + u} ∪
      {y : R3 | y ∈ Submission.PBox s c σ ∧ c (σ 2) + u < y (σ 2)} ∪
      PardonSlice s c σ u := by
  ext y
  simp only [mem_PardonSlice, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro hy
    rcases lt_trichotomy (y (σ 2)) (c (σ 2) + u) with h | h | h
    · exact Or.inl (Or.inl ⟨hy, h⟩)
    · exact Or.inr ⟨hy, h⟩
    · exact Or.inl (Or.inr ⟨hy, h⟩)
  · rintro ((⟨hy, _⟩ | ⟨hy, _⟩) | ⟨hy, _⟩) <;> exact hy

/-! ## The plane `{y | y (σ 2) = h}` as `ℂ` -/

/-- **The projection of `ℝ³` onto `ℂ` along the coordinates `σ 0` and `σ 1`.**  On the plane
`{y | y (σ 2) = h}` the map `planeProj σ` is a bijection onto `ℂ`, with inverse `planeLift σ h`. -/
def planeProj (σ : Equiv.Perm (Fin 3)) (y : R3) : ℂ := ⟨y (σ 0), y (σ 1)⟩

@[simp] theorem planeProj_re (σ : Equiv.Perm (Fin 3)) (y : R3) : (planeProj σ y).re = y (σ 0) := rfl

@[simp] theorem planeProj_im (σ : Equiv.Perm (Fin 3)) (y : R3) : (planeProj σ y).im = y (σ 1) := rfl

/-- The underlying real-linear map of `planeProj σ`. -/
def planeProjL (σ : Equiv.Perm (Fin 3)) : R3 →ₗ[ℝ] ℂ where
  toFun := planeProj σ
  map_add' := by
    intro x y
    apply Complex.ext <;> simp [planeProj]
  map_smul' := by
    intro a x
    apply Complex.ext <;> simp [planeProj]

theorem planeProjL_apply (σ : Equiv.Perm (Fin 3)) (y : R3) :
    planeProjL σ y = planeProj σ y := rfl

/-- **The point of the plane `{y | y (σ 2) = h}` with `ℂ`-coordinates `z`.** -/
def planeLift (σ : Equiv.Perm (Fin 3)) (h : ℝ) (z : ℂ) : R3 :=
  WithLp.toLp 2 fun i : Fin 3 => if i = σ 0 then z.re else if i = σ 1 then z.im else h

@[simp] theorem planeLift_apply_zero (σ : Equiv.Perm (Fin 3)) (h : ℝ) (z : ℂ) :
    planeLift σ h z (σ 0) = z.re := by
  simp [planeLift]

@[simp] theorem planeLift_apply_one (σ : Equiv.Perm (Fin 3)) (h : ℝ) (z : ℂ) :
    planeLift σ h z (σ 1) = z.im := by
  have h0 : σ 1 ≠ σ 0 := fun hc => by
    have := congrArg Fin.val (σ.injective hc); simp at this
  simp [planeLift, h0]

@[simp] theorem planeLift_apply_two (σ : Equiv.Perm (Fin 3)) (h : ℝ) (z : ℂ) :
    planeLift σ h z (σ 2) = h := by
  have h0 : σ 2 ≠ σ 0 := fun hc => by
    have := congrArg Fin.val (σ.injective hc); simp at this
  have h1 : σ 2 ≠ σ 1 := fun hc => by
    have := congrArg Fin.val (σ.injective hc); simp at this
  simp [planeLift, h0, h1]

@[simp] theorem planeProj_planeLift (σ : Equiv.Perm (Fin 3)) (h : ℝ) (z : ℂ) :
    planeProj σ (planeLift σ h z) = z := by
  apply Complex.ext <;> simp [planeProj]

theorem planeLift_planeProj (σ : Equiv.Perm (Fin 3)) {h : ℝ} {y : R3} (hy : y (σ 2) = h) :
    planeLift σ h (planeProj σ y) = y := by
  have hh : (planeLift σ h (planeProj σ y)).ofLp = y.ofLp := by
    funext i
    obtain ⟨j, rfl⟩ := σ.surjective i
    fin_cases j
    · simp [planeLift, planeProj]
    · simp [planeLift, planeProj]
    · simpa [planeLift] using hy.symm
  calc planeLift σ h (planeProj σ y)
      = WithLp.toLp 2 (planeLift σ h (planeProj σ y)).ofLp := (WithLp.toLp_ofLp 2 _).symm
    _ = WithLp.toLp 2 y.ofLp := by rw [hh]
    _ = y := WithLp.toLp_ofLp 2 y

theorem planeLift_injective (σ : Equiv.Perm (Fin 3)) (h : ℝ) : Function.Injective (planeLift σ h) :=
  fun z z' hzz' => by
    have := congrArg (planeProj σ) hzz'
    simpa using this

/-- **A simple closed curve in a subset `D ⊆ ℝ³`**: a continuous `2π`-periodic map, injective on
one period `[0, 2π)`, whose image lies in `D`.  This is the shape of curve for which the planar
separation theorems are stated. -/
def IsSimpleClosedCurveIn (D : Set R3) (c : ℝ → R3) : Prop :=
  (∀ t : ℝ, c t ∈ D) ∧ Continuous c ∧ Function.Periodic c (2 * Real.pi) ∧
    Set.InjOn c (Set.Ico 0 (2 * Real.pi))

/-- Every point of the closed unit disc lying on the unit circle is `circlePoint θ` for some `θ`. -/
theorem exists_circlePoint_eq_of_norm_eq_one {z : Work.InnermostDisk.Disc}
    (hz : ‖(z : ℂ)‖ = 1) : ∃ θ : ℝ, Work.CoreTopology.circlePoint θ = z := by
  refine ⟨Complex.arg (z : ℂ), Subtype.ext ?_⟩
  rw [Work.CoreTopology.circlePoint_coe]
  have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [hz] at h
  simpa using h

theorem continuous_planeProj (σ : Equiv.Perm (Fin 3)) : Continuous (planeProj σ) := by
  have h : planeProj σ = fun y : R3 => (y (σ 0) : ℂ) + (y (σ 1) : ℂ) * Complex.I := by
    funext y; apply Complex.ext <;> simp [planeProj]
  rw [h]
  fun_prop

theorem continuous_planeLift (σ : Equiv.Perm (Fin 3)) (h : ℝ) : Continuous (planeLift σ h) := by
  have hg : Continuous (fun z : ℂ => fun i : Fin 3 =>
      if i = σ 0 then z.re else if i = σ 1 then z.im else h) := by
    refine continuous_pi fun i => ?_
    by_cases hi0 : i = σ 0
    · subst hi0; simp only [if_true]; exact Complex.continuous_re
    · by_cases hi1 : i = σ 1
      · subst hi1; simp only [hi0, if_false, if_true]; exact Complex.continuous_im
      · simp only [hi0, hi1, if_false]; exact continuous_const
  exact Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)) hg

theorem planeProj_image_convex (σ : Equiv.Perm (Fin 3)) {D : Set R3} (hD : Convex ℝ D) :
    Convex ℝ (planeProj σ '' D) :=
  hD.linear_image (planeProjL σ)

/-- **Membership in the lift of a planar set.**  If `D` is contained in the plane
`{y | y (σ 2) = h}`, then `planeLift σ h z ∈ D` exactly when `z` is the projection of a point of
`D`. -/
theorem planeLift_mem_iff (σ : Equiv.Perm (Fin 3)) {D : Set R3} {h : ℝ}
    (hD : ∀ y ∈ D, y (σ 2) = h) (z : ℂ) :
    planeLift σ h z ∈ D ↔ z ∈ planeProj σ '' D := by
  constructor
  · intro hz
    exact ⟨planeLift σ h z, hz, planeProj_planeLift σ h z⟩
  · rintro ⟨y, hy, rfl⟩
    rw [planeLift_planeProj σ (hD y hy)]
    exact hy

/-- **The projection is injective on a plane.** -/
theorem planeProj_injOn (σ : Equiv.Perm (Fin 3)) {h : ℝ} :
    Set.InjOn (planeProj σ) {y : R3 | y (σ 2) = h} := by
  intro y hy y' hy' hproj
  rw [← planeLift_planeProj σ (h := h) hy, ← planeLift_planeProj σ (h := h) hy', hproj]

end

end Work.Smooth.Plane
