import Submission.Work.PlaneSlice.PlaneTopology
import Submission.Work.InnermostDisk.All

/-!
# The planar slice of a convex region of a coordinate plane: rings and arcs

The workspace's `Work.Smooth.Plane.PlaneSliceData` / `Work.Smooth.Plane.PlaneSlicing` describe the
slicing of a convex planar region `D` by the surface `F` in terms of *closed* arcs inside `D`.
That is the right notion for a region which contains its boundary (a sphere, or a plane), but it
does not cover the region produced by Pardon's box: `Work.BoxShrink.Core.cutDisc s c σ u =
Submission.PBox s c σ ∩ {y | y (σ 2) = c (σ 2) + u}` is cut out by the **open** box, so the circles
of `F ∩ {plane}` that cross the boundary of the box meet `D` in *open* arcs, whose endpoints lie on
the boundary of `D` and are not themselves points of `D`.  Since the family of arcs of a
`PlaneSlicing` is finite and the arcs lie in `D`, such a crossing can never be described by a
`PlaneSlicing` (see `Submission/Work/PlaneSlice/README.md` for the argument, and
`Work.PlaneSlice.transversePlane_closed` for the formal shadow of it).

For Pardon's *first* innermost argument, however, the arcs are irrelevant: an arc is contractible,
so a loop of `F` lying in an arc is inessential.  What the argument really needs is

* the circles of `F` that lie wholly inside `D` (the *rings*), each with the disc it bounds inside
  `D`, nested;
* the fact that every **essential** loop of `F` inside `D` lies on one of those rings
  (`covers_essential`);
* the disc interiors meeting `F` only along the rings (`covers_interior`).

The structure `SliceRings` records exactly this, and
`Work.PlaneSlice.innermostDiscInput_of_sliceRings` derives Pardon's first innermost step
(`Work.InnermostDisk.InnermostDiscInput`) from it.  The construction of a `SliceRings` from the
classification of a plane level set is in `Submission/Work/PlaneSlice/SliceConstruction.lean`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PlaneSlice

noncomputable section

/-- **The rings of the slice of a convex plane region `D` by the surface `F = ψ(standard torus)`.**

The closed curves `c i` are the circles of `F ∩ Π` (the plane containing `D`) which lie wholly
inside `D`; `disc i` is the Jordan disc of `c i` inside `D`; the family is nested (`rank`, `inside`,
`inside_subset`); the interior of a disc meets `F` only along the rings (`covers_interior`); and
every *essential* loop of `F` inside `D` lies on one of the rings (`covers_essential`) — the loops
of `D` that lie in the arcs (the pieces of the circles that cross the boundary of `D`) are
inessential and are therefore not seen by the essential-loop structure. -/
structure SliceRings (ψ : Submission.Diffeo) (D : Set R3) where
  /-- the index type of the rings -/
  ι : Type
  /-- finitely many rings -/
  fintype : Fintype ι
  /-- the rings -/
  c : ι → Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)
  /-- each ring is an embedded loop -/
  simple : ∀ i : ι, Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) (c i)
  /-- distinct rings are disjoint -/
  disjoint : Pairwise fun i j : ι => Disjoint (Set.range (c i).γ) (Set.range (c j).γ)
  /-- the rings lie in `D` -/
  mem : ∀ i : ι, ∀ t : ℝ, (c i).γ t ∈ D
  /-- the disc inside `D` bounded by a ring -/
  disc : ι → C(Work.InnermostDisk.Disc, R3)
  /-- the disc is embedded -/
  disc_inj : ∀ i : ι, Function.Injective (disc i)
  /-- its boundary is the ring -/
  disc_boundary : ∀ i : ι, ∀ θ : ℝ,
    disc i (Work.CoreTopology.circlePoint θ) = (c i).γ θ
  /-- the disc lies in `D` -/
  disc_mem : ∀ i : ι, ∀ z : Work.InnermostDisk.Disc, disc i z ∈ D
  /-- the interior of a disc meets `F` only along the rings -/
  covers_interior : ∀ i : ι, ∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 →
    disc i z ∈ (Work.Smooth.Morse.torus ψ).carrier → ∃ j : ι, disc i z ∈ Set.range (c j).γ
  /-- **the essential loops of `D` lie on the rings**: an essential loop of `F` whose image lies in
  `D` lies on one of the rings (the loops lying in the arcs are inessential) -/
  covers_essential : ∀ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
    Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) γ → (∀ t : ℝ, γ.γ t ∈ D) →
      ∃ i : ι, Set.range γ.γ ⊆ Set.range (c i).γ
  /-- a ring meeting the interior of the disc of another is contained in it -/
  inside_subset : ∀ i j : ι, (∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
      disc i z ∈ Set.range (c j).γ) → Set.range (c j).γ ⊆ Set.range (disc i)
  /-- the nesting rank of the rings -/
  rank : ι → ℕ
  /-- a ring meeting the interior of the disc of another has smaller rank -/
  inside : ∀ i j : ι, (∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
      disc i z ∈ Set.range (c j).γ) → rank j < rank i

attribute [instance] SliceRings.fintype

/-- **Pardon's first innermost step from the rings of a plane slice.**

If `D` carries a `SliceRings` datum, then every essential loop of `F` inside `D` bounds — through
the ring of minimal rank among the essential ones — an innermost disc: Pardon's datum
`Work.InnermostDisk.InnermostDisc P D`.  Hence `Work.InnermostDisk.InnermostDiscInput P D`.

This mirrors `Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing` and
`Work.Smooth.Plane.Slicing.innermostDiscInput_of_slicing`: an essential loop lies on a ring
(`covers_essential`), the rings are nested and finitely many, so some essential ring is of minimal
rank, and the curves of `F` in the interior of its disc are then inessential by minimality. -/
theorem innermostDiscInput_of_sliceRings {ψ : Submission.Diffeo} {D : Set R3}
    (h : SliceRings ψ D) : Work.InnermostDisk.InnermostDiscInput (Work.Smooth.Morse.torus ψ) D := by
  classical
  intro hD
  obtain ⟨γ, hγess, hγD⟩ := hD
  obtain ⟨i₀, hi₀⟩ := h.covers_essential γ hγess hγD
  have hess₀ : Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) (h.c i₀) := by
    by_contra hne
    exact absurd hγess
      (Work.InnermostDisk.not_isEssential_of_range_subset_isSimple (h.simple i₀) hi₀ hne)
  obtain ⟨i, hi_mem, hmin⟩ :=
    Finset.exists_min_image
      (Finset.univ.filter fun i : h.ι =>
        Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) (h.c i))
      h.rank ⟨i₀, by simp [hess₀]⟩
  have hi_ess : Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) (h.c i) := by
    simpa using hi_mem
  have hmin' : ∀ j : h.ι, Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) (h.c j) →
      ¬ h.rank j < h.rank i := fun j hj hlt =>
    absurd (hmin j (by simp [hj])) (not_le.mpr hlt)
  exact ⟨{
    α := h.c i
    simple := h.simple i
    essential := hi_ess
    mem := h.mem i
    e := h.disc i
    inj := h.disc_inj i
    boundary := h.disc_boundary i
    e_mem := h.disc_mem i
    ι := {j : h.ι // ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
      h.disc i z ∈ Set.range (h.c j).γ}
    fintype := by classical infer_instance
    curves := fun j => h.c j.1
    curves_simple := fun j => h.simple j.1
    curves_inessential := fun j => by
      by_contra hne
      exact hmin' j.1 hne (h.inside i j.1 j.2)
    curves_disjoint := fun j j' hne => h.disjoint fun hval => hne (Subtype.ext hval)
    curves_subset := fun j => h.inside_subset i j.1 j.2
    covers := fun z hz hc => by
      obtain ⟨j, hj⟩ := h.covers_interior i z hz hc
      exact ⟨⟨j, z, hz, hj⟩, hj⟩ }⟩

end

end Work.PlaneSlice
