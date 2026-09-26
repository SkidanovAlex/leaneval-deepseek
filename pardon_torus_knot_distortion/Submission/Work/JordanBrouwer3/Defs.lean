import Mathlib
import Submission.Work.InnermostDisk.Defs

/-!
# `Work.JordanBrouwer3` — Jordan–Brouwer separation for an embedded `2`-sphere in `ℝ³`

This chapter is the *tameness-free* home of the theorem

> **`Work.Collar3D.SphereBoundsBall`.**  An embedded `2`-sphere `S ⊆ ℝ³`
> (`Work.InnermostDisk.IsEmbeddedSphere S`) is the frontier of a compact set `K` with nonempty
> interior.

and of the separation statement that the cut-and-paste of Pardon's theorem consumes
(`Work.Collar3D.separates_of_sphereBoundsBall`).  The chapter deliberately never uses
`Work.Topology.Classical.AlexanderSphereTheorem`: that proposition is *false as stated* (it claims a
ball homeomorphism for an **arbitrary** embedded sphere, which fails for the Alexander horned
sphere; see the README of this chapter).  Everything here is stated for
`Work.InnermostDisk.IsEmbeddedSphere`, i.e. for a continuous injective map of the round `2`-sphere,
with **no** local flatness hypothesis anywhere.

## The vocabulary of the chapter

* **`Work.JordanBrouwer3.SphereSides S`** — *the two sides of `S`*: two disjoint nonempty open sets
  `U, V` with union `Sᶜ`, `U` bounded, `S` bounded, and `frontier U = S = frontier V`.  This is
  Jordan–Brouwer separation in the form in which the collar chapter uses it: "which side is a point
  on".
* **`Work.JordanBrouwer3.SphereBoundsCompactAt S`** — the conclusion of
  `Work.Collar3D.SphereBoundsBall` at a single set `S`: there is a compact `K` with `S = frontier K`
  and `(interior K).Nonempty`.  (`Work.Collar3D.SphereBoundsBall` is the universally quantified
  form `∀ S, IsEmbeddedSphere S → SphereBoundsCompactAt S`.)
* **`Work.JordanBrouwer3.JordanBrouwerSphere`** — the chapter's single *residual*: every embedded
  sphere has two sides.  It is the classical Jordan–Brouwer separation theorem in `ℝ³`; the theorem
  is true for arbitrary topological embeddings (it is *not* the false ball statement), but its proof
  is not formalised in this workspace.  The chapter
  * proves everything else and isolates this one statement;
  * proves that it implies the `SphereBoundsBall` shape
    (`Work.JordanBrouwer3.sphereBoundsBall_of_jordanBrouwerSphere`) and decomposes it into two
    independent, clearly non-vacuous halves
    (`Work.JordanBrouwer3.SeparationSphere` — the complement is disconnected — and
    `Work.JordanBrouwer3.AccessibilitySphere` — every point of the sphere is in the closure of every
    side);
  * certifies it on the spheres that Pardon's double bubble actually uses (the box sphere and the
    two halves `Work.Step2.halfAbove`, `Work.Step2.halfBelow`, which are frontiers of convex
    bodies), so that the residual is *satisfied*, not merely satisfiable, in the application.

## Conventions

* `R3 = EuclideanSpace ℝ (Fin 3)`;
* `Sᶜ = ℝ³ ∖ S`; `frontier S` is the topological frontier;
* a *side* of `S` is a connected component of `Sᶜ`; the two sides of an embedded sphere are one
  bounded ("inside") and one unbounded ("outside").

## A note on dot notation

`R3 = WithLp 2 (Fin 3 → ℝ)` carries the topology *induced* from `Fin 3 → ℝ`, so `IsOpen s` for
`s : Set R3` is definitionally the existential form of `TopologicalSpace.induced`.  Dot notation
such as `h.isOpen_U.interior_eq` therefore does not resolve; use the explicit forms
`IsOpen.interior_eq h.isOpen_U`, or the accessors proved in `Sides.lean`.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.JordanBrouwer3

noncomputable section

/-! ## The two sides of an embedded sphere -/

/-- **The two sides of `S`.**  `U` is the bounded side and `V` the unbounded one; both are open and
nonempty, they are disjoint, they cover the complement of `S`, and each has frontier exactly `S`.
`S` itself is bounded (for an embedded sphere this is compactness of the round sphere).

With the connectedness clauses, `U` and `V` are *exactly* the two connected components of `Sᶜ`
(`SphereSides.component_eq_U_or_V`), which is the classical formulation of Jordan–Brouwer
separation. -/
structure SphereSides (S : Set R3) where
  /-- the bounded side of `S` -/
  U : Set R3
  /-- the unbounded side of `S` -/
  V : Set R3
  /-- the bounded side is open -/
  isOpen_U : IsOpen U
  /-- the unbounded side is open -/
  isOpen_V : IsOpen V
  /-- the two sides are disjoint -/
  disjoint : Disjoint U V
  /-- the two sides cover the complement of `S` -/
  cover : U ∪ V = Sᶜ
  /-- the bounded side is nonempty -/
  nonempty_U : U.Nonempty
  /-- the unbounded side is nonempty -/
  nonempty_V : V.Nonempty
  /-- the bounded side is bounded -/
  isBounded_U : Bornology.IsBounded U
  /-- `S` is bounded (compact) -/
  isBounded_S : Bornology.IsBounded S
  /-- the bounded side has frontier `S` -/
  frontier_U : frontier U = S
  /-- the unbounded side has frontier `S` -/
  frontier_V : frontier V = S
  /-- the bounded side is connected (it is a connected component of `Sᶜ`) -/
  isPreconnected_U : IsPreconnected U
  /-- the unbounded side is connected (it is a connected component of `Sᶜ`) -/
  isPreconnected_V : IsPreconnected V

namespace SphereSides

variable {S : Set R3} (h : SphereSides S)

/-- Membership in the union of the two sides. -/
theorem mem_union_iff {x : R3} : x ∈ h.U ∪ h.V ↔ x ∉ S := by
  rw [h.cover]; exact Iff.rfl

/-- A point off `S` lies on one of the two sides. -/
theorem mem_or_mem {x : R3} (hx : x ∉ S) : x ∈ h.U ∨ x ∈ h.V := by
  have : x ∈ h.U ∪ h.V := by rw [h.cover]; exact hx
  exact this

/-- The complement of the unbounded side is `S ∪ U`: the two sides cover the complement of `S`. -/
theorem compl_V_eq : h.Vᶜ = S ∪ h.U := by
  ext x
  constructor
  · intro hxV
    by_cases hxS : x ∈ S
    · exact Or.inl hxS
    · exact Or.inr ((h.mem_or_mem hxS).resolve_right hxV)
  · rintro (hxS | hxU)
    · intro hxV
      have hfr : x ∈ frontier h.V := by rw [h.frontier_V]; exact hxS
      have hcl : interior h.V = h.V := IsOpen.interior_eq h.isOpen_V
      rw [frontier, Set.mem_sdiff, hcl] at hfr
      exact hfr.2 hxV
    · exact fun hxV => Set.disjoint_left.mp h.disjoint hxU hxV

/-- Membership form of `compl_V_eq`. -/
theorem mem_compl_V_iff {x : R3} : x ∈ h.Vᶜ ↔ x ∈ S ∨ x ∈ h.U := by
  simp only [compl_V_eq, Set.mem_union]

/-- The complement of the unbounded side is bounded. -/
theorem isBounded_compl_V : Bornology.IsBounded h.Vᶜ := by
  rw [compl_V_eq]
  exact Bornology.IsBounded.union h.isBounded_S h.isBounded_U

/-- The complement of the unbounded side is compact. -/
theorem isCompact_compl_V : IsCompact h.Vᶜ :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_compl_iff.mpr h.isOpen_V, h.isBounded_compl_V⟩

/-- `S` is the frontier of the complement of the unbounded side: the `K` of
`SphereBoundsCompactAt`. -/
theorem frontier_compl_V : frontier h.Vᶜ = S := by
  rw [frontier_compl]; exact h.frontier_V

/-- The bounded side is contained in the complement of `S`. -/
theorem U_subset_compl : h.U ⊆ Sᶜ := by
  rw [← h.cover]; exact subset_union_left

/-- The unbounded side is contained in the complement of `S`. -/
theorem V_subset_compl : h.V ⊆ Sᶜ := by
  rw [← h.cover]; exact subset_union_right

/-- The bounded side is contained in the complement of the unbounded side. -/
theorem U_subset_compl_V : h.U ⊆ h.Vᶜ := by
  rw [compl_V_eq]; exact subset_union_right

/-- The interior of the compact `K = Vᶜ` is nonempty (it contains the bounded side). -/
theorem nonempty_interior_compl_V : (interior h.Vᶜ).Nonempty := by
  obtain ⟨x, hx⟩ := h.nonempty_U
  exact ⟨x, interior_maximal (U_subset_compl_V h) h.isOpen_U hx⟩

/-- **The two sides separate the connected sets of `Sᶜ`**: a preconnected subset of `Sᶜ` lies
entirely in one of them. -/
theorem subset_U_or_subset_V {C : Set R3} (hC : IsPreconnected C) (hCsub : C ⊆ Sᶜ) :
    C ⊆ h.U ∨ C ⊆ h.V :=
  IsPreconnected.subset_or_subset h.isOpen_U h.isOpen_V h.disjoint
    (by rw [h.cover]; exact hCsub) hC

/-- Every connected component of `Sᶜ` is one of the two sides. -/
theorem component_subset_U_or_V (x : R3) :
    connectedComponentIn Sᶜ x ⊆ h.U ∨ connectedComponentIn Sᶜ x ⊆ h.V :=
  h.subset_U_or_subset_V isPreconnected_connectedComponentIn (connectedComponentIn_subset Sᶜ x)

/-- **The connected component of a point of the bounded side is the bounded side.**  Together with
the same statement for `V`, this says that the two sides are exactly the two connected components of
`Sᶜ`, i.e. that `Sᶜ` has exactly two components. -/
theorem connectedComponentIn_eq_U {x : R3} (hx : x ∈ h.U) :
    connectedComponentIn Sᶜ x = h.U := by
  have hxcomp : x ∈ connectedComponentIn Sᶜ x := mem_connectedComponentIn (h.U_subset_compl hx)
  refine le_antisymm ?_ ?_
  · rcases h.component_subset_U_or_V x with hsub | hsub
    · exact hsub
    · exact absurd (hsub hxcomp) (fun hxV => Set.disjoint_left.mp h.disjoint hx hxV)
  · exact h.isPreconnected_U.subset_connectedComponentIn hx h.U_subset_compl

/-- **The connected component of a point of the unbounded side is the unbounded side.** -/
theorem connectedComponentIn_eq_V {x : R3} (hx : x ∈ h.V) :
    connectedComponentIn Sᶜ x = h.V := by
  have hxcomp : x ∈ connectedComponentIn Sᶜ x := mem_connectedComponentIn (h.V_subset_compl hx)
  refine le_antisymm ?_ ?_
  · rcases h.component_subset_U_or_V x with hsub | hsub
    · exact absurd (hsub hxcomp) (fun hxU => Set.disjoint_left.mp h.disjoint hxU hx)
    · exact hsub
  · exact h.isPreconnected_V.subset_connectedComponentIn hx h.V_subset_compl

/-- The two sides are distinct: `Sᶜ` has at least two components. -/
theorem U_ne_V : h.U ≠ h.V := by
  intro hUV
  obtain ⟨x, hx⟩ := h.nonempty_U
  exact Set.disjoint_left.mp h.disjoint hx (by rw [← hUV]; exact hx)

end SphereSides

/-! ## The conclusion of `Work.Collar3D.SphereBoundsBall` at one sphere -/

/-- **`Work.Collar3D.SphereBoundsBall` at a single set `S`**: `S` is the frontier of a compact set
with nonempty interior. -/
def SphereBoundsCompactAt (S : Set R3) : Prop :=
  ∃ K : Set R3, IsCompact K ∧ S = frontier K ∧ (interior K).Nonempty

/-- **The separation statement consumed by the cut-and-paste** at a single set `S`: a point of the
inside and a point of the outside of `S` cannot be joined by a preconnected set avoiding `S`. -/
def SeparatesAt (S : Set R3) : Prop :=
  ∃ K : Set R3, IsCompact K ∧ S = frontier K ∧ (interior K).Nonempty ∧
    ∃ x ∈ interior K, ∃ y : R3, y ∉ K ∧
      ∀ Z : Set R3, IsPreconnected Z → x ∈ Z → y ∈ Z → (Z ∩ S).Nonempty

/-! ## The residual: Jordan–Brouwer separation in `ℝ³` -/

/-- **Jordan–Brouwer separation for an embedded sphere.**  Every embedded `2`-sphere in `ℝ³` has
two sides in the sense of `SphereSides`.

This is the chapter's only residual statement.  It is the classical (true) Jordan–Brouwer
separation theorem for an arbitrary topological embedding of `S²` in `ℝ³`; unlike
`Work.Topology.Classical.AlexanderSphereTheorem` it asserts nothing about the inside being a ball,
so it is not contradicted by wild spheres.  It is decomposed into two halves in `Reduction.lean`,
and it is *proved* in the chapter for the spheres of Pardon's double bubble (`Certificates.lean`). -/
def JordanBrouwerSphere : Prop :=
  ∀ S : Set R3, Work.InnermostDisk.IsEmbeddedSphere S → Nonempty (SphereSides S)

/-- **The complement of an embedded sphere is disconnected.**  This is the "separation" half of
Jordan–Brouwer, isolated as its own proposition: there are two points of `Sᶜ` which no connected
subset of `Sᶜ` joins. -/
def SeparationSphere : Prop :=
  ∀ S : Set R3, Work.InnermostDisk.IsEmbeddedSphere S →
    ∃ x : R3, x ∉ S ∧ ∃ y : R3, y ∉ S ∧ y ∉ connectedComponentIn Sᶜ x

/-- **The complement has exactly two components, each with frontier `S`, one of them bounded.**
This is the classical wording of Jordan–Brouwer separation ("`ℝ³ ∖ S` has exactly two connected
components"), and it is equivalent to `JordanBrouwerSphere`
(`Work.JordanBrouwer3.jordanBrouwer_iff_twoComponents`). -/
def TwoComponentsAt (S : Set R3) : Prop :=
  ∃ x y : R3, x ∉ S ∧ y ∉ S ∧
    connectedComponentIn Sᶜ x ≠ connectedComponentIn Sᶜ y ∧
    (∀ z : R3, z ∉ S → connectedComponentIn Sᶜ z = connectedComponentIn Sᶜ x ∨
      connectedComponentIn Sᶜ z = connectedComponentIn Sᶜ y) ∧
    (Bornology.IsBounded (connectedComponentIn Sᶜ x) ∨
      Bornology.IsBounded (connectedComponentIn Sᶜ y)) ∧
    frontier (connectedComponentIn Sᶜ x) = S ∧ frontier (connectedComponentIn Sᶜ y) = S

/-- **`ℝ³ ∖ S` has exactly two connected components** for every embedded sphere `S`. -/
def TwoComponentsSphere : Prop :=
  ∀ S : Set R3, Work.InnermostDisk.IsEmbeddedSphere S → TwoComponentsAt S

/-- **At most two components**: of any three points off `S`, two lie in the same connected component
of `Sᶜ`.  (Together with `SeparationSphere` this says that the complement has exactly two
components.) -/
def AtMostTwoComponentsAt (S : Set R3) : Prop :=
  ∀ x y z : R3, x ∉ S → y ∉ S → z ∉ S →
    connectedComponentIn Sᶜ x = connectedComponentIn Sᶜ y ∨
    connectedComponentIn Sᶜ x = connectedComponentIn Sᶜ z ∨
    connectedComponentIn Sᶜ y = connectedComponentIn Sᶜ z

/-- `ℝ³ ∖ S` has at most two connected components, for every embedded sphere `S`. -/
def AtMostTwoSphere : Prop :=
  ∀ S : Set R3, Work.InnermostDisk.IsEmbeddedSphere S → AtMostTwoComponentsAt S

/-- **Every point of an embedded sphere is accessible from every side.**  The second half of
Jordan–Brouwer, isolated: for every point `p ∈ S` and every point `x` off `S`, the point `p` lies
in the closure of the connected component of `x` in `Sᶜ`.  (Equivalently: no point of `S` is
"one-sided"; together with `SeparationSphere` this identifies the components of `Sᶜ` and gives them
frontier `S`.) -/
def AccessibilitySphere : Prop :=
  ∀ S : Set R3, Work.InnermostDisk.IsEmbeddedSphere S →
    ∀ p ∈ S, ∀ x : R3, x ∉ S → p ∈ closure (connectedComponentIn Sᶜ x)

end

end Work.JordanBrouwer3
