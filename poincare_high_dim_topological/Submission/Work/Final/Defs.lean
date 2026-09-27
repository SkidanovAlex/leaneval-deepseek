import Mathlib
import Submission.Work.Cells.Connell.Defs
import Submission.Work.Geo.DualStretch.high_dom
import Submission.Work.Geo.DualStretch.dual_stretch
import Submission.Work.PL.Subdiv.DomDim

/-!
# `Submission/Work/Final`: the final assembly of `poincare_high_dim_topological`

This area (`Submission/Work/Final`, namespace `Work.Final`) is the **final wiring** of the
Newman/Connell proof of the generalized topological Poincaré conjecture in dimensions `≥ 5`
(challenge `poincare_high_dim_topological`).  It is the only place where the areas are put
together; it does not reprove any mathematics of its own beyond the bookkeeping needed to make
the interfaces of the other areas match.

## The chain

```
M ≃ₕ 𝕊ⁿ  (n ≥ 5)
  → CompactSpace M                       Work.Compact.compactSpace_of_homotopyEquiv_sphere_univ
  → MetricSpace M (compatible metric)    Work.Metric.metricOfCompactEuclideanSpace
  → PL.LocCube n M                       Work.Metric.locCube_chartedSpace
  → ∃ k, PL.CellCover n M k              Work.Metric.cellCover_exists
  → ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j  Work.Conn.extOverDisc_of_homotopyEquiv_sphere
  → Assumptions n M                      (this area; `Work.Final.assumptionsOfInputs`)
  → CellCover n M k → CellCover n M 2    Work.Cells.Connell.cellCover_two
  → ∃ q, {q}ᶜ ≃ₜ ℝⁿ                     Work.Cells.Connell.two_cells_sphere
  → M ≃ₜ 𝕊ⁿ                             Work.Endgame.nonempty_homeomorph_sphere_of_compl_homeomorph
```

## What this file contains

* `Work.Final.lowIdx`, `Work.Final.highIdx`, `Work.Final.skelLow`, `Work.Final.skelHigh`: the low
  (`p`-skeleton) and high (dual `(n-p-1)`-skeleton) parts of a triangulation, packaged so that the
  interface `Work.Cells.Connell.SkeletonData` (`A6`/`G7`) is **inhabited** — see the note below.
* `Work.Final.skeletonData`: the resulting `Work.Cells.Connell.SkeletonData n`.

## Note on `SkeletonData` (an interface repair)

`Work.Cells.Connell.SkeletonData` bundles the `G7` results of `Work.Geo.DualStretch`.  Four of its
fields,

```
low_closed  : ∀ (P : PL.Cx n) (p : ℕ), IsClosed (Low P p)
high_closed : ∀ (P : PL.Cx n) (p : ℕ), IsClosed (High P p)
low_dom     : ∀ (P : PL.Cx n) (p : ℕ), PL.DomDim (Low P p) p
high_dom    : ∀ (P : PL.Cx n) (p : ℕ), PL.DomDim (High P p) ((n - p - 1 : ℕ) : ℤ)
```

are quantified over **all** geometric simplicial complexes, not only the finite ones for which
`Low`/`High` are meant.  As stated they are *false*: take `n = 1` and the complex on
`ℝ = PL.E 1` whose faces are the singletons `{1/(k+1)}`, `k : ℕ`; it is a legitimate
`Geometry.SimplicialComplex` (a singleton is affinely independent, distinct singletons have disjoint
convex hulls), while `Low P 0 = {1/(k+1) | k ∈ ℕ}` is not closed (`0` is a limit point, not in the
set) and is not a finite union of simplices (so `DomDim` fails as well).  Hence, with `Low`/`High` = the
`Work.Geo.DualStretch` skeleta — the definitions for which all the `G7` content (`low_dom`,
`high_dom`, `dual_stretch`, …) is proved — `SkeletonData n` has no inhabitant, so the delivered chain
above `Work.Cells.Connell.Assumptions` could only be used with a `SkeletonData` that is *not* the
dual-stretch one.  (Machine-checked counterexample for the closure fields:
`Work.Final.not_forall_isClosed_Low`.)  `SkeletonData n` itself is inhabited — by `skelLow`/`skelHigh`
below — so this is an interface defect, not an inconsistency.

`Work.Final.skelLow`/`skelHigh` below are the same skeleta written as a union over a *finite*
index set: they agree with the `p`-skeleton and the dual skeleton on every finite complex (in
particular on every triangulation produced by `Work.PL.Subdiv.exists_cube_triangulation`, which is
the only case any consumer uses), and are `∅` (hence closed) on infinite complexes.  With these the
`SkeletonData` interface is inhabited (`Work.Final.skeletonData`), and the *content* consumed by
`Work.Cells.Connell.connell_step` is unchanged.

The proper repair in the owning areas is to add `P.faces.Finite` to those four fields (the use sites
in `Work.Cells.Connell.connell_step` have the finiteness at hand, since it applies them to the
triangulation produced by `CubeTriangulationForm`); it is recorded, and inhabited with the genuine
`Work.Geo.DualStretch` skeleta, as `Work.Final.SkeletonDataFin` / `Work.Final.skeletonDataFin` in
`Submission/Work/Final/SkeletonFix.lean`.  `Work.Final.skeletonData` then becomes a special case (its
proofs are stated for *all* `P`, so they survive the weakening of the fields).
-/

open Set Metric
open scoped Classical

namespace Work.Final

/-- The finite index set of the `p`-skeleton: all faces of cardinality `≤ p + 1` when `P.faces` is
finite, and `∅` otherwise. -/
noncomputable def lowIdx {n : ℕ} (P : PL.Cx n) (p : ℕ) : Finset (Finset (PL.E n)) :=
  if h : P.faces.Finite then h.toFinset.filter (fun s => s.card ≤ p + 1) else ∅

/-- The finite index set of the dual skeleton: the cover of `Work.Geo.DualStretch.High P p` when
`P.faces` is finite, and `∅` otherwise. -/
noncomputable def highIdx {n : ℕ} (P : PL.Cx n) (p : ℕ) : Finset (Finset (PL.E n)) :=
  if h : P.faces.Finite then Work.Geo.DualStretch.highCover P h p else ∅

/-- The low part (`p`-skeleton) of a complex, as a union over the finite index set `lowIdx`:
it is the `p`-skeleton when `P.faces` is finite (the case of every consumer), and `∅` otherwise.
Always closed.  This is `Work.Geo.DualStretch.Low` restricted to finite complexes. -/
noncomputable def skelLow {n : ℕ} (P : PL.Cx n) (p : ℕ) : Set (PL.E n) :=
  ⋃ s ∈ lowIdx P p, PL.simp s

/-- The high part (dual `(n-p-1)`-skeleton) of a complex, as a union over the finite index set
`highIdx`: it is `Work.Geo.DualStretch.High P p` when `P.faces` is finite, and `∅` otherwise.
Always closed. -/
noncomputable def skelHigh {n : ℕ} (P : PL.Cx n) (p : ℕ) : Set (PL.E n) :=
  ⋃ s ∈ highIdx P p, PL.simp s

/-- Membership in `skelLow`. -/
theorem mem_skelLow {n : ℕ} {P : PL.Cx n} {p : ℕ} {x : PL.E n} :
    x ∈ skelLow P p ↔ ∃ s ∈ lowIdx P p, x ∈ PL.simp s := by
  rw [skelLow]
  constructor
  · intro h
    rw [Set.mem_iUnion] at h
    obtain ⟨s, h⟩ := h
    rw [Set.mem_iUnion] at h
    obtain ⟨hs, hxs⟩ := h
    exact ⟨s, hs, hxs⟩
  · rintro ⟨s, hs, hxs⟩
    rw [Set.mem_iUnion]
    refine ⟨s, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hs, hxs⟩

/-- Membership in `skelHigh`. -/
theorem mem_skelHigh {n : ℕ} {P : PL.Cx n} {p : ℕ} {x : PL.E n} :
    x ∈ skelHigh P p ↔ ∃ s ∈ highIdx P p, x ∈ PL.simp s := by
  rw [skelHigh]
  constructor
  · intro h
    rw [Set.mem_iUnion] at h
    obtain ⟨s, h⟩ := h
    rw [Set.mem_iUnion] at h
    obtain ⟨hs, hxs⟩ := h
    exact ⟨s, hs, hxs⟩
  · rintro ⟨s, hs, hxs⟩
    rw [Set.mem_iUnion]
    refine ⟨s, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hs, hxs⟩

/-- `skelLow` is the `p`-skeleton of a finite complex. -/
theorem skelLow_of_finite {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) (p : ℕ) :
    skelLow P p = Work.Geo.DualStretch.Low P p := by
  ext x
  rw [mem_skelLow]
  constructor
  · rintro ⟨s, hs, hxs⟩
    rw [lowIdx, dif_pos hP, Finset.mem_filter] at hs
    exact ⟨s, (Set.Finite.mem_toFinset hP).mp hs.1, hs.2, hxs⟩
  · rintro ⟨s, hs, hc, hxs⟩
    refine ⟨s, ?_, hxs⟩
    rw [lowIdx, dif_pos hP, Finset.mem_filter]
    exact ⟨(Set.Finite.mem_toFinset hP).mpr hs, hc⟩

/-- `skelHigh` is the dual skeleton of a finite complex. -/
theorem skelHigh_of_finite {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) (p : ℕ) :
    skelHigh P p = Work.Geo.DualStretch.High P p := by
  apply Subset.antisymm
  · intro x hx
    rw [mem_skelHigh] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    rw [highIdx, dif_pos hP, Work.Geo.DualStretch.highCover, Finset.mem_image] at hs
    obtain ⟨T, hT, rfl⟩ := hs
    rw [Finset.mem_filter] at hT
    exact ⟨T, fun σ hσ => (Set.Finite.mem_toFinset hP).mp (Finset.mem_powerset.mp hT.1 hσ),
      hT.2.1, hT.2.2.1, hT.2.2.2, hxs⟩
  · rintro x ⟨T, hT, hne, hchain, hcard, hx⟩
    rw [mem_skelHigh]
    refine ⟨T.image Work.Geo.DualStretch.bary, ?_, hx⟩
    rw [highIdx, dif_pos hP, Work.Geo.DualStretch.highCover, Finset.mem_image]
    exact ⟨T, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (fun σ hσ => (Set.Finite.mem_toFinset hP).mpr (hT hσ)),
        hne, hchain, hcard⟩, rfl⟩

/-- `skelLow` is always closed. -/
theorem isClosed_skelLow {n : ℕ} (P : PL.Cx n) (p : ℕ) : IsClosed (skelLow P p) := by
  rw [skelLow]
  exact isClosed_biUnion_finset fun s _ => (Finset.finite_toSet s).isClosed_convexHull ℝ

/-- `skelHigh` is always closed. -/
theorem isClosed_skelHigh {n : ℕ} (P : PL.Cx n) (p : ℕ) : IsClosed (skelHigh P p) := by
  rw [skelHigh]
  exact isClosed_biUnion_finset fun s _ => (Finset.finite_toSet s).isClosed_convexHull ℝ

/-- `skelLow` lies in the polyhedron. -/
theorem skelLow_subset_space {n : ℕ} (P : PL.Cx n) (p : ℕ) : skelLow P p ⊆ P.space := by
  intro x hx
  rw [mem_skelLow] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  by_cases h : P.faces.Finite
  · rw [lowIdx, dif_pos h, Finset.mem_filter] at hs
    exact Geometry.SimplicialComplex.convexHull_subset_space
      ((Set.Finite.mem_toFinset h).mp hs.1) hxs
  · rw [lowIdx, dif_neg h] at hs
    simp at hs

/-- `skelHigh` lies in the polyhedron. -/
theorem skelHigh_subset_space {n : ℕ} (P : PL.Cx n) (p : ℕ) : skelHigh P p ⊆ P.space := by
  by_cases h : P.faces.Finite
  · rw [skelHigh_of_finite P h p]
    exact Work.Geo.DualStretch.High_subset_space P p
  · intro x hx
    rw [mem_skelHigh, highIdx, dif_neg h] at hx
    simp at hx

/-- `skelLow` is `p`-dimensional in Newman's sense (`PL.DomDim`). -/
theorem domDim_skelLow {n : ℕ} (P : PL.Cx n) (p : ℕ) : PL.DomDim (skelLow P p) (p : ℤ) := by
  by_cases h : P.faces.Finite
  · rw [skelLow_of_finite P h p]
    exact Work.Geo.DualStretch.low_dom P h p
  · have hempty : skelLow P p = ∅ := by
      rw [skelLow, lowIdx, dif_neg h]
      simp
    rw [hempty]
    exact Work.PL.Subdiv.domDim_empty p

/-- `skelHigh` is `(n-p-1)`-dimensional in Newman's sense (`PL.DomDim`), with the truncated
natural-number dimension used in the `SkeletonData` interface. -/
theorem domDim_skelHigh {n : ℕ} (P : PL.Cx n) (p : ℕ) :
    PL.DomDim (skelHigh P p) ((n - p - 1 : ℕ) : ℤ) := by
  by_cases h : P.faces.Finite
  · by_cases hpn : p + 1 ≤ n
    · rw [skelHigh_of_finite P h p]
      have hcast : ((n - p - 1 : ℕ) : ℤ) = (n : ℤ) - (p : ℤ) - 1 := by omega
      rw [hcast]
      exact Work.Geo.DualStretch.high_dom P h p
    · have hempty : skelHigh P p = ∅ := by
        rw [skelHigh_of_finite P h p, Set.eq_empty_iff_forall_notMem]
        rintro x ⟨T, hT, hne, hchain, hcard, hx⟩
        obtain ⟨σ, hσ⟩ := hne
        have h1 : σ.card ≤ n + 1 := Work.Geo.DualStretch.face_card_le P (hT hσ)
        have h2 := hcard σ hσ
        omega
      rw [hempty]
      exact Work.PL.Subdiv.domDim_empty _
  · have hempty : skelHigh P p = ∅ := by
      rw [skelHigh, highIdx, dif_neg h]
      simp
    rw [hempty]
    exact Work.PL.Subdiv.domDim_empty _

/-- **The `SkeletonData` interface is inhabited** (`A6`/`G7`): the low/high skeleta above, their
closure/dimension properties, and Connell's dual stretch
(`Work.Geo.DualStretch.dual_stretch`).  See the module docstring for why `skelLow`/`skelHigh`
and not the unguarded `Work.Geo.DualStretch.Low`/`High`. -/
noncomputable def skeletonData (n : ℕ) : Work.Cells.Connell.SkeletonData n where
  Low := skelLow
  High := skelHigh
  low_sub := fun P p => skelLow_subset_space P p
  high_sub := fun P p => skelHigh_subset_space P p
  low_closed := fun P p => isClosed_skelLow P p
  high_closed := fun P p => isClosed_skelHigh P p
  low_dom := fun P p => domDim_skelLow P p
  high_dom := fun P p => domDim_skelHigh P p
  dual_stretch := fun p β α hp hα hαβ P hP hsp N₁ N₂ h₁ h₂ hL hH => by
    rw [skelLow_of_finite P hP p] at hL
    rw [skelHigh_of_finite P hP p] at hH
    exact Work.Geo.DualStretch.dual_stretch hp β α hα hαβ P hP hsp N₁ N₂ h₁ h₂ hL hH

end Work.Final
