import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.Models
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.attachCells_extension
import Submission.Work.Serre.AttachCompress.Assemble
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.Serre.attachIncl_pi0_bijective
import Submission.Work.Serre.rwPiMapN_bijective_of_homotopyEquiv
import Submission.Work.Serre.surjective_pimap_setIncl_of_compressRel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Wedging on `d`-spheres preserves `π_{≤ d-1}`

Let `Z` be obtained from `Y` by attaching `d`-cells along *constant* attaching maps, i.e. `Z = Y`
with a `d`-sphere wedged on at each point `y i` (`d ≥ 2`).  This file proves that the inclusion
`Y → Z` induces a *bijection* on `π_j` for every `j ≤ d - 1`.  It is the technical input that lets
one *create* homotopy groups by attaching cells: wedging on `d`-spheres raises `π_d` (and changes
nothing below it).

## Route

Write `n = d - 2`, so the attached cells have dimension `n + 2` and `d - 1 = n + 1`.

* *Injectivity* (`j ≥ 1`).  Since the attaching maps are constant, the boundary of each new cell is
  glued to a single point of `Y`; sending each new cell constantly to its attaching point is
  compatible with the gluing.  By the universal property of the attachment
  (`Work.RatHurewicz.attachCells_extension`) this gives a continuous retraction `r : Z → Y` with
  `r ∘ attachIncl = id`, and a retraction makes `π_j (attachIncl)` injective in every degree
  (`pimap_injective_of_retraction`).
* *Surjectivity, `j ≤ n + 1`.*  The pair `(Z, range attachIncl)` is compressed in dimensions
  `≤ n + 1` (`Work.Serre.AttachCompress.compression`), which by
  `Work.Serre.surjective_pimap_setIncl_of_compressRel` makes the inclusion of the range
  surjective on `π_j` for
  `j ≤ n + 1`; the homeomorphism `Work.RatHurewicz.rangeHomeo : Y ≃ₜ range attachIncl` transports
  this to `attachIncl` itself (`surjective_pimap_attachIncl_of_surjective_range`).
* Degree `0` is not a group and is not covered by the above indexing; it is
  `Work.Serre.attachIncl_pi0_bijective`.
-/

open scoped Topology unitInterval Topology.Homotopy

namespace Work.Serre

noncomputable section

/-! ## Elementary helpers -/

/-- **`piMapN` in degree `k+1` is `Work.StemsB.πmap` in index `k`** (both are the same
`Quotient.map` of postcomposition with `f`). -/
theorem piMapN_eq_pimap_succ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (k : ℕ) (x : X) :
    Work.Serre.piMapN f (k + 1) x = ⇑(Work.StemsB.πmap f k x) := by
  funext a
  induction a using Quotient.inductionOn with
  | h p => rfl

/-- **A retraction of `i` makes `π_j i` injective** for `j ≥ 1`: `π_j r` splits it, up to the
transport of the base point along `r ∘ i = id` (`Work.StemsB.homotopyGroupCast`). -/
theorem pimap_injective_of_retraction {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (i : C(X, Y)) (r : C(Y, X)) (hr : r.comp i = ContinuousMap.id X) (j : ℕ) (x : X) :
    Function.Injective (Work.StemsB.πmap i j x) := by
  have hcast : (r.comp i) x = (ContinuousMap.id X) x :=
    congrArg (fun k : C(X, X) => k x) hr
  have key : ∀ a : HomotopyGroup (Fin (j + 1)) X x,
      Work.StemsB.homotopyGroupCast hcast j (Work.StemsB.πmap (r.comp i) j x a) = a := by
    intro a
    have h := Work.StemsB.πmap_congr hr j x a
    rw [Work.StemsB.πmap_id_apply j x a] at h
    exact h
  intro a b hab
  have h : Work.StemsB.πmap (r.comp i) j x a = Work.StemsB.πmap (r.comp i) j x b := by
    have h1 := congrArg (Work.StemsB.πmap r j (i x)) hab
    rwa [← Work.StemsB.πmap_comp_apply i r j x a,
      ← Work.StemsB.πmap_comp_apply i r j x b] at h1
  have h2 := congrArg (Work.StemsB.homotopyGroupCast hcast j) h
  rw [key a, key b] at h2
  exact h2

/-! ## The retraction of a wedge of cells -/

/-- **Attaching cells along constant maps admits a continuous retraction.**  Collapse every new cell
onto its (constant) attaching point: the boundary of the `i`-th cell is glued to the single point
`y i`, so the collapse is compatible with the gluing and the universal property of the attachment
(`Work.RatHurewicz.attachCells_extension`) produces a retraction of `attachIncl`. -/
theorem exists_retraction_attachIncl_const (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (y : ι → Y) :
    ∃ r : C(Work.RatHurewicz.attachCells n Y ι (fun i => ContinuousMap.const _ (y i)), Y),
      r.comp (Work.RatHurewicz.attachIncl n Y ι (fun i => ContinuousMap.const _ (y i))) =
        ContinuousMap.id Y := by
  obtain ⟨r, hr, -⟩ := Work.RatHurewicz.attachCells_extension n Y ι
    (fun i => ContinuousMap.const (Work.RatHurewicz.cellSphere n) (y i)) (ContinuousMap.id Y)
    (fun i => ContinuousMap.const (Work.RatHurewicz.cellDisk n) (y i))
    (by intro i z; rfl)
  exact ⟨r, hr⟩

/-! ## `attachIncl` versus the inclusion of its range -/

/-- The homeomorphism `Work.RatHurewicz.rangeHomeo` as a continuous map `Y → range attachIncl`. -/
def rangeIncl (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    C(Y, ↥(Set.range (Work.RatHurewicz.attachIncl n Y ι f))) :=
  ⟨⇑(Work.RatHurewicz.rangeHomeo n Y ι f), (Work.RatHurewicz.rangeHomeo n Y ι f).continuous⟩

/-- The inverse homeomorphism, as a continuous map `range attachIncl → Y`. -/
def rangeRetr (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    C(↥(Set.range (Work.RatHurewicz.attachIncl n Y ι f)), Y) :=
  ⟨⇑(Work.RatHurewicz.rangeHomeo n Y ι f).symm,
    (Work.RatHurewicz.rangeHomeo n Y ι f).symm.continuous⟩

/-- **Surjectivity on `π` transfers from the inclusion of the range of `attachIncl` to `attachIncl`
itself**: `attachIncl` agrees with `setIncl (range attachIncl) ∘ rangeIncl`, and `rangeIncl` is a
homeomorphism.  The two factors are composed through `Work.StemsB.πmap_comp_apply`, and the change
of continuous map is handled by `Work.StemsB.πmap_congr` (which transports the base point). -/
theorem surjective_pimap_attachIncl_of_surjective_range (n : ℕ) (Y : Type) [TopologicalSpace Y]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (y₀ : Y) (j : ℕ)
    (h : Function.Surjective (Work.StemsB.πmap
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f))) j
      (rangeIncl n Y ι f y₀))) :
    Function.Surjective (Work.StemsB.πmap (Work.RatHurewicz.attachIncl n Y ι f) j y₀) := by
  have h1 : (rangeRetr n Y ι f).comp (rangeIncl n Y ι f) = ContinuousMap.id Y := by
    ext y
    simp [rangeIncl, rangeRetr]
  have h2 : (rangeIncl n Y ι f).comp (rangeRetr n Y ι f) = ContinuousMap.id _ := by
    ext q
    simp [rangeIncl, rangeRetr]
  have hcomp : (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f))).comp
      (rangeIncl n Y ι f) = Work.RatHurewicz.attachIncl n Y ι f := by
    ext y
    rfl
  have hbij : Function.Surjective (Work.StemsB.πmap (rangeIncl n Y ι f) j y₀) :=
    (Work.Serre.bijective_πmap_of_comp_eq_id_gen (rangeIncl n Y ι f) (rangeRetr n Y ι f)
      h1 h2 j y₀).2
  have hcompmap : ⇑(Work.StemsB.πmap
        ((Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f))).comp
          (rangeIncl n Y ι f)) j y₀)
      = fun a => Work.StemsB.πmap
          (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f))) j
          (rangeIncl n Y ι f y₀) (Work.StemsB.πmap (rangeIncl n Y ι f) j y₀ a) :=
    funext fun a => Work.StemsB.πmap_comp_apply (rangeIncl n Y ι f)
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f))) j y₀ a
  have hsurj : Function.Surjective (Work.StemsB.πmap
      ((Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f))).comp
        (rangeIncl n Y ι f)) j y₀) := by
    rw [hcompmap]
    exact h.comp hbij
  intro z
  obtain ⟨v, hv⟩ := hsurj ((Work.StemsB.homotopyGroupCast
    (congrArg (fun k : C(Y, Work.RatHurewicz.attachCells n Y ι f) => k y₀) hcomp) j).symm z)
  refine ⟨v, ?_⟩
  rw [← Work.StemsB.πmap_congr hcomp j y₀ v, hv, MulEquiv.apply_symm_apply]

/-! ## The main statement -/

/-- **Attaching `(n+2)`-cells along constant maps does not change `π_{≤ n+1}`** (the indexed form of
the target, with `n = d - 2`). -/
theorem piMapN_attachIncl_const_bijective (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (y : ι → Y) (y₀ : Y) :
    ∀ j : ℕ, j ≤ n + 1 →
      Function.Bijective (Work.Serre.piMapN
        (Work.RatHurewicz.attachIncl n Y ι (fun i => ContinuousMap.const _ (y i))) j y₀) := by
  intro j hj
  let f : ι → C(Work.RatHurewicz.cellSphere n, Y) := fun i => ContinuousMap.const _ (y i)
  let Z := Work.RatHurewicz.attachCells n Y ι f
  let iZ := Work.RatHurewicz.attachIncl n Y ι f
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    rw [Work.Serre.piMapN_eq_homotopyGroupMap iZ 0 y₀]
    exact Work.Serre.attachIncl_pi0_bijective n Y ι f y₀
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [piMapN_eq_pimap_succ iZ k y₀]
    constructor
    · obtain ⟨r, hr⟩ := exists_retraction_attachIncl_const n Y ι y
      exact pimap_injective_of_retraction iZ r hr k y₀
    · have hsurj : Function.Surjective (Work.StemsB.πmap
          (Work.RatHurewicz.setIncl (Set.range iZ)) k (rangeIncl n Y ι f y₀)) :=
        Work.Serre.surjective_pimap_setIncl_of_compressRel (X := Z) (A := Set.range iZ) (rangeIncl n Y ι f y₀) (n + 1)
          (fun d' hd' => Work.Serre.AttachCompress.compression n Y ι f d' hd') k hj
      exact surjective_pimap_attachIncl_of_surjective_range n Y ι f y₀ k hsurj

/-- Attaching cells along *constant* maps (i.e. wedging on `d`-spheres) preserves `π_j` for `j ≤ d-1`.

Let `Z` be obtained from `Y` by attaching `d`-cells (`d ≥ 2`) along the constant maps at the
points `y i` (so `Z` is `Y` wedged with a `d`-sphere at each point `y i`).  Then for every `j ≤ d-1`
the inclusion `Y → Z` induces a bijection on `π_j`.

Proof sketch.  (a) *Injectivity, all `j`*: because the attaching map of the `i`-th cell is the
constant map at `y i`, collapsing each new disc onto its attaching point is compatible with the
gluing and defines a continuous retraction `r : Z → Y` with `r ∘ attachIncl = id`; hence
`π_j (attachIncl)` is injective (it is split by `π_j r`).  (b) *Surjectivity, `j ≤ d-1`*: the pair
`(Z,Y)` is `(d-1)`-connected, i.e. `Work.RatHurewicz.attachCells_relPi_subsingleton` gives the
vanishing of `RelHomotopyGroup (attachIncl (d-2) Y ι f) y₀ j` for `j ≤ d-2`, so the pair long exact
sequence (`Work.RatHurewicz.pair_les`, or `piMap_surjective_of_relPi_subsingleton`) makes
`π_j(Y) → π_j(Z)` surjective.

This is the fact needed to *create* homotopy groups by attaching cells: wedging on `n`-spheres
raises `π_n` (and nothing below `n`) without disturbing `π_j` for `j ≤ n-1`. -/
theorem attachIncl_const_piMapN_bijective (d : ℕ) (hd : 2 ≤ d) (Y : Type) [TopologicalSpace Y]
    (ι : Type) (y : ι → Y) (y₀ : Y) :
    ∀ j : ℕ, j ≤ d - 1 →
      Function.Bijective (Work.Serre.piMapN (Work.RatHurewicz.attachIncl (d - 2) Y ι
        (fun i => ContinuousMap.const _ (y i))) j y₀) := by
  intro j hj
  exact piMapN_attachIncl_const_bijective (d - 2) Y ι y y₀ j (by omega)

end

end Work.Serre
