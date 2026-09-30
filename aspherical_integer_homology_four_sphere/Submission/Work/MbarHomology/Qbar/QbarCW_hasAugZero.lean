/-
# The augmentation condition for the face poset of `Q̄`

`PolyCW.HasAugZero QbarCW` says that for every `1`-cell `e` of the face poset of the
truncated 24-cell, the incidence numbers of its two endpoints sum to zero: the two
vertices of every edge of `Q̄` receive *opposite* orientation signs.  This is the
condition that makes the cellular chain complex of `Q̄` an augmented complex
(`H₀(Q̄) ≅ ℤ`, and `Q̄` connected), and it is a hypothesis of the subdivision machinery
of `Work.Subdivision`.

## How the finite verification is done

`HasAugZero` is a statement about the two (generated) tables `qFacet` (the facet list of
each face) and `qIncRow` (the orientation number of each facet).  Writing out the check
edge by edge as `decide` would make the kernel evaluate the `865`-element filter
`P.facets e` for each of the `384` edges — the tables are long `if`-chains, and the whole
check then costs tens of minutes of kernel time.

Instead we use the structure of the data:

* `qEdge_facet_data` is *one* `decide` over `x : Fin 865` (the implication `card = 3 → …`
  short-circuits for the `481` non-edges): for every edge `x`, `qFacet x` has exactly two
  elements, every element of `qFacet x` is a facet of `x` (expressed through the cheap
  `Finset.filter` form, which only evaluates the two candidates), and the corresponding
  row of `qIncRow` sums to `0`.

* The reduction of the sum over *all* facets to the sum over the two listed facets is
  then pure `Finset` bookkeeping (`QbarCW_sum_facets_eq`): the only fact needed in the
  other direction is that `inc e f = qInc e.idx f.idx` vanishes for `f.idx ∉ qFacet e.idx`,
  which is the *definition* of `qInc`.  No facet enumeration is involved.

  (This also means the proof never needs the much stronger — and much more expensive —
  statement `(qFacet x).image ⟨·⟩ = P.facets ⟨x⟩`; only the inclusion of the listed
  facets, plus vanishing of `qInc` off the list, is used.)
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.CW

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false
-- `QbarCW.Cell` is definitionally `QbarCell`, but the projection `QbarCW.facets` is
-- elaborated with argument type `QbarCW.Cell`; the legacy transparency behaviour lets
-- `rw`/`exact` identify the two.
set_option backward.isDefEq.respectTransparency false

namespace Work.MbarHomology.Qbar

open Work.Subdivision Work.MbarHomology

/-- The finite verification, one edge at a time, of the data `qFacet`, `qIncRow` of `Q̄`.

For every `x : Fin 865` with `(qTight x).card = 3` (that is, `x` is the index of a
`1`-cell, alias an *edge* of `Q̄`):

* `qFacet x` has exactly two elements (the two endpoints), so the next two conjuncts are
  not vacuous;
* every element of `qFacet x` is a facet of `x` in `QbarCW`, i.e. a `0`-cell of the closed
  cell `x` (stated in the cheap `filter = ∅` form so that `decide` only inspects the two
  listed candidates);
* the incidence numbers of that row sum to zero, i.e. the two endpoints of the edge get
  opposite signs.

The single `decide` runs over the `865` indices; for the `481` indices which are not
edges the hypothesis is false and the kernel stops at the cardinality check. -/
theorem qEdge_facet_data : ∀ x : Fin 865, (qTight x).card = 3 →
    (qFacet x).card = 2 ∧
    (qFacet x).filter (fun y => ¬ ((⟨y⟩ : QbarCell) < (⟨x⟩ : QbarCell) ∧
        QbarCW.dim (⟨x⟩ : QbarCell) = QbarCW.dim (⟨y⟩ : QbarCell) + 1)) = ∅ ∧
    (∑ y ∈ qFacet x, qIncRow x y) = 0 := by
  decide

/-- Non-vacuity of the statement: `Q̄` has `384` edges (`1`-cells), and every edge has exactly
two facets with opposite incidence numbers (`qEdge_facet_data`). -/
theorem card_dim_one_cells :
    ((Finset.univ : Finset QbarCell).filter (fun e => QbarCW.dim e = 1)).card = 384 := by
  decide

/-- For an edge `x` of `Q̄`, the sum of the incidence numbers over *all* facets of `x`
equals the sum of the entries of the facet row `qFacet x` in the table `qIncRow`.

This reduces the (expensive to enumerate) facet set to the two entries of `qFacet x`: the
listed facets are facets (`qEdge_facet_data`), and `qInc` vanishes off `qFacet` by
definition. -/
theorem QbarCW_sum_facets_eq (x : Fin 865) (hx : (qTight x).card = 3) :
    (∑ f ∈ Work.MbarHomology.QbarCW.facets (⟨x⟩ : QbarCell),
        Work.MbarHomology.QbarCW.inc (⟨x⟩ : QbarCell) f)
      = ∑ y ∈ qFacet x, qIncRow x y := by
  obtain ⟨-, hfilt, -⟩ := qEdge_facet_data x hx
  have hsub : (qFacet x).image (fun i => (⟨i⟩ : QbarCell)) ⊆
      Work.MbarHomology.QbarCW.facets (⟨x⟩ : QbarCell) := by
    intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨y, hy, rfl⟩ := hf
    rw [PolyCW.mem_facets]
    have h := (Finset.filter_eq_empty_iff.mp hfilt) hy
    simpa only [not_not] using h
  have hzero : ∀ f ∈ Work.MbarHomology.QbarCW.facets (⟨x⟩ : QbarCell),
      f ∉ (qFacet x).image (fun i => (⟨i⟩ : QbarCell)) →
        Work.MbarHomology.QbarCW.inc (⟨x⟩ : QbarCell) f = 0 := by
    intro f _ hfnot
    have hfx : f.idx ∉ qFacet x := by
      intro hmem
      exact hfnot (by rw [Finset.mem_image]; exact ⟨f.idx, hmem, by cases f; rfl⟩)
    rw [Work.MbarHomology.QbarCW_inc, qInc]
    exact ite_eq_right hfx
  trans ∑ f ∈ (qFacet x).image (fun i => (⟨i⟩ : QbarCell)),
      Work.MbarHomology.QbarCW.inc (⟨x⟩ : QbarCell) f
  · exact (Finset.sum_subset hsub hzero).symm
  · rw [Finset.sum_image (by intro y _ z _ h; simpa using congrArg QbarCell.idx h)]
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [Work.MbarHomology.QbarCW_inc, qInc]
    exact ite_eq_left hy

/-- The incidence numbers of the two endpoints of every edge of `Q̄` sum to zero.  A kernel-checked
`decide` needs the finite check split per edge (the tables `qFacet`, `qIncRow` are long if-chains);
`native_decide` works but is not axiom-clean. -/
theorem QbarCW_hasAugZero : Work.Subdivision.PolyCW.HasAugZero Work.MbarHomology.QbarCW := by
  intro e he
  rcases e with ⟨x⟩
  have hcard : (qTight x).card = 3 := by
    have h := he
    simp only [Work.MbarHomology.QbarCW_dim] at h
    omega
  obtain ⟨-, -, hsum⟩ := qEdge_facet_data x hcard
  exact (QbarCW_sum_facets_eq x hcard).trans hsum

end Work.MbarHomology.Qbar
