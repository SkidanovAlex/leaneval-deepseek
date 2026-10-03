import Mathlib
import Submission.Lib.Unif2.Commons.Topology.CWComplex.countable_cell_of_secondCountable
import Submission.Lib.Unif2.Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace
import Submission.Lib.Unif2.Commons.Topology.CWComplex.exists_cwComplex_homeomorph_univ
import Submission.Lib.Unif2.Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract
import Submission.Lib.Unif2.Commons.Topology.Homotopy.exists_sdr_of_locallyFinite_closed_cover_folds
import Submission.Lib.Unif2.Commons.Topology.Homotopy.deformationRetract_of_chamber_folds
import Submission.Lib.Unif2.Commons.Topology.Homotopy.chamber_fold_of_closure_deformationRetract
import Submission.Lib.Unif2.Commons.Topology.Surface.exists_locallyFinite_disk_tiling
import Submission.Lib.Unif2.Commons.Topology.Jordan.frontier_connectedComponentIn_subset
import Submission.Lib.Unif2.Commons.Topology.Jordan.crosscut_component_closure
import Submission.Lib.Unif2.Commons.Topology.Jordan.crosscut_complement_at_most_two
import Submission.Lib.Unif2.Commons.Topology.Jordan.crosscut_complement_not_preconnected
import Submission.Lib.Unif2.Commons.Topology.Plane.closure_deformationRetract_of_starShaped
import Submission.Lib.Unif2.Commons.Topology.Plane.convex_tree_retract
import Submission.Lib.Unif2.Commons.Topology.Plane.retract_union_accumulate_of_retracts
import Submission.Lib.Unif2.Commons.Topology.Charts.chartedSpace_stronglyLocallyContractible
import Submission.Lib.Unif2.Commons.Topology.Plane.maxCell_mem_of_mem
import Submission.Lib.Unif2.Commons.Topology.Plane.maxCell_interior_disjoint
import Submission.Lib.Unif2.Commons.Topology.Plane.maximal_dyadicCells_locallyFinite

/-!
# The spine of a non-compact surface: the reduction, with the geometric input as a hypothesis

This is the *hand-off* form of `Submission/Work/Topology/Surface/spine_of_noncompact_surface.lean`:
the one missing geometric input (a locally finite one-sided cut system, `HasCutSystemCore`) is an
explicit hypothesis of every theorem below, so the file is **`sorry`-free** and its results can be
imported and instantiated by whoever supplies that input.

# The spine of a non-compact surface

`Commons.Topology.Surface.spine_of_noncompact_surface`: every connected, second countable,
non-compact *topological* surface (a space with `ChartedSpace ℂ`) contains a subspace `G` which, as a
subspace, is a one-dimensional CW complex (no cells of dimension `≥ 2`, countably many cells), and to
which `X` is homotopy equivalent.  This is the classical spine theorem of Johansson/Stallings.

## What this file proves, and the single remaining gap

The file is a *reduction*, with the geometric input made an explicit hypothesis: the chain

`spine_of_noncompact_surface_of_core`  ⟸  `exists_chamber_data_of_surface_of_core`
⟸  `exists_cutSystem_of_surface_of_core`  ⟸  **`HasCutSystemCore X`**

is proved *unconditionally except for* `HasCutSystemCore X` (a `def`, no proof obligation), so the
file is `sorry`-free and importable.  To obtain the spine statement one only has to supply
`HasCutSystemCore X`; everything else below is unconditional.  The pieces are:

* **`HasCutSystemCore X`** is the *cut-system crux, reduced to its geometric essence*: a
  subspace `S` (the spine) carrying a CW structure with no cells of dimension `≥ 2`, whose
  complement's connected components are locally finite at points of `S` and whose closures strongly
  deformation retract onto `S` -- i.e. the surface has a handle decomposition with only `0`- and
  `1`-handles.  All the *non*-geometric clauses have been carved off and proved: closedness of `S` is
  automatic from the CW structure in a Hausdorff space; the frontier condition
  `frontier (connectedComponentIn Sᶜ x) ⊆ S` is automatic in a locally connected space
  (`Commons.Topology.frontier_connectedComponentIn_compl_subset`); local finiteness of the components
  is automatic away from `S` (`Commons.Topology.exists_nhds_finite_components_of_mem_compl`); and the
  assembled statement is the structure `Commons.Topology.HasCutSystemData`, obtained from the reduced
  data by `Commons.Topology.HasCutSystemData.of_reduced` (used by `exists_cutSystem_of_surface`).
* **`exists_chamber_data_of_surface_of_core`** is the *enumerated* form (the interface consumed by the gluing
  engines), **proved** from the crux via the *bridge*
  `Commons.Topology.exists_chamber_data_of_hasCutSystemData`, which enumerates the components of
  `X ∖ S` by `Commons.Topology.exists_enumeration_components` and transports the six clauses.
* `Commons.Topology.Homotopy.spine_geometric_input_of_chamber_data` converts the enumerated data into
  the CW-statement form of the geometric input, using `Commons.Topology.Homotopy.sdr_of_chamber_data`:
  the per-chamber closure retractions become supported folds via
  `chamber_fold_of_closure_deformationRetract`, the local finiteness becomes the gluing engine's `hint`
  clause via `hint_of_locallyFinite_chambers`, and the folds are pasted by
  `deformationRetract_of_chamber_folds`.
* the last step is *proved*, using the commons theorems `exists_cwComplex_univ_of_isClosed_subspace`
  (CW structure on a closed subspace, transported to the subtype),
  `countable_cell_of_secondCountable` (countably many cells on a second countable space), and
  `homotopyEquiv_of_deformationRetract` (an SDR is a homotopy equivalence).
* `spine_geometric_input_of_local_data` (proved) is the assembled *engine-ready* form of the same
  input: a locally finite closed cover `K` of `X` whose pairwise intersections lie in a 1-dimensional
  CW spine `S`, together with folds of the pieces into `S`; it is fed by
  `Commons.Topology.Homotopy.exists_sdr_of_locallyFinite_closed_cover_folds`.
* `Commons.Topology.CWComplex.ArcDev.cwComplex_of_locallyFinite_arcs` (proved, inlined below) builds
  the one-dimensional CW structure on a locally finite union of arcs meeting only in common endpoints.

Everything else proved in this file (the planar `V`-fold machinery, the two-piece collapse, the
crosscut lemmas, the disk decompositions, ...) is helper material for the topological route.

## Why the remaining statement is hard

The hypotheses have **no** `IsManifold` hypothesis, so none of the project's complex-analytic or
smooth machinery applies: `exists_locallyFinite_disk_tiling` needs
`IsManifold (modelWithCornersSelf ℂ ℂ) 1 X`, and `IsManifold` is *not* derivable from
`ChartedSpace ℂ X`. The only structural input available in the topological category is the star cover
(`exists_star_cover`: a locally finite closed cover by chart disks any two overlapping members of
which lie in a common chart). Consequently the *smooth* versions of this theorem (pursued elsewhere
in the repository) are strictly easier; the remaining gap here is the topological-surface layer
(a locally finite cut system / triangulation, equivalently tame arcs and regular neighbourhoods),
which is in neither Mathlib nor the commons.
-/

open Set Metric
open scoped Topology

/-!
# Locally finite unions of arcs are one-dimensional CW complexes (development)

Proved (`cwComplex_of_locallyFinite_arcs`, at the bottom of this block), inlined into this
file because the published file may import only Mathlib and `Submission.Commons.*`.

Given a locally finite family of arcs in a Hausdorff space whose pairwise intersections consist of
common endpoints, the union carries a CW complex structure with no cells of dimension `≥ 2`: the
`0`-cells are the endpoints, the `1`-cells the arcs themselves, each arc parametrised by
`[-1,1] ≅ [0,1]` through the given injection.

This file is built incrementally and kept green; what is proved so far is what is listed below.
-/

namespace Commons.Topology.CWComplex.ArcDev

open Classical

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] {ι : Type u}

/-- The set of endpoints of all the arcs. -/
def endSet (γ : ι → C(Set.Icc (0:ℝ) 1, X)) : Set X :=
  Set.range (fun i => (γ i) 0) ∪ Set.range (fun i => (γ i) 1)

/-- The affine identification of `[-1,1]` with `[0,1]`, clamped so as to be total. -/
noncomputable def toIcc (v : Fin 1 → ℝ) : Set.Icc (0:ℝ) 1 :=
  ⟨max 0 (min 1 ((v 0 + 1) / 2)), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma norm_fin_one (v : Fin 1 → ℝ) : ‖v‖ = |v 0| := by rw [Pi.norm_def]; simp

lemma ball_fin_one {v : Fin 1 → ℝ} (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) : |v 0| < 1 := by
  have h' : ‖v‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hv
  rwa [norm_fin_one v] at h'

lemma toIcc_coe (v : Fin 1 → ℝ) (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    (toIcc v : ℝ) = (v 0 + 1) / 2 := by
  have h := ball_fin_one hv
  rw [abs_lt] at h
  simp only [toIcc]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- The homeomorphism from the parameter interval onto the `i`-th arc. -/
noncomputable def arcHomeo (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) : Set.Icc (0:ℝ) 1 ≃ₜ Set.range (γ i) := by
  haveI : CompactSpace (Set.Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective (γ i) (hinj i))
    ((γ i).continuous.subtype_mk (fun x => ⟨x, rfl⟩))

@[simp] lemma arcHomeo_coe (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj) (i : ι) (s : Set.Icc (0:ℝ) 1) :
    ((arcHomeo γ hinj i s : Set.range (γ i)) : X) = (γ i) s := rfl

/-- The parametrisation of the `i`-th arc by `Fin 1 → ℝ`. -/
noncomputable def cellToFun (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) (v : Fin 1 → ℝ) : X := (arcHomeo γ hinj i (toIcc v) : X)

lemma arcHomeo_zero (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj) (i : ι) :
    arcHomeo γ hinj i 0 = ⟨(γ i) 0, ⟨0, rfl⟩⟩ := rfl

lemma arcHomeo_one (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj) (i : ι) :
    arcHomeo γ hinj i 1 = ⟨(γ i) 1, ⟨1, rfl⟩⟩ := rfl

/-- The inverse parametrisation: on the `i`-th arc this is the inverse of the parametrisation. -/
noncomputable def cellInvFun (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) (x : X) : Fin 1 → ℝ :=
  fun _ => if h : x ∈ Set.range (γ i) then
    2 * (((arcHomeo γ hinj i).symm ⟨x, h⟩ : Set.Icc (0:ℝ) 1) : ℝ) - 1 else 0

lemma cellInvFun_apply (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) {x : X} (hx : x ∈ Set.range (γ i)) :
    cellInvFun γ hinj i x = fun _ : Fin 1 =>
      2 * (((arcHomeo γ hinj i).symm ⟨x, hx⟩ : Set.Icc (0:ℝ) 1) : ℝ) - 1 := by
  unfold cellInvFun
  rw [dif_pos hx]

lemma cellInvFun_apply_zero (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) {x : X} (hx : x ∈ Set.range (γ i)) :
    cellInvFun γ hinj i x 0 =
      2 * (((arcHomeo γ hinj i).symm ⟨x, hx⟩ : Set.Icc (0:ℝ) 1) : ℝ) - 1 := by
  rw [cellInvFun_apply γ hinj i hx]

/-- The parameter of the left endpoint is not attained away from that endpoint. -/
lemma symm_ne_zero_of_ne_left (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) {x : X} (hx : x ∈ Set.range (γ i))
    (hx0 : x ≠ (γ i) 0) : (arcHomeo γ hinj i).symm ⟨x, hx⟩ ≠ 0 := by
  intro h
  have h1 : arcHomeo γ hinj i ((arcHomeo γ hinj i).symm ⟨x, hx⟩) = arcHomeo γ hinj i 0 := by rw [h]
  rw [Homeomorph.apply_symm_apply, arcHomeo_zero] at h1
  exact hx0 (Subtype.ext_iff.mp h1)

/-- The parameter of the right endpoint is not attained away from that endpoint. -/
lemma symm_ne_one_of_ne_right (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) {x : X} (hx : x ∈ Set.range (γ i))
    (hx1 : x ≠ (γ i) 1) : (arcHomeo γ hinj i).symm ⟨x, hx⟩ ≠ 1 := by
  intro h
  have h1 : arcHomeo γ hinj i ((arcHomeo γ hinj i).symm ⟨x, hx⟩) = arcHomeo γ hinj i 1 := by rw [h]
  rw [Homeomorph.apply_symm_apply, arcHomeo_one] at h1
  exact hx1 (Subtype.ext_iff.mp h1)

/-- The inverse parametrisation maps the open arc into the open unit ball. -/
lemma cellInvFun_mem_ball (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) {x : X}
    (hx : x ∈ Set.range (γ i) \ {(γ i) 0, (γ i) 1}) :
    cellInvFun γ hinj i x ∈ Metric.ball (0 : Fin 1 → ℝ) 1 := by
  have hxr : x ∈ Set.range (γ i) := hx.1
  have hx0 : x ≠ (γ i) 0 := fun h => hx.2 (by rw [h]; simp)
  have hx1 : x ≠ (γ i) 1 := fun h => hx.2 (by rw [h]; simp)
  have hs0 := symm_ne_zero_of_ne_left γ hinj i hxr hx0
  have hs1 := symm_ne_one_of_ne_right γ hinj i hxr hx1
  have hb : (0:ℝ) ≤ (((arcHomeo γ hinj i).symm ⟨x, hxr⟩ : Set.Icc (0:ℝ) 1) : ℝ) ∧
      (((arcHomeo γ hinj i).symm ⟨x, hxr⟩ : Set.Icc (0:ℝ) 1) : ℝ) ≤ 1 :=
    ((arcHomeo γ hinj i).symm ⟨x, hxr⟩).2
  have hpos : (0:ℝ) < (((arcHomeo γ hinj i).symm ⟨x, hxr⟩ : Set.Icc (0:ℝ) 1) : ℝ) :=
    lt_of_le_of_ne hb.1 (Ne.symm (fun h => hs0 (Subtype.ext h)))
  have hlt : (((arcHomeo γ hinj i).symm ⟨x, hxr⟩ : Set.Icc (0:ℝ) 1) : ℝ) < 1 :=
    lt_of_le_of_ne hb.2 (fun h => hs1 (Subtype.ext h))
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_fin_one,
    cellInvFun_apply_zero γ hinj i hxr]
  rw [abs_lt]
  constructor <;> linarith

/-- `toIcc` inverts the inverse parametrisation: the clamped affine map undoes `cellInvFun`. -/
lemma toIcc_cellInvFun (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) {x : X} (hx : x ∈ Set.range (γ i)) :
    toIcc (cellInvFun γ hinj i x) = (arcHomeo γ hinj i).symm ⟨x, hx⟩ := by
  have hb : (0:ℝ) ≤ (((arcHomeo γ hinj i).symm ⟨x, hx⟩ : Set.Icc (0:ℝ) 1) : ℝ) ∧
      (((arcHomeo γ hinj i).symm ⟨x, hx⟩ : Set.Icc (0:ℝ) 1) : ℝ) ≤ 1 :=
    ((arcHomeo γ hinj i).symm ⟨x, hx⟩).2
  apply Subtype.ext
  show (max 0 (min 1 ((cellInvFun γ hinj i x 0 + 1) / 2)) : ℝ) = _
  rw [cellInvFun_apply_zero γ hinj i hx]
  rw [show (2 * (((arcHomeo γ hinj i).symm ⟨x, hx⟩ : Set.Icc (0:ℝ) 1) : ℝ) - 1 + 1) / 2
      = (((arcHomeo γ hinj i).symm ⟨x, hx⟩ : Set.Icc (0:ℝ) 1) : ℝ) from by ring_nf]
  rw [min_eq_right hb.2, max_eq_right hb.1]

/-- The parametrisation is a left inverse of the inverse parametrisation. -/
lemma cellToFun_inv (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) {x : X} (hx : x ∈ Set.range (γ i)) :
    cellToFun γ hinj i (cellInvFun γ hinj i x) = x := by
  show ((arcHomeo γ hinj i (toIcc (cellInvFun γ hinj i x))) : X) = x
  rw [toIcc_cellInvFun γ hinj i hx]
  show ((arcHomeo γ hinj i ((arcHomeo γ hinj i).symm ⟨x, hx⟩) : Set.range (γ i)) : X) = x
  rw [Homeomorph.apply_symm_apply]

/-- The inverse parametrisation is a left inverse of the parametrisation. -/
lemma cellInvFun_toFun (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) {v : Fin 1 → ℝ}
    (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    cellInvFun γ hinj i (cellToFun γ hinj i v) = v := by
  have hx : cellToFun γ hinj i v ∈ Set.range (γ i) := (arcHomeo γ hinj i (toIcc v)).2
  have hsymm : (arcHomeo γ hinj i).symm ⟨cellToFun γ hinj i v, hx⟩ = toIcc v := by
    show (arcHomeo γ hinj i).symm ⟨(arcHomeo γ hinj i (toIcc v) : Set.range (γ i)), hx⟩ = toIcc v
    rw [Homeomorph.symm_apply_apply]
  rw [cellInvFun_apply γ hinj i hx]
  funext j
  fin_cases j
  show 2 * (((arcHomeo γ hinj i).symm ⟨cellToFun γ hinj i v, hx⟩ : Set.Icc (0:ℝ) 1) : ℝ) - 1
      = v 0
  rw [hsymm, toIcc_coe v hv]
  ring

/-- Continuity of the parametrisation on the whole model space (hence on `closedBall 0 1`). -/
lemma continuous_cellToFun (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) : Continuous (cellToFun γ hinj i) := by
  have h1 : Continuous (fun v : Fin 1 → ℝ =>
      (toIcc v : Set.Icc (0:ℝ) 1)) := by
    apply Continuous.subtype_mk
    show Continuous fun v : Fin 1 → ℝ => max 0 (min 1 ((v 0 + 1) / 2))
    fun_prop
  exact continuous_subtype_val.comp ((arcHomeo γ hinj i).continuous.comp h1)

/-- Continuity of the inverse parametrisation on the arc. -/
lemma continuousOn_cellInvFun (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    ContinuousOn (cellInvFun γ hinj i) (Set.range (γ i)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_pi (fun j => ?_)
  fin_cases j
  have h1 : Continuous (fun y : Set.range (γ i) =>
      (((arcHomeo γ hinj i).symm y : Set.Icc (0:ℝ) 1) : ℝ)) :=
    continuous_subtype_val.comp (arcHomeo γ hinj i).symm.continuous
  exact ((continuous_const.mul h1).sub continuous_const).congr
    (fun y => (congrFun (cellInvFun_apply γ hinj i y.2) 0).symm)

lemma toIcc_ne_zero (v : Fin 1 → ℝ) (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    toIcc v ≠ 0 := by
  intro h
  have h1 : (toIcc v : ℝ) = 0 := by rw [h]; rfl
  rw [toIcc_coe v hv] at h1
  have h2 := ball_fin_one hv
  rw [abs_lt] at h2
  linarith [h2.1]

lemma toIcc_ne_one (v : Fin 1 → ℝ) (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    toIcc v ≠ 1 := by
  intro h
  have h1 : (toIcc v : ℝ) = 1 := by rw [h]; rfl
  rw [toIcc_coe v hv] at h1
  have h2 := ball_fin_one hv
  rw [abs_lt] at h2
  linarith [h2.2]

lemma cellToFun_ne_left (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) {v : Fin 1 → ℝ}
    (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) : cellToFun γ hinj i v ≠ (γ i) 0 := by
  intro h
  have h1 : arcHomeo γ hinj i (toIcc v) = arcHomeo γ hinj i 0 := Subtype.ext h
  exact toIcc_ne_zero v hv ((arcHomeo γ hinj i).injective h1)

lemma cellToFun_ne_right (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) {v : Fin 1 → ℝ}
    (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) : cellToFun γ hinj i v ≠ (γ i) 1 := by
  intro h
  have h1 : arcHomeo γ hinj i (toIcc v) = arcHomeo γ hinj i 1 := Subtype.ext h
  exact toIcc_ne_one v hv ((arcHomeo γ hinj i).injective h1)

/-- **The cell map of the `i`-th arc**: it parametrises the arc by the closed unit ball of
`Fin 1 → ℝ` (i.e. by `[-1,1]`), with the (open) arc as target. -/
noncomputable def cellMap (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) : PartialEquiv (Fin 1 → ℝ) X where
  toFun := cellToFun γ hinj i
  invFun := cellInvFun γ hinj i
  source := Metric.ball 0 1
  target := Set.range (γ i) \ {(γ i) 0, (γ i) 1}
  map_source' := fun v hv => ⟨(arcHomeo γ hinj i (toIcc v)).2, by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨cellToFun_ne_left γ hinj i hv, cellToFun_ne_right γ hinj i hv⟩⟩
  map_target' := fun x hx => cellInvFun_mem_ball γ hinj i hx
  left_inv' := fun v hv => cellInvFun_toFun γ hinj i hv
  right_inv' := fun x hx => cellToFun_inv γ hinj i hx.1

@[simp] lemma cellMap_source (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    (cellMap γ hinj i).source = Metric.ball (0 : Fin 1 → ℝ) 1 := rfl

@[simp] lemma cellMap_toFun (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    (cellMap γ hinj i) = fun v => cellToFun γ hinj i v := rfl

/-- The first CW axiom for the arc decomposition: the source of a cell map is the open unit ball. -/
lemma cellMap_source_eq (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    (cellMap γ hinj i).source = Metric.ball (0 : Fin 1 → ℝ) 1 := rfl

/-- The characteristic map of an arc is continuous on the closed unit ball. -/
lemma cellMap_continuousOn (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    ContinuousOn (cellMap γ hinj i) (Metric.closedBall (0 : Fin 1 → ℝ) 1) :=
  (continuous_cellToFun γ hinj i).continuousOn

/-- The inverse of the characteristic map of an arc is continuous on its target. -/
lemma cellMap_continuousOn_symm (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    ContinuousOn (cellMap γ hinj i).symm (cellMap γ hinj i).target := by
  have h : (cellMap γ hinj i).symm = cellInvFun γ hinj i := rfl
  rw [h]
  exact (continuousOn_cellInvFun γ hinj i).mono (by intro x hx; exact hx.1)

lemma toIcc_one : toIcc (fun _ : Fin 1 => (1:ℝ)) = 1 := by
  apply Subtype.ext
  simp [toIcc]

lemma toIcc_neg_one : toIcc (fun _ : Fin 1 => (-1:ℝ)) = 0 := by
  apply Subtype.ext
  simp [toIcc]

lemma cellToFun_one (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    cellToFun γ hinj i (fun _ : Fin 1 => (1:ℝ)) = (γ i) 1 := by
  show ((arcHomeo γ hinj i (toIcc (fun _ : Fin 1 => (1:ℝ)))) : X) = (γ i) 1
  rw [toIcc_one]
  rw [arcHomeo_coe]

lemma cellToFun_neg_one (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    cellToFun γ hinj i (fun _ : Fin 1 => (-1:ℝ)) = (γ i) 0 := by
  show ((arcHomeo γ hinj i (toIcc (fun _ : Fin 1 => (-1:ℝ)))) : X) = (γ i) 0
  rw [toIcc_neg_one]
  rw [arcHomeo_coe]

/-- **The open cells are disjoint**: two arcs meet only in common endpoints, and those are not in
the open cells. -/
lemma cellMap_openCell_disjoint (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i))
    (hint : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
      ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X))
    {i j : ι} (hij : i ≠ j) :
    Disjoint ((cellMap γ hinj i) '' Metric.ball (0 : Fin 1 → ℝ) 1)
      ((cellMap γ hinj j) '' Metric.ball (0 : Fin 1 → ℝ) 1) := by
  rw [Set.disjoint_left]
  rintro x ⟨v, hv, hvx⟩ ⟨w, hw, hwx⟩
  have hmem_i : x ∈ Set.range (γ i) := hvx ▸ (arcHomeo γ hinj i (toIcc v)).2
  have hmem_j : x ∈ Set.range (γ j) := hwx ▸ (arcHomeo γ hinj j (toIcc w)).2
  have hmem := hint i j hij ⟨hmem_i, hmem_j⟩
  have hx' : x = cellToFun γ hinj i v := hvx.symm
  have hx : x ∉ ({(γ i) 0, (γ i) 1} : Set X) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨?_, ?_⟩
    · intro h
      exact cellToFun_ne_left γ hinj i hv (hx'.symm.trans h)
    · intro h
      exact cellToFun_ne_right γ hinj i hv (hx'.symm.trans h)
  exact hx hmem.1

/-- The unit sphere of `Fin 1 → ℝ` consists of the two vectors with entries `±1`. -/
lemma sphere_fin_one (v : Fin 1 → ℝ) (hv : v ∈ Metric.sphere (0 : Fin 1 → ℝ) 1) :
    v = (fun _ : Fin 1 => (1:ℝ)) ∨ v = (fun _ : Fin 1 => (-1:ℝ)) := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_fin_one] at hv
  have h : v 0 = 1 ∨ v 0 = -1 := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hv
  rcases h with h | h
  · left; funext j; fin_cases j; exact h
  · right; funext j; fin_cases j; exact h

/-- The boundary of an arc consists of its two endpoints, i.e. of `0`-cells. -/
lemma cellToFun_mem_pair (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) {v : Fin 1 → ℝ}
    (hv : v ∈ Metric.sphere (0 : Fin 1 → ℝ) 1) :
    cellToFun γ hinj i v ∈ ({(γ i) 0, (γ i) 1} : Set X) := by
  rcases sphere_fin_one v hv with h | h
  · rw [h]
    show ((arcHomeo γ hinj i (toIcc (fun _ : Fin 1 => (1:ℝ)))) : X) ∈ ({(γ i) 0, (γ i) 1} : Set X)
    rw [toIcc_one, arcHomeo_coe]
    exact Or.inr rfl
  · rw [h]
    show ((arcHomeo γ hinj i (toIcc (fun _ : Fin 1 => (-1:ℝ)))) : X) ∈ ({(γ i) 0, (γ i) 1} : Set X)
    rw [toIcc_neg_one, arcHomeo_coe]
    exact Or.inl rfl
section CrossPairs

/-- A point of the *open* cell of an arc is neither endpoint of that arc. -/
lemma cellMap_notMem_pair (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) {v : Fin 1 → ℝ}
    (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    cellToFun γ hinj i v ∉ ({(γ i) 0, (γ i) 1} : Set X) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨cellToFun_ne_left γ hinj i hv, cellToFun_ne_right γ hinj i hv⟩

/-- The `0`-cell map at a point of `endSet γ`: the constant partial equivalence at that point. -/
noncomputable def pointMap (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) :
    PartialEquiv (Fin 0 → ℝ) X :=
  PartialEquiv.single (α := Fin 0 → ℝ) (β := X) ![] (e : X)

lemma pointMap_apply (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) (v : Fin 0 → ℝ) :
    pointMap γ e v = (e : X) := rfl

/-- **CW axiom 1 for the `0`-cells.**  The model space of a `0`-cell is `Fin 0 → ℝ`, a single point,
so the source `{![]}` is the whole unit ball. -/
lemma pointMap_source_eq (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) :
    (pointMap γ e).source = Metric.ball (0 : Fin 0 → ℝ) 1 := by
  have h : (pointMap γ e).source = ({![]} : Set (Fin 0 → ℝ)) := rfl
  have h1 : ({![]} : Set (Fin 0 → ℝ)) = Set.univ := by
    rw [eq_univ_iff_forall]; intro v; exact Subsingleton.elim v _
  have h2 : Metric.ball (0 : Fin 0 → ℝ) 1 = Set.univ := by
    rw [eq_univ_iff_forall]; intro v
    have : v = 0 := Subsingleton.elim v 0
    rw [Metric.mem_ball, this]
    simp
  rw [h, h1, h2]

/-- **CW axiom 2 for the `0`-cells.** -/
lemma pointMap_continuousOn (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) :
    ContinuousOn (pointMap γ e) (Metric.closedBall (0 : Fin 0 → ℝ) 1) :=
  continuousOn_const

/-- **CW axiom 3 for the `0`-cells.** -/
lemma pointMap_continuousOn_symm (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) :
    ContinuousOn (pointMap γ e).symm (pointMap γ e).target :=
  continuousOn_const

/-- The closed cell of a `0`-cell is that point. -/
lemma pointMap_image (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) :
    pointMap γ e '' Metric.closedBall (0 : Fin 0 → ℝ) 1 = {(e : X)} := by
  ext x
  constructor
  · rintro ⟨v, -, hv⟩
    rw [← hv, pointMap_apply]
    simp
  · rintro rfl
    exact ⟨0, by simp [Metric.mem_closedBall], pointMap_apply γ e 0⟩

/-- The open cell of a `0`-cell is that point. -/
lemma pointMap_ball_image (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) :
    pointMap γ e '' Metric.ball (0 : Fin 0 → ℝ) 1 = {(e : X)} := by
  ext x
  constructor
  · rintro ⟨v, -, hv⟩
    rw [← hv, pointMap_apply]
    simp
  · rintro rfl
    exact ⟨0, by simp [Metric.mem_ball], pointMap_apply γ e 0⟩

/-- Two distinct `0`-cells have disjoint open cells. -/
lemma pointMap_disjoint (γ : ι → C(Set.Icc (0:ℝ) 1, X)) {e e' : ↥(endSet γ)} (h : e ≠ e') :
    Disjoint (pointMap γ e '' Metric.ball (0 : Fin 0 → ℝ) 1)
      (pointMap γ e' '' Metric.ball (0 : Fin 0 → ℝ) 1) := by
  rw [pointMap_ball_image γ e, pointMap_ball_image γ e', Set.disjoint_left]
  rintro x hx hy
  rw [Set.mem_singleton_iff] at hx hy
  exact h (Subtype.ext (hx.symm.trans hy))

/-- The open cell of a `0`-cell and the open cell of an arc are disjoint. -/
lemma pointMap_disjoint_cellMap (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i))
    (hint : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
      ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X))
    (e : ↥(endSet γ)) (i : ι) :
    Disjoint (pointMap γ e '' Metric.ball (0 : Fin 0 → ℝ) 1)
      (cellMap γ hinj i '' Metric.ball (0 : Fin 1 → ℝ) 1) := by
  rw [pointMap_ball_image γ e, Set.disjoint_left]
  rintro x hx ⟨w, hw, hw'⟩
  rw [Set.mem_singleton_iff] at hx
  have hzig : cellMap γ hinj i w = (e : X) := hw'.trans hx
  have hx_arc : (e : X) ∈ Set.range (γ i) := hzig.symm ▸ (arcHomeo γ hinj i (toIcc w)).2
  have hx_ne : (e : X) ∉ ({(γ i) 0, (γ i) 1} : Set X) := by
    rw [← hzig]
    exact cellMap_notMem_pair γ hinj i hw
  obtain ⟨i', hi'⟩ : ∃ i', (e : X) = (γ i') 0 ∨ (e : X) = (γ i') 1 := by
    rcases e.2 with h | h
    · obtain ⟨j, hj⟩ := h; exact ⟨j, Or.inl hj.symm⟩
    · obtain ⟨j, hj⟩ := h; exact ⟨j, Or.inr hj.symm⟩
  rcases hi' with hi' | hi'
  · by_cases hii : i = i'
    · subst hii; exact hx_ne (Or.inl hi')
    · have hmem := hint i i' hii
      exact hx_ne (hmem ⟨hx_arc, ⟨0, hi'.symm⟩⟩).1
  · by_cases hii : i = i'
    · subst hii; exact hx_ne (Or.inr hi')
    · have hmem := hint i i' hii
      exact hx_ne (hmem ⟨hx_arc, ⟨1, hi'.symm⟩⟩).1

end CrossPairs







section Disjointness

/-- The indexing type of the `n`-cells: the endpoints in dimension `0`, the arcs in dimension `1`,
nothing above.  It lives in the same universe as `X`, which is what `Topology.CWComplex` requires of
its cell families. -/
def Cell (γ : ι → C(Set.Icc (0:ℝ) 1, X)) : ℕ → Type u
  | 0 => ↥(endSet γ)
  | 1 => ι
  | (_ + 2) => ULift.{u, 0} PEmpty

/-- The characteristic map of an `n`-cell. -/
noncomputable def cellMapAll (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) :
    (n : ℕ) → Cell γ n → PartialEquiv (Fin n → ℝ) X
  | 0, e => pointMap γ e
  | 1, i => cellMap γ hinj i
  | (_ + 2), i => i.down.elim

/-- **`pairwiseDisjoint'`.**  The `0`-`0`, `0`-`1` and `1`-`1` cases are the three lemmas proved
above; the remaining cases are vacuous, an empty cell type having no elements. -/
lemma cellMapAll_disjoint (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i))
    (hint : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
      ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X)) :
    ∀ {n m : ℕ} (i : Cell γ n) (j : Cell γ m),
      (⟨n, i⟩ : Σ k, Cell γ k) ≠ ⟨m, j⟩ →
      Disjoint (cellMapAll γ hinj n i '' Metric.ball (0 : Fin n → ℝ) 1)
        (cellMapAll γ hinj m j '' Metric.ball (0 : Fin m → ℝ) 1) := by
  intro n m
  cases n with
  | zero =>
      cases m with
      | zero => exact fun i j h => pointMap_disjoint γ (fun hh => h (by cases hh; rfl))
      | succ m' =>
          cases m' with
          | zero => exact fun i j _ => pointMap_disjoint_cellMap γ hinj hint i j
          | succ m'' => exact fun i j _ => j.down.elim
  | succ n' =>
      cases n' with
      | zero =>
          cases m with
          | zero => exact fun i j _ => (pointMap_disjoint_cellMap γ hinj hint j i).symm
          | succ m' =>
              cases m' with
              | zero =>
                  exact fun i j h =>
                    cellMap_openCell_disjoint γ hinj hint (fun hh => h (by cases hh; rfl))
              | succ m'' => exact fun i j _ => j.down.elim
      | succ n'' => exact fun i j _ => i.down.elim

/-- **The `pairwiseDisjoint'` axiom**, in the shape required by `Topology.CWComplex`. -/
lemma cellMapAll_pairwiseDisjoint (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i))
    (hint : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
      ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X)) :
    (Set.univ : Set (Σ n, Cell γ n)).PairwiseDisjoint
      (fun ni => cellMapAll γ hinj ni.1 ni.2 '' Metric.ball (0 : Fin ni.1 → ℝ) 1) :=
  fun a _ b _ hab => cellMapAll_disjoint γ hinj hint a.2 b.2 hab

end Disjointness
section MapsTo

/-- The `0`-cells attached to the `1`-cell `i`: the two endpoints of the arc. -/
noncomputable def targetCells (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (i : ι) :
    Π m, Finset (Cell γ m) := by
  classical
  exact fun m => match m with
    | 0 => {⟨(γ i) 1, Or.inr ⟨i, rfl⟩⟩, ⟨(γ i) 0, Or.inl ⟨i, rfl⟩⟩}
    | _ => ∅

@[simp] lemma targetCells_zero (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (i : ι) :
    targetCells γ i 0 = ({⟨(γ i) 1, Or.inr ⟨i, rfl⟩⟩, ⟨(γ i) 0, Or.inl ⟨i, rfl⟩⟩} :
      Finset (Cell γ 0)) := rfl

lemma targetCells_pos (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (i : ι) {m : ℕ} (hm : m ≠ 0) :
    targetCells γ i m = (∅ : Finset (Cell γ m)) := by
  match m with
  | 0 => exact absurd rfl hm
  | _ + 1 => rfl

/-- The two endpoints of the arc `i` lie in the union of the attached `0`-cells. -/
lemma endpoints_subset_target (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    ({(γ i) 0, (γ i) 1} : Set X) ⊆
      (⋃ (m : ℕ) (_ : m < 1) (j ∈ targetCells γ i m),
        cellMapAll γ hinj m j '' Metric.closedBall (0 : Fin m → ℝ) 1) := by
  classical
  intro x hx
  have key : x ∈ (⋃ (m : ℕ) (_ : m < 1) (j ∈ targetCells γ i m),
        cellMapAll γ hinj m j '' Metric.closedBall (0 : Fin m → ℝ) 1) := by
    rcases hx with hx | hx
    · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      refine Set.mem_iUnion.mpr ⟨by norm_num, ?_⟩
      refine Set.mem_iUnion₂.mpr ⟨⟨(γ i) 0, Or.inl ⟨i, rfl⟩⟩, ?_, ?_⟩
      · rw [targetCells_zero]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · have hz : cellMapAll γ hinj 0 ⟨(γ i) 0, Or.inl ⟨i, rfl⟩⟩ =
            pointMap γ ⟨(γ i) 0, Or.inl ⟨i, rfl⟩⟩ := rfl
        rw [hx, hz, pointMap_image]
        exact rfl
    · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      refine Set.mem_iUnion.mpr ⟨by norm_num, ?_⟩
      refine Set.mem_iUnion₂.mpr ⟨⟨(γ i) 1, Or.inr ⟨i, rfl⟩⟩, ?_, ?_⟩
      · rw [targetCells_zero]
        exact Finset.mem_insert_self _ _
      · have hz : cellMapAll γ hinj 0 ⟨(γ i) 1, Or.inr ⟨i, rfl⟩⟩ =
            pointMap γ ⟨(γ i) 1, Or.inr ⟨i, rfl⟩⟩ := rfl
        rw [hx, hz, pointMap_image]
        exact rfl
  exact key

/-- **`mapsTo'`.**  The boundary of a `1`-cell is its two `0`-cells; a `0`-cell has empty boundary;
there are no higher cells. -/
lemma cellMapAll_mapsTo (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) :
    ∀ (n : ℕ) (i : Cell γ n), ∃ I : Π m, Finset (Cell γ m),
      Set.MapsTo (cellMapAll γ hinj n i) (Metric.sphere (0 : Fin n → ℝ) 1)
        (⋃ (m : ℕ) (_ : m < n) (j ∈ I m),
          cellMapAll γ hinj m j '' Metric.closedBall (0 : Fin m → ℝ) 1) := by
  intro n
  cases n with
  | zero =>
      intro i
      refine ⟨fun _ => ∅, ?_⟩
      have hsp : (Metric.sphere (0 : Fin 0 → ℝ) 1) = ∅ :=
        Metric.sphere_eq_empty_of_subsingleton (by norm_num : (1:ℝ) ≠ 0)
      rw [hsp]
      intro x hx
      simp at hx
  | succ n' =>
      cases n' with
      | zero =>
          intro i
          refine ⟨targetCells γ i, ?_⟩
          intro v hv
          show cellToFun γ hinj i v ∈ _
          exact endpoints_subset_target γ hinj i (cellToFun_mem_pair γ hinj i hv)
      | succ n'' => exact fun i => i.down.elim

/-- The image of the closed unit ball of the model space of a `1`-cell is exactly the arc. -/
lemma cellToFun_image_closedBall (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    cellToFun γ hinj i '' Metric.closedBall (0 : Fin 1 → ℝ) 1 = Set.range (γ i) := by
  ext x
  constructor
  · rintro ⟨v, -, rfl⟩
    exact ⟨toIcc v, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨fun _ : Fin 1 => 2 * (t : ℝ) - 1, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_fin_one, abs_le]
      exact ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
    · have ht : toIcc (fun _ : Fin 1 => 2 * (t : ℝ) - 1) = t := by
        apply Subtype.ext
        show max 0 (min 1 ((2 * (t : ℝ) - 1 + 1) / 2)) = (t : ℝ)
        rw [show (2 * (t : ℝ) - 1 + 1) / 2 = (t : ℝ) from by ring_nf]
        rw [min_eq_right t.2.2, max_eq_right t.2.1]
      show ((arcHomeo γ hinj i (toIcc (fun _ : Fin 1 => 2 * (t : ℝ) - 1))) : X) = (γ i) t
      rw [ht, arcHomeo_coe]

/-- **`union'`.**  The closed cells cover exactly the union of the arcs: the `0`-cells give the
endpoints, the `1`-cells give the arcs, and there are no higher cells. -/
lemma cellMapAll_union (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) :
    (⋃ (n : ℕ) (j : Cell γ n), cellMapAll γ hinj n j '' Metric.closedBall (0 : Fin n → ℝ) 1)
      = (⋃ i, Set.range (γ i)) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨j, hx⟩ := hx
    cases n with
    | zero =>
        cases j with
        | mk p hp =>
            rcases hx with ⟨v, -, hv⟩
            have hxj : x = p := by
              rw [← hv]
              show pointMap γ (⟨p, hp⟩ : ↥(endSet γ)) v = p
              exact pointMap_apply γ (⟨p, hp⟩ : ↥(endSet γ)) v
            rw [hxj]
            rcases hp with ⟨i, hi⟩ | ⟨i, hi⟩
            · exact Set.mem_iUnion.mpr ⟨i, ⟨0, hi⟩⟩
            · exact Set.mem_iUnion.mpr ⟨i, ⟨1, hi⟩⟩
    | succ n' =>
        cases n' with
        | zero =>
            rcases hx with ⟨v, -, hv⟩
            refine Set.mem_iUnion.mpr ⟨j, ?_⟩
            exact ⟨toIcc v, by rw [← hv]; rfl⟩
        | succ n'' => exact j.down.elim
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, t, ht⟩ := hx
    refine Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
    rw [← ht]
    exact (cellToFun_image_closedBall γ hinj i).ge ⟨t, rfl⟩

/-- A closed cell is compact: a point for a `0`-cell, an arc for a `1`-cell, nothing above. -/
lemma isCompact_cellMapAll (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (n : ℕ) (j : Cell γ n) :
    IsCompact (cellMapAll γ hinj n j '' Metric.closedBall (0 : Fin n → ℝ) 1) := by
  cases n with
  | zero =>
      cases j with
      | mk p hp =>
          rw [show cellMapAll γ hinj 0 (⟨p, hp⟩ : ↥(endSet γ)) '' Metric.closedBall (0 : Fin 0 → ℝ) 1
              = {p} from by
            rw [show cellMapAll γ hinj 0 (⟨p, hp⟩ : ↥(endSet γ)) = pointMap γ (⟨p, hp⟩ : ↥(endSet γ))
                from rfl, pointMap_image]]
          exact isCompact_singleton
  | succ n' =>
      cases n' with
      | zero =>
          rw [show cellMapAll γ hinj 1 j '' Metric.closedBall (0 : Fin 1 → ℝ) 1 = Set.range (γ j) from
            cellToFun_image_closedBall γ hinj j]
          rw [← Set.image_univ]
          exact isCompact_univ.image (γ j).continuous
      | succ n'' => exact j.down.elim

/-- Every closed cell is closed (in a Hausdorff space). -/
lemma isClosed_cellMapAll (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (n : ℕ) (j : Cell γ n) :
    IsClosed (cellMapAll γ hinj n j '' Metric.closedBall (0 : Fin n → ℝ) 1) :=
  (isCompact_cellMapAll γ hinj n j).isClosed

/-- **`closed'`.**  If `A` is covered by the arcs and each `A ∩ (closed cell)` is closed, then `A`
is closed: locally only finitely many arcs meet a point, so `A` agrees near that point with a finite
union of closed pieces. -/
lemma cellMapAll_closed' (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i))
    (hlf : LocallyFinite (fun i => Set.range (γ i)))
    (A : Set X) (hA : A ⊆ ⋃ i, Set.range (γ i))
    (hcl : ∀ (n : ℕ) (j : Cell γ n),
      IsClosed (A ∩ cellMapAll γ hinj n j '' Metric.closedBall (0 : Fin n → ℝ) 1)) :
    IsClosed A := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨t, ht, hfin⟩ := hlf x
  obtain ⟨W, hWt, hWopen, hxW⟩ := mem_nhds_iff.mp ht
  have hcell : ∀ i : ι,
      cellMapAll γ hinj 1 i '' Metric.closedBall (0 : Fin 1 → ℝ) 1 = Set.range (γ i) := by
    intro i
    show cellToFun γ hinj i '' Metric.closedBall (0 : Fin 1 → ℝ) 1 = Set.range (γ i)
    exact cellToFun_image_closedBall γ hinj i
  have hBclosed : IsClosed (⋃ (i : ↥{i : ι | (Set.range (γ i) ∩ t).Nonempty}),
      A ∩ Set.range (γ i)) := by
    haveI : Finite ↥{i : ι | (Set.range (γ i) ∩ t).Nonempty} := hfin.to_subtype
    exact isClosed_iUnion_of_finite (fun i => by rw [← hcell i.1]; exact hcl 1 i.1)
  have hxcl : x ∈ closure (A ∩ W) := by
    refine mem_closure_iff_nhds.mpr ?_
    intro V hV
    have hVW : V ∩ W ∈ 𝓝 x := Filter.inter_mem hV (IsOpen.mem_nhds hWopen hxW)
    have hxA := mem_closure_iff_nhds.mp hx
    obtain ⟨y, hyVW, hyA⟩ := hxA (V ∩ W) hVW
    exact ⟨y, hyVW.1, hyA, hyVW.2⟩
  have hsub : A ∩ W ⊆ ⋃ (i : ↥{i : ι | (Set.range (γ i) ∩ t).Nonempty}),
      A ∩ Set.range (γ i) := by
    intro y hy
    obtain ⟨hyA, hyW⟩ := hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hA hyA)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨y, hi, hWt hyW⟩⟩, ⟨hyA, hi⟩⟩
  have hxB : x ∈ ⋃ (i : ↥{i : ι | (Set.range (γ i) ∩ t).Nonempty}), A ∩ Set.range (γ i) :=
    hBclosed.closure_subset (closure_mono hsub hxcl)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxB
  exact hi.1

/-- The source axiom for an arbitrary cell. -/
lemma cellMapAll_source_eq (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (n : ℕ) (j : Cell γ n) :
    (cellMapAll γ hinj n j).source = Metric.ball (0 : Fin n → ℝ) 1 := by
  cases n with
  | zero => cases j with | mk p hp => exact pointMap_source_eq γ ⟨p, hp⟩
  | succ n' =>
      cases n' with
      | zero => exact cellMap_source_eq γ hinj j
      | succ n'' => exact j.down.elim

/-- The continuity axiom for an arbitrary cell. -/
lemma cellMapAll_continuousOn (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (n : ℕ) (j : Cell γ n) :
    ContinuousOn (cellMapAll γ hinj n j) (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  cases n with
  | zero => cases j with | mk p hp => exact pointMap_continuousOn γ ⟨p, hp⟩
  | succ n' =>
      cases n' with
      | zero => exact cellMap_continuousOn γ hinj j
      | succ n'' => exact j.down.elim

/-- The inverse-continuity axiom for an arbitrary cell. -/
lemma cellMapAll_continuousOn_symm (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (n : ℕ) (j : Cell γ n) :
    ContinuousOn (cellMapAll γ hinj n j).symm (cellMapAll γ hinj n j).target := by
  cases n with
  | zero => cases j with | mk p hp => exact pointMap_continuousOn_symm γ ⟨p, hp⟩
  | succ n' =>
      cases n' with
      | zero => exact cellMap_continuousOn_symm γ hinj j
      | succ n'' => exact j.down.elim

/-- **`cwComplex_of_locallyFinite_arcs`.**  A locally finite family of arcs in a Hausdorff space,
whose pairwise intersections consist of common endpoints, carries a CW complex structure with no
cells of dimension `≥ 2` on its union: the `0`-cells are the endpoints, the `1`-cells the arcs. -/
theorem cwComplex_of_locallyFinite_arcs (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i))
    (hlf : LocallyFinite (fun i => Set.range (γ i)))
    (hint : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
      ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X)) :
    ∃ hC : @Topology.CWComplex X _ (⋃ i, Set.range (γ i)),
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ _ hC n)) := by
  refine ⟨{ cell := Cell γ
            map := cellMapAll γ hinj
            source_eq := fun n j => cellMapAll_source_eq γ hinj n j
            continuousOn := fun n j => cellMapAll_continuousOn γ hinj n j
            continuousOn_symm := fun n j => cellMapAll_continuousOn_symm γ hinj n j
            pairwiseDisjoint' := cellMapAll_pairwiseDisjoint γ hinj hint
            mapsTo' := fun n j => cellMapAll_mapsTo γ hinj n j
            closed' := fun A hA hcl => cellMapAll_closed' γ hinj hlf A hA hcl
            union' := cellMapAll_union γ hinj }, ?_⟩
  intro n hn
  cases n with
  | zero => exact absurd hn (by norm_num)
  | succ n' =>
      cases n' with
      | zero => exact absurd hn (by norm_num)
      | succ n'' => exact ⟨fun x => (x : Cell γ (n'' + 2)).down.elim⟩

end MapsTo

end Commons.Topology.CWComplex.ArcDev

namespace Commons.Topology

open Set in
/-- **R3a, part 1: the first-occurrence set of a path.**

For a continuous path `γ` in a Hausdorff space, let
`T := {t | ∀ s < t, γ s ≠ γ t}` be the set of times at which `γ` attains a value it has not attained
before.  Then `0 ∈ T` and `γ` is injective on `T`: if `s < t` are both in `T` then `t ∈ T` gives
`γ s ≠ γ t` directly, and if `t < s` then `s ∈ T` gives `γ t ≠ γ s`.

This is the first ingredient of the arc-extraction lemma `exists_injective_path_between` (a path
between two distinct points of a Hausdorff space contains an injective arc): the arc is the trace of
`γ` on `T`, reparametrised by pushing the order of the interval onto `T`. -/
theorem firstOccurrences_injective {X : Type*} [TopologicalSpace X] [T2Space X]
    (γ : C(Set.Icc (0:ℝ) 1, X)) :
    (0 : Set.Icc (0:ℝ) 1) ∈ {t : Set.Icc (0:ℝ) 1 | ∀ s, s < t → γ s ≠ γ t} ∧
      InjOn γ {t : Set.Icc (0:ℝ) 1 | ∀ s, s < t → γ s ≠ γ t} := by
  constructor
  · intro s hs
    exact absurd hs (not_lt_of_ge s.2.1)
  · intro s hs t ht hst
    rcases lt_trichotomy s t with h | h | h
    · exact absurd hst (ht s h)
    · exact h
    · exact absurd hst.symm (hs t h)

/-- **R3a, part 2 (Route 1, first two ingredients).**

The image of a path is compact and connected; together with
`LocallyConnectedSpace ↥(Set.range γ)` (the third ingredient, a quotient-map transfer of the local
connectedness of the interval) it says that `range γ` is a *Peano continuum*, so that
`Topology.peanoContinuum_arcwiseConnected` turns a path between two distinct points into an injective
arc between them -- Route 1 for the arc-extraction lemma `exists_injective_path_between`.

Locating the third ingredient: `LocallyConnectedSpace (Set.Icc (0:ℝ) 1)` is not an instance found by
direct search; the two documented routes are `Topology.IsCoinducing.locallyConnectedSpace`
(`Mathlib/Topology/Connected/LocallyConnected.lean:155`), applicable because the range-factorisation
of `γ` is coinducing (a continuous surjection from a compact space to a Hausdorff space is a
quotient map), and `instLocallyConnectedSpace`
(`Mathlib/Topology/Connected/LocallyPathConnected.lean:25`) after establishing
`LocallyPathConnectedSpace` of the unit interval.  Transport along `Set.Icc 0 1 ≃ₜ unitInterval` is
the cheapest way to get the domain instance. -/

theorem isCompact_isConnected_range {X : Type*} [TopologicalSpace X]
    (γ : C(Set.Icc (0:ℝ) 1, X)) :
    IsCompact (Set.range γ) ∧ IsConnected (Set.range γ) :=
  ⟨isCompact_range γ.continuous, isConnected_range γ.continuous⟩

/-- **Obstacle 2 of Route 1, solved without the missing instance (Route B).**

The trace of an open interval on `Set.Icc a b` is preconnected, proved without ever needing
`ConditionallyCompleteLinearOrder ↥(Set.Icc a b)` (which Mathlib lacks): the trace is the image of
the *ambient* set `Set.Icc a b ∩ Set.Ioo c d` — preconnected, being an intersection of convex sets
(`Convex.isPreconnected`) — under the clamping map `t ↦ min (max t a) b`, which is continuous and
equals the coercion on `Set.Icc a b`.  This is what makes the interval traces usable as
`IsPreconnected` neighbourhoods in `locallyConnectedSpace_of_connected_bases`. -/
theorem isPreconnected_preimage_Ioo_Icc (a b c d : ℝ) (hab : a ≤ b) :
    IsPreconnected ((Subtype.val : Set.Icc a b → ℝ) ⁻¹' Set.Ioo c d) := by
  classical
  have hpre : IsPreconnected (Set.Icc a b ∩ Set.Ioo c d) :=
    ((convex_Icc a b).inter (convex_Ioo c d)).isPreconnected
  have hf : Continuous fun t : ℝ =>
      (⟨min (max t a) b, le_min (le_max_right t a) hab, min_le_right _ _⟩ : Set.Icc a b) := by
    apply Continuous.subtype_mk
    fun_prop
  have hset : ((fun t : ℝ =>
      (⟨min (max t a) b, le_min (le_max_right t a) hab, min_le_right _ _⟩ : Set.Icc a b)) ''
      (Set.Icc a b ∩ Set.Ioo c d)) = (Subtype.val : Set.Icc a b → ℝ) ⁻¹' Set.Ioo c d := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 : a ≤ t := ht.1.1
      have h2 : t ≤ b := ht.1.2
      have hcoe : (min (max t a) b : ℝ) = t := by
        rw [min_eq_left (max_le h2 hab), max_eq_left h1]
      show min (max t a) b ∈ Set.Ioo c d
      simpa only [hcoe] using ht.2
    · intro hy
      refine ⟨y.1, ⟨y.2, hy⟩, ?_⟩
      apply Subtype.ext
      have h1 : a ≤ (y : ℝ) := y.2.1
      have h2 : (y : ℝ) ≤ b := y.2.2
      show min (max (y : ℝ) a) b = (y : ℝ)
      rw [min_eq_left (max_le h2 hab), max_eq_left h1]
  rw [← hset]
  exact hpre.image _ hf.continuousOn

/-- **Obligation 1 of Route 1, assembled: closed intervals are locally connected.**

The neighbourhood basis is the trace of the `ε`-balls (`rw [nhds_induced]` then
`Metric.nhds_basis_ball.comap Subtype.val`), and the preconnected witnesses are the traces of the
balls, identified with the traces of open intervals by the verified rewrite
`Metric.mem_ball → Set.mem_Ioo → Real.dist_eq → abs_lt`, then supplied by
`isPreconnected_preimage_Ioo_Icc`.  When `b < a` the subtype is a subsingleton and every subset is
preconnected, so that case is immediate. -/
theorem locallyConnectedSpace_Icc (a b : ℝ) : LocallyConnectedSpace (Set.Icc a b) := by
  refine locallyConnectedSpace_of_connected_bases
    (fun (x : Set.Icc a b) (ε : ℝ) => Subtype.val ⁻¹' Metric.ball (x : ℝ) ε)
    (fun _ ε => 0 < ε) ?_ ?_
  · intro x
    rw [nhds_induced]
    exact (Metric.nhds_basis_ball (x := (x : ℝ))).comap Subtype.val
  · intro x ε hε
    by_cases hab : a ≤ b
    · have hset : (Subtype.val : Set.Icc a b → ℝ) ⁻¹' Metric.ball (x : ℝ) ε
          = (Subtype.val : Set.Icc a b → ℝ) ⁻¹' Set.Ioo ((x : ℝ) - ε) ((x : ℝ) + ε) := by
        ext y
        rw [Set.mem_preimage, Set.mem_preimage, Metric.mem_ball, Set.mem_Ioo, Real.dist_eq, abs_lt]
        constructor <;> intro h
        · exact ⟨by linarith [h.1], by linarith [h.2]⟩
        · exact ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [hset]
      exact isPreconnected_preimage_Ioo_Icc a b ((x : ℝ) - ε) ((x : ℝ) + ε) hab
    · have hlt : b < a := not_le.mp hab
      have hsub : Subsingleton (Set.Icc a b) := by
        refine ⟨fun u v => Subtype.ext ?_⟩
        have hu : (u : ℝ) ≤ b := (Set.mem_Icc.mp u.2).2
        have hu' : a ≤ (u : ℝ) := (Set.mem_Icc.mp u.2).1
        have hv : (v : ℝ) ≤ b := (Set.mem_Icc.mp v.2).2
        have hv' : a ≤ (v : ℝ) := (Set.mem_Icc.mp v.2).1
        exact le_antisymm (le_trans (le_trans hu hlt.le) hv') (le_trans (le_trans hv hlt.le) hu')
      exact Set.Subsingleton.isPreconnected fun y _ z _ => hsub.elim y z

/-- **Obligation 2 of Route 1: the range-factorisation of a path is coinducing.**

For `γ : C(Set.Icc 0 1, X)` with `X` Hausdorff, the map `t ↦ ⟨γ t, ⟨t, rfl⟩⟩` from the interval onto
`Set.range γ` makes the range's topology the quotient topology: `γ` is a *closed* map (closed subsets
of the compact interval have compact image, which is closed in `X`), and a continuous closed map is
strict (`IsClosedMap.isStrictMap`), i.e. its range-factorisation is a quotient map; a quotient map is
coinducing (`IsQuotientMap.isCoinducing`).  Combined with `locallyConnectedSpace_Icc` and
`Topology.IsCoinducing.locallyConnectedSpace` this gives `LocallyConnectedSpace ↥(Set.range γ)`, the
third and last ingredient of Route 1 for the arc-extraction lemma. -/
theorem isCoinducing_rangeFactorization {X : Type*} [TopologicalSpace X] [T2Space X]
    (γ : C(Set.Icc (0:ℝ) 1, X)) :
    Topology.IsCoinducing (fun t => (⟨γ t, ⟨t, rfl⟩⟩ : Set.range γ)) := by
  have hclosed : IsClosedMap γ :=
    fun s hs => (hs.isCompact.image γ.continuous).isClosed
  have hstrict : Topology.IsStrictMap γ := hclosed.isStrictMap γ.continuous
  exact hstrict.isCoinducing

/-- **Route 1, third ingredient: the image of a path is locally connected.**

Immediate from `isCoinducing_rangeFactorization` and the local connectedness of the interval
(`locallyConnectedSpace_Icc 0 1`): local connectedness is preserved by coinducing maps.  Together with
`isCompact_isConnected_range` this makes `↥(Set.range γ)` a *Peano continuum* (compact, connected,
locally connected, Hausdorff), so `Topology.peanoContinuum_arcwiseConnected` applies to it and yields
the injective arc between `γ 0` and `γ 1` — i.e. the arc-extraction lemma R3a. -/
theorem locallyConnectedSpace_range {X : Type*} [TopologicalSpace X] [T2Space X]
    (γ : C(Set.Icc (0:ℝ) 1, X)) : LocallyConnectedSpace ↥(Set.range γ) := by
  haveI := locallyConnectedSpace_Icc 0 1
  exact (isCoinducing_rangeFactorization γ).locallyConnectedSpace

-- RUNG (Obligation 1 of Route 1): `LocallyConnectedSpace (Set.Icc a b)` for closed intervals.
-- The engine is `locallyConnectedSpace_of_connected_bases`
-- (`Mathlib/Topology/Connected/LocallyConnected.lean:113`) with the trace of the `ε`-balls as the
-- neighbourhood basis (`Metric.nhds_basis_ball` pushed through `nhds_induced Subtype.val`, which
-- typechecks) and the traces as preconnected witnesses.  Two obstacles were met and are recorded so
-- the next pass starts past them:
--   (1) the set equality "trace of ball = trace of interval" needs `Subtype.dist_eq` before
--       `Real.dist_eq`/`abs_lt`: on the subtype `simp [Metric.mem_ball]` stops at `dist y x < ε`;
--   (2) `ConditionallyCompleteLinearOrder ↥(Set.Icc a b)` is NOT an instance in Mathlib (checked), so
--       `Set.OrdConnected.isPreconnected` (`Topology/Order/IntermediateValue.lean:446`) cannot be
--       applied to the subtype directly.  Workarounds to use instead: prove the preconnectedness of
--       the *ambient* interval and transfer it along the monotone quotient/order-isomorphism
--       `↥(Set.Icc a b) ≃o ↥(Set.Icc a b)`, or supply the missing instance by
--       `isPreconnected_Icc`-style transfer; or use `locallyConnectedSpace_iff_connected_subsets`
--       (`LocallyConnected.lean:101`) with interval witnesses and prove preconnectedness of the
--       interval traces through `IsPreconnected` of the ambient interval plus
--       `IsPreconnected.preimage_of_...`.


/-- **Design constraint for the spine engines (F2 of `NOTES_L245_...`).**

If `K : ι → Set X` is a locally finite closed cover of `X`, then every point of the frontier of a
member lies in another member.  Indeed the union of the *other* members is closed (local finiteness),
and if it avoided a frontier point `x` of `K i`, that whole complement would be a neighbourhood of
`x` contained in `K i` (the cover covers `X`), making `x` an interior point of `K i`.

Consequence (used to prune the design space): in any closed-cover/fold datum for the spine, the
frontier of every piece is contained in the spine, so the fold of a piece must realize a deformation
retraction of the piece onto (the spine part inside it). -/
theorem frontier_subset_iUnion_of_locallyFinite_closed_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} {K : ι → Set X} (hlf : LocallyFinite K) (hc : ∀ i, IsClosed (K i))
    (hcov : (⋃ i, K i) = Set.univ) (i : ι) :
    frontier (K i) ⊆ ⋃ j : {j : ι // j ≠ i}, K j.1 := by
  have hclosed : IsClosed (⋃ j : {j : ι // j ≠ i}, K j.1) :=
    (hlf.comp_injective Subtype.val_injective).isClosed_iUnion fun j => hc j.1
  intro x hx
  by_contra hxnot
  have hUK : ((⋃ j : {j : ι // j ≠ i}, K j.1))ᶜ ⊆ K i := by
    intro y hy
    have hyc : y ∈ ⋃ k, K k := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hyc
    by_cases hki : k = i
    · simpa [hki] using hk
    · exact absurd (Set.mem_iUnion.mpr ⟨⟨k, hki⟩, hk⟩) hy
  have hint : x ∈ interior (K i) :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hxnot) hUK)
  exact (mem_frontier_iff_notMem_interior ((hc i).frontier_subset hx)).mp hx hint


/-- **Design constraint (F3 of `NOTES_L245_...`).**

A fold `φ` of a piece `K` which keeps `K` inside `K` (the form every actual design uses) and which
at time `1` lands in the spine `S` while fixing `S` pointwise, *is* a strong deformation retraction
of `K` onto `S ∩ K`: the time-`1` map takes `K` into `S ∩ K` and fixes `S ∩ K` pointwise.

Combined with
`Commons.Topology.frontier_subset_iUnion_of_locallyFinite_closed_cover` (the frontier of every piece
lies in the spine) this is the constraint that rules out the compact "disk-like" pieces: such a
piece would have to deformation retract onto a set containing its whole boundary, which carries
essential loops. -/
theorem exists_deformationRetract_of_fold {X : Type*} [TopologicalSpace X] {K S : Set X}
    (φ : X × unitInterval → X) (hcont : ContinuousOn φ (K ×ˢ (Set.univ : Set unitInterval)))
    (h0 : ∀ x ∈ K, φ (x, 0) = x) (hK : ∀ x ∈ K, ∀ t : unitInterval, φ (x, t) ∈ K)
    (h1 : ∀ x ∈ K, φ (x, 1) ∈ S) (hfix : ∀ x ∈ S, ∀ t : unitInterval, φ (x, t) = x) :
    ∃ H : ↥K × unitInterval → ↥K, Continuous H ∧ (∀ x, H (x, 0) = x) ∧
      (∀ x, ((H (x, 1) : ↥K) : X) ∈ S) ∧
      (∀ x, (Subtype.val x) ∈ S → ∀ t : unitInterval, H (x, t) = x) := by
  have hg : Continuous fun p : ↥K × unitInterval => (Subtype.val p.1, p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hgm : ∀ p : ↥K × unitInterval, (Subtype.val p.1, p.2) ∈ K ×ˢ (Set.univ : Set unitInterval) :=
    fun p => ⟨p.1.2, Set.mem_univ _⟩
  have hφ : Continuous fun p : ↥K × unitInterval => φ (Subtype.val p.1, p.2) :=
    hcont.comp_continuous hg hgm
  refine ⟨fun p => ⟨φ (Subtype.val p.1, p.2), hK p.1.1 p.1.2 p.2⟩,
    hφ.subtype_mk _, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    exact h0 x.1 x.2
  · intro x
    exact h1 x.1 x.2
  · intro x hx t
    apply Subtype.ext
    exact hfix (x : X) hx t


/-- **Enumerating the chambers of a cut system.**

The connected components of an open subset `F` of a locally connected second countable space are
open, pairwise disjoint and cover `F`; they are therefore countable (separability: a pairwise
disjoint family of nonempty open sets is countable) and can be enumerated.  The enumeration produced
here is a sequence `c : ℕ → Set U` whose members are *either* a component of `F` (hence connected,
nonempty and open) *or* the empty set, with `⋃ n, c n = F`.

A geometric construction of a cut system produces the components of `X ∖ S`; this lemma removes the
enumeration from the geometric obligation, so that the crux can be stated in component form. -/
theorem exists_enumeration_components {U : Type*} [TopologicalSpace U]
    [SecondCountableTopology U] [LocallyConnectedSpace U] {F : Set U} (hF : IsOpen F) :
    ∃ c : ℕ → Set U, (∀ n, IsOpen (c n)) ∧ (∀ n, IsPreconnected (c n)) ∧
      (∀ n, (c n).Nonempty → IsConnected (c n)) ∧ (∀ n, c n ⊆ F) ∧
      (∀ m n, m ≠ n → Disjoint (c m) (c n)) ∧ (⋃ n, c n) = F ∧
      (∀ n, c n = ∅ ∨ ∃ x ∈ F, c n = connectedComponentIn F x) := by
  classical
  set A : Set (Set U) := {K | ∃ x ∈ F, K = connectedComponentIn F x} with hA
  have hAopen : ∀ K ∈ A, IsOpen K := by
    rintro K ⟨x, _hx, rfl⟩
    exact hF.connectedComponentIn
  have hAne : ∀ K ∈ A, K.Nonempty := by
    rintro K ⟨x, hx, rfl⟩
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hAdisj : A.PairwiseDisjoint id := by
    intro K hK L hL hKL
    rcases hK with ⟨x, hx, rfl⟩
    rcases hL with ⟨y, hy, rfl⟩
    by_contra hnd
    obtain ⟨z, hzK, hzL⟩ := Set.not_disjoint_iff.mp hnd
    have h1 : connectedComponentIn F x = connectedComponentIn F z := connectedComponentIn_eq hzK
    have h2 : connectedComponentIn F y = connectedComponentIn F z := connectedComponentIn_eq hzL
    exact hKL (h1.trans h2.symm)
  have hAcnt : A.Countable := hAdisj.countable_of_isOpen hAopen hAne
  haveI : Countable {K : Set U // K ∈ A} := hAcnt.to_subtype
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat {K : Set U // K ∈ A}
  let c : ℕ → Set U := fun n =>
    if h : ∃ K : {K : Set U // K ∈ A}, f K = n then (Classical.choose h).1 else ∅
  have hc : ∀ n, c n = (if h : ∃ K : {K : Set U // K ∈ A}, f K = n then
      (Classical.choose h).1 else ∅) := fun n => rfl
  refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [hc n]
    by_cases h : ∃ K : {K : Set U // K ∈ A}, f K = n
    · rw [dif_pos h]
      exact hAopen _ (Classical.choose h).2
    · rw [dif_neg h]
      exact isOpen_empty
  · intro n
    rw [hc n]
    by_cases h : ∃ K : {K : Set U // K ∈ A}, f K = n
    · obtain ⟨x, _hx, hxK⟩ := (Classical.choose h).2
      rw [dif_pos h, hxK]
      exact isPreconnected_connectedComponentIn
    · rw [dif_neg h]
      exact isPreconnected_empty
  · intro n hne
    rw [hc n] at hne ⊢
    by_cases h : ∃ K : {K : Set U // K ∈ A}, f K = n
    · obtain ⟨x, _hx, hxK⟩ := (Classical.choose h).2
      rw [dif_pos h, hxK] at hne ⊢
      exact ⟨hne, isPreconnected_connectedComponentIn⟩
    · rw [dif_neg h] at hne
      exact absurd hne (by simp)
  · intro n
    rw [hc n]
    by_cases h : ∃ K : {K : Set U // K ∈ A}, f K = n
    · obtain ⟨x, _hx, hxK⟩ := (Classical.choose h).2
      rw [dif_pos h, hxK]
      exact connectedComponentIn_subset F x
    · rw [dif_neg h]
      exact Set.empty_subset F
  · intro m n hmn
    rw [hc m, hc n]
    by_cases hm : ∃ K : {K : Set U // K ∈ A}, f K = m
    · by_cases hn : ∃ K : {K : Set U // K ∈ A}, f K = n
      · rw [dif_pos hm, dif_pos hn]
        by_contra hnd
        obtain ⟨z, hz1, hz2⟩ := Set.not_disjoint_iff.mp hnd
        obtain ⟨x, _hx, hxK⟩ := (Classical.choose hm).2
        obtain ⟨y, _hy, hyK⟩ := (Classical.choose hn).2
        have h1 : connectedComponentIn F x = connectedComponentIn F z :=
          connectedComponentIn_eq (hxK ▸ hz1)
        have h2 : connectedComponentIn F y = connectedComponentIn F z :=
          connectedComponentIn_eq (hyK ▸ hz2)
        have heq : (Classical.choose hm : {K : Set U // K ∈ A}).1
            = (Classical.choose hn : {K : Set U // K ∈ A}).1 := by
          rw [hxK, hyK, h1, h2]
        have hsub : (Classical.choose hm : {K : Set U // K ∈ A}) = Classical.choose hn :=
          Subtype.ext heq
        have hmn' : m = n := by
          rw [← Classical.choose_spec hm, ← Classical.choose_spec hn, hsub]
        exact hmn hmn'
      · rw [dif_pos hm, dif_neg hn]
        simp
    · rw [dif_neg hm]
      simp
  · apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun n => ?_
      rw [hc n]
      by_cases h : ∃ K : {K : Set U // K ∈ A}, f K = n
      · obtain ⟨x, _hx, hxK⟩ := (Classical.choose h).2
        rw [dif_pos h, hxK]
        exact connectedComponentIn_subset F x
      · rw [dif_neg h]
        exact Set.empty_subset F
    · intro x hx
      have hcomp : connectedComponentIn F x ∈ A := ⟨x, hx, rfl⟩
      refine Set.mem_iUnion.mpr ⟨f ⟨connectedComponentIn F x, hcomp⟩, ?_⟩
      rw [hc _]
      have hpos : ∃ K : {K : Set U // K ∈ A}, f K = f ⟨connectedComponentIn F x, hcomp⟩ :=
        ⟨⟨connectedComponentIn F x, hcomp⟩, rfl⟩
      rw [dif_pos hpos]
      have hspec : f (Classical.choose hpos) = f ⟨connectedComponentIn F x, hcomp⟩ :=
        Classical.choose_spec hpos
      have heq : Classical.choose hpos = ⟨connectedComponentIn F x, hcomp⟩ := hf hspec
      rw [heq]
      exact mem_connectedComponentIn hx
  · intro n
    rw [hc n]
    by_cases h : ∃ K : {K : Set U // K ∈ A}, f K = n
    · right
      obtain ⟨x, hx, hxK⟩ := (Classical.choose h).2
      rw [dif_pos h]
      exact ⟨x, hx, hxK⟩
    · left
      rw [dif_neg h]

/-- **The frontier of a component of the complement of a closed set lies in the set** (in a locally
connected space).  If `z` were a frontier point of a component `C` of `Sᶜ` with `z ∈ Sᶜ`, then `z` lies
in the component of `z`, which is open, so a neighbourhood of `z` is inside it while also meeting `C`
(since `z ∈ closure C`), forcing the two components to coincide and `z` to be an interior point of `C`,
contradicting `z ∈ frontier C`. -/
theorem frontier_connectedComponentIn_compl_subset {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {S : Set X} (hS : IsClosed S) {x : X} (hx : x ∈ Sᶜ) :
    frontier (connectedComponentIn Sᶜ x) ⊆ S := by
  intro z hz
  by_contra hzS
  have hzU : z ∈ Sᶜ := hzS
  have hzmem : z ∈ connectedComponentIn Sᶜ z := mem_connectedComponentIn hzU
  have hopen : IsOpen (connectedComponentIn Sᶜ z) := hS.isOpen_compl.connectedComponentIn
  have hzcl : z ∈ closure (connectedComponentIn Sᶜ x) := hz.1
  obtain ⟨w, hw⟩ := mem_closure_iff.mp hzcl (interior (connectedComponentIn Sᶜ z))
    isOpen_interior (by rwa [hopen.interior_eq])
  obtain ⟨hwC', hwC⟩ := hw
  have h1 : connectedComponentIn Sᶜ z = connectedComponentIn Sᶜ w :=
    connectedComponentIn_eq (interior_subset hwC')
  have h2 : connectedComponentIn Sᶜ x = connectedComponentIn Sᶜ w := connectedComponentIn_eq hwC
  have heq : connectedComponentIn Sᶜ z = connectedComponentIn Sᶜ x := by rw [h1, h2]
  have hzint : z ∈ interior (connectedComponentIn Sᶜ x) := by
    rw [← heq, hopen.interior_eq]
    exact hzmem
  exact Set.disjoint_left.mp disjoint_interior_frontier hzint hz

/-- **Local finiteness of the components of the complement is automatic at points of the complement**:
a point of `Sᶜ` lies in exactly one component, and that component is open. -/
theorem exists_nhds_finite_components_of_mem_compl {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {S : Set X} (hS : IsClosed S) {x : X} (hx : x ∈ Sᶜ) :
    ∃ W ∈ 𝓝 x,
      {K : Set X | (∃ y ∈ Sᶜ, K = connectedComponentIn Sᶜ y) ∧ (K ∩ W).Nonempty}.Finite := by
  refine ⟨connectedComponentIn Sᶜ x, ?_, ?_⟩
  · exact (hS.isOpen_compl.connectedComponentIn).mem_nhds (mem_connectedComponentIn hx)
  · refine Set.Finite.subset (Set.finite_singleton (connectedComponentIn Sᶜ x)) ?_
    rintro K ⟨⟨y, _hy, rfl⟩, ⟨w, hwK, hwW⟩⟩
    have h1 : connectedComponentIn Sᶜ y = connectedComponentIn Sᶜ w := connectedComponentIn_eq hwK
    have h2 : connectedComponentIn Sᶜ x = connectedComponentIn Sᶜ w := connectedComponentIn_eq hwW
    simp only [Set.mem_singleton_iff]
    rw [h1, h2]

/-- **Cut-system data for a spine.**  `S ⊆ X` is a *locally finite one-sided cut system*: it is
closed, carries a CW structure without cells of dimension `≥ 2`, the connected components of its
complement are locally finite, their frontiers lie in `S`, and the closure of each component strongly
deformation retracts onto `S` (the one-sided collar condition).

This is the geometric input of the spine theorem, stated without any enumeration. -/
structure HasCutSystemData (X : Type*) [TopologicalSpace X] (S : Set X)
    (hS : @Topology.CWComplex X _ S) : Prop where
  /-- The spine is closed. -/
  closed' : IsClosed S
  /-- The CW structure has no cells of dimension `≥ 2`. -/
  cells_le_one : ∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ S hS n)
  /-- Frontiers of the chambers lie in the spine. -/
  frontier_subset : ∀ x ∈ Sᶜ, frontier (connectedComponentIn Sᶜ x) ⊆ S
  /-- Each chamber's closure strongly deformation retracts onto the spine. -/
  closure_retract : ∀ x ∈ Sᶜ, ∃ H : ↥(closure (connectedComponentIn Sᶜ x)) × unitInterval →
      ↥(closure (connectedComponentIn Sᶜ x)),
    Continuous H ∧ (∀ z, H (z, 0) = z) ∧ (∀ z, (H (z, 1) : X) ∈ S) ∧
    (∀ z : ↥(closure (connectedComponentIn Sᶜ x)), (z : X) ∈ S → ∀ t : unitInterval, H (z, t) = z)
  /-- The chambers are locally finite: only finitely many meet a small neighbourhood of any point. -/
  locallyFinite : ∀ x : X, ∃ W ∈ 𝓝 x,
    {K : Set X | (∃ y ∈ Sᶜ, K = connectedComponentIn Sᶜ y) ∧ (K ∩ W).Nonempty}.Finite

/-- **Cut-system data, reduced form.**  To produce `HasCutSystemData X S hS` it suffices to give the
CW structure (no cells of dimension `≥ 2`), the local finiteness of the chambers *at points of `S`*,
and the per-chamber closure retractions: closedness of `S` is automatic in a Hausdorff space, the
frontier condition is automatic in a locally connected space, and local finiteness at points of the
complement is automatic too. -/
theorem HasCutSystemData.of_reduced {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyConnectedSpace X] {S : Set X} {hS : @Topology.CWComplex X _ S}
    (hcell : ∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ S hS n))
    (hlf : ∀ x ∈ S, ∃ W ∈ 𝓝 x,
      {K : Set X | (∃ y ∈ Sᶜ, K = connectedComponentIn Sᶜ y) ∧ (K ∩ W).Nonempty}.Finite)
    (hret : ∀ x ∈ Sᶜ, ∃ H : ↥(closure (connectedComponentIn Sᶜ x)) × unitInterval →
        ↥(closure (connectedComponentIn Sᶜ x)),
      Continuous H ∧ (∀ z, H (z, 0) = z) ∧ (∀ z, (H (z, 1) : X) ∈ S) ∧
      (∀ z : ↥(closure (connectedComponentIn Sᶜ x)), (z : X) ∈ S → ∀ t : unitInterval, H (z, t) = z)) :
    HasCutSystemData X S hS := by
  have hScl : IsClosed S := Topology.RelCWComplex.isClosed (C := S) (D := (∅ : Set X))
  have hlf' : ∀ x : X, ∃ W ∈ 𝓝 x,
      {K : Set X | (∃ y ∈ Sᶜ, K = connectedComponentIn Sᶜ y) ∧ (K ∩ W).Nonempty}.Finite := by
    intro x
    by_cases hx : x ∈ S
    · exact hlf x hx
    · exact exists_nhds_finite_components_of_mem_compl hScl hx
  refine ⟨hScl, hcell, fun x hx => frontier_connectedComponentIn_compl_subset hScl hx, hret, hlf'⟩

/-- **Bridge: cut-system data ⟹ the enumerated chamber decomposition.**

The components of `X ∖ S` are enumerated by `exists_enumeration_components` (they are open, pairwise
disjoint and cover the complement, since `S` is closed and `X` is locally connected — for a charted
space this comes from the commons' `chartedSpace_stronglyLocallyContractible`), and the six clauses
transport: the two spare enumeration values are `∅`, whose frontier clause is vacuous and whose
closure retraction is the empty map. -/
theorem exists_chamber_data_of_hasCutSystemData {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyConnectedSpace X] {S : Set X}
    {hS : @Topology.CWComplex X _ S} (h : HasCutSystemData X S hS) :
    ∃ c : ℕ → Set X, (∀ m n, m ≠ n → Disjoint (c m) (c n)) ∧ (∀ n, Disjoint (c n) S) ∧
      ((⋃ n, c n) ∪ S = Set.univ) ∧ (∀ n, IsOpen (c n)) ∧
      (∀ n ⦃x : X⦄, x ∈ closure (c n) → x ∉ c n → x ∈ S) ∧
      (∀ x : X, ∃ W ∈ 𝓝 x, {n | (c n ∩ W).Nonempty}.Finite) ∧
      (∀ n, ∃ H : ↥(closure (c n)) × unitInterval → ↥(closure (c n)),
        Continuous H ∧ (∀ z, H (z, 0) = z) ∧ (∀ z, (H (z, 1) : X) ∈ S) ∧
        (∀ z : ↥(closure (c n)), (z : X) ∈ S → ∀ t : unitInterval, H (z, t) = z)) := by
  obtain ⟨hScl, _hdim, hfront, hH, hlf⟩ := h
  have hF : IsOpen Sᶜ := hScl.isOpen_compl
  obtain ⟨c, hcop, _hpre, _hconn, hcsub, hcdisj, hccov, hcchar⟩ :=
    exists_enumeration_components (F := Sᶜ) hF
  refine ⟨c, hcdisj, ?_, ?_, hcop, ?_, ?_, ?_⟩
  · intro n
    rw [Set.disjoint_left]
    intro x hx hxS
    exact hcsub n hx hxS
  · rw [hccov, Set.compl_union_self]
  · intro n x hxcl hxcn
    rcases hcchar n with hnil | ⟨y, hy, hyK⟩
    · rw [hnil] at hxcl
      simp at hxcl
    · rw [hyK] at hxcl hxcn
      have hfr : x ∈ frontier (connectedComponentIn Sᶜ y) := by
        have h2 : x ∉ interior (connectedComponentIn Sᶜ y) :=
          fun hmem => hxcn (interior_subset hmem)
        have hthis : x ∈ closure (connectedComponentIn Sᶜ y) \
            interior (connectedComponentIn Sᶜ y) := ⟨hxcl, h2⟩
        rwa [closure_sdiff_interior] at hthis
      exact hfront y hy hfr
  · intro x
    obtain ⟨W, hW, hfin⟩ := hlf x
    refine ⟨W, hW, ?_⟩
    have hinj : Set.InjOn c {n | (c n ∩ W).Nonempty} := by
      intro m hm n hn hmn
      by_contra hne
      obtain ⟨a, ha⟩ := hm
      exact Set.not_disjoint_iff.mpr ⟨a, ha.1, hmn ▸ ha.1⟩ (hcdisj m n hne)
    have hsub : c '' {n | (c n ∩ W).Nonempty} ⊆
        {K : Set X | (∃ y ∈ Sᶜ, K = connectedComponentIn Sᶜ y) ∧ (K ∩ W).Nonempty} := by
      rintro K ⟨n, hn, rfl⟩
      have hmem : ∃ y ∈ Sᶜ, c n = connectedComponentIn Sᶜ y := by
        rcases hcchar n with hnil | h
        · exfalso
          obtain ⟨z, hz⟩ := hn
          rw [hnil] at hz
          exact hz.1
        · exact h
      exact ⟨hmem, hn⟩
    exact (hfin.subset hsub).of_finite_image hinj
  · intro n
    rcases hcchar n with hnil | ⟨y, hy, hyK⟩
    · rw [hnil, closure_empty]
      haveI : IsEmpty (↥(∅ : Set X) × unitInterval) := inferInstance
      exact ⟨fun z => (IsEmpty.false z).elim,
        continuous_iff_continuousAt.mpr (fun z => (IsEmpty.false z).elim),
        (fun z => (IsEmpty.false z).elim), (fun z => (IsEmpty.false z).elim),
        (fun z _ t => (IsEmpty.false z).elim)⟩
    · rw [hyK]
      exact hH y hy


end Commons.Topology


namespace Commons.Topology.Homotopy

/-- **Local finiteness of a chamber decomposition is exactly the gluing engine's `hint` clause.**

If the chambers `c n` together with the spine `S` cover `U`, and the chamber decomposition is
*locally finite at every point* of `U` (equivalently: the chambers form a nested exhaustion of
`U ∖ S` — only finitely many of them meet a small neighbourhood of any point), then the
`hint` hypothesis of `Commons.Topology.Homotopy.deformationRetract_of_chamber_folds` holds.

This is the "easy half" of the cut-system programme: it lets a designer *check local finiteness*
(the natural geometric condition, automatic for the components of `U ∖ S` when `S` is a locally
finite cut system) instead of the awkward `hint` clause. -/
theorem hint_of_locallyFinite_chambers {U : Type*} [TopologicalSpace U] (c : ℕ → Set U)
    (S : Set U) (hcov : (⋃ n, c n) ∪ S = Set.univ)
    (hlf : ∀ x : U, ∃ W ∈ 𝓝 x, {n | (c n ∩ W).Nonempty}.Finite) :
    ∀ x : U, ∃ n, x ∈ interior ((⋃ i ∈ Finset.range n, closure (c i)) ∪ S) := by
  intro x
  obtain ⟨W, hW, hfin⟩ := hlf x
  set n := hfin.toFinset.sup id + 1 with hn
  have hWsub : W ⊆ (⋃ i ∈ Finset.range n, closure (c i)) ∪ S := by
    intro y hy
    by_cases hyS : y ∈ S
    · exact Or.inr hyS
    · have hyc : y ∈ (⋃ n, c n) ∪ S := by rw [hcov]; exact Set.mem_univ y
      rcases hyc with hyc | hyc
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hyc
        have hkfin : k ∈ hfin.toFinset := by
          rw [Set.Finite.mem_toFinset]; exact ⟨y, hk, hy⟩
        have hklt : k < n := by
          have := hfin.toFinset.le_sup (f := id) hkfin
          simp only [id_eq] at this
          omega
        exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hklt, subset_closure hk⟩)
      · exact absurd hyc hyS
  exact ⟨n, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hW hWsub)⟩

/-- **The easy half of the cut-system programme (assembled form).**

A locally finite chamber decomposition of `U` with spine `S` (chambers pairwise disjoint, disjoint
from `S`, covering `U ∖ S`, with frontiers in `S` and locally finite), together with a strong
deformation retraction of each chamber's *closure* onto `S`, yields a strong deformation retraction
of `U` onto `S`.

The per-chamber closures-to-`S` retractions are turned into *supported folds* by
`Commons.Topology.Homotopy.chamber_fold_of_closure_deformationRetract`, the local finiteness into the
engine's `hint` clause by `hint_of_locallyFinite_chambers`, and the folds are then pasted by
`Commons.Topology.Homotopy.deformationRetract_of_chamber_folds`. -/
theorem sdr_of_chamber_data {U : Type*} [TopologicalSpace U] (c : ℕ → Set U) (S : Set U)
    (hcdisj : ∀ m n, m ≠ n → Disjoint (c m) (c n)) (hcS : ∀ n, Disjoint (c n) S)
    (hcov : (⋃ n, c n) ∪ S = Set.univ) (hopen : ∀ n, IsOpen (c n))
    (hlf : ∀ x : U, ∃ W ∈ 𝓝 x, {n | (c n ∩ W).Nonempty}.Finite)
    (hbd : ∀ n ⦃x : U⦄, x ∈ closure (c n) → x ∉ c n → x ∈ S)
    (Hc : ∀ n, ∃ H : ↥(closure (c n)) × unitInterval → ↥(closure (c n)),
      Continuous H ∧ (∀ x, H (x, 0) = x) ∧ (∀ x, (H (x, 1) : U) ∈ S) ∧
      (∀ x : ↥(closure (c n)), (x : U) ∈ S → ∀ t : unitInterval, H (x, t) = x)) :
    ∃ H : U × unitInterval → U, Continuous H ∧ (∀ x, H (x, 0) = x) ∧
      (∀ x, H (x, 1) ∈ S) ∧ (∀ x, x ∈ S → ∀ t : unitInterval, H (x, t) = x) := by
  have key : ∀ n, ∃ Φ : U × unitInterval → U, Continuous Φ ∧ (∀ x, Φ (x, 0) = x) ∧
      (∀ x, x ∈ S → ∀ t : unitInterval, Φ (x, t) = x) ∧
      (∀ x, x ∉ c n → ∀ t : unitInterval, Φ (x, t) = x) ∧
      (∀ x, x ∈ c n → ∀ t : unitInterval, Φ (x, t) ∈ c n ∪ S) ∧
      (∀ x, x ∈ c n → Φ (x, 1) ∈ S) := by
    intro n
    obtain ⟨H, hHc, hH0, hH1, hHfix⟩ := Hc n
    exact chamber_fold_of_closure_deformationRetract (c n) S (hopen n) (hbd n) H hHc hH0 hH1 hHfix
  choose Φ hΦ using key
  exact deformationRetract_of_chamber_folds c S hcdisj hcS hbd
    (hint_of_locallyFinite_chambers c S hcov hlf) Φ (fun n => (hΦ n).1)
    (fun n x => (hΦ n).2.1 x) (fun n x hx t => (hΦ n).2.2.1 x hx t)
    (fun n x hx t => (hΦ n).2.2.2.1 x hx t) (fun n x hx t => (hΦ n).2.2.2.2.1 x hx t)
    (fun n x hx => (hΦ n).2.2.2.2.2 x hx)

/-- **The chamber-data hypothesis implies the CW-spine form of the geometric input** (with the
chamber data as an *existential* hypothesis, so that any producer of the data can use this). -/
theorem spine_geometric_input_of_chamber_data {X : Type*} [TopologicalSpace X]
    (h : ∃ (S : Set X) (hS : @Topology.CWComplex X _ S) (c : ℕ → Set X),
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ S hS n)) ∧
      (∀ m n, m ≠ n → Disjoint (c m) (c n)) ∧ (∀ n, Disjoint (c n) S) ∧
      ((⋃ n, c n) ∪ S = Set.univ) ∧ (∀ n, IsOpen (c n)) ∧
      (∀ n ⦃x : X⦄, x ∈ closure (c n) → x ∉ c n → x ∈ S) ∧
      (∀ x : X, ∃ W ∈ 𝓝 x, {n | (c n ∩ W).Nonempty}.Finite) ∧
      (∀ n, ∃ H : ↥(closure (c n)) × unitInterval → ↥(closure (c n)),
        Continuous H ∧ (∀ x, H (x, 0) = x) ∧ (∀ x, (H (x, 1) : X) ∈ S) ∧
        (∀ x : ↥(closure (c n)), (x : X) ∈ S → ∀ t : unitInterval, H (x, t) = x))) :
    ∃ (S : Set X) (hC : @Topology.CWComplex X _ S),
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ S hC n)) ∧
      ∃ H : X × unitInterval → X, Continuous H ∧ (∀ x : X, H (x, 0) = x) ∧
        (∀ x : X, H (x, 1) ∈ S) ∧ (∀ x : X, x ∈ S → ∀ t : unitInterval, H (x, t) = x) := by
  obtain ⟨S, hS, c, hdim, hcdisj, hcS, hcov, hopen, hbd, hlf, Hc⟩ := h
  obtain ⟨H, hHc, hH0, hH1, hHfix⟩ := sdr_of_chamber_data c S hcdisj hcS hcov hopen hlf hbd Hc
  exact ⟨S, hS, hdim, H, hHc, hH0, hH1, hHfix⟩

end Commons.Topology.Homotopy


namespace Commons.Topology.Surface

/-- **P1.0 — the locally finite closed refinement.**  Out of the topological star cover
(`Commons.Topology.Surface.exists_star_cover`) there is a locally finite closed cover of `X` by
nonempty connected compact sets.  No disk-ness and no interior-disjointness are used or produced;
this is the first refinement step of the topological disk tiling. -/
theorem exists_locallyFinite_closedCover_connectedCompact
    {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ConnectedSpace X]
    [ChartedSpace ℂ X] :
    ∃ (ι : Type) (C : ι → Set X), LocallyFinite C ∧ (⋃ i, C i = Set.univ) ∧
      (∀ i, IsClosed (C i)) ∧ (∀ i, (C i).Nonempty) ∧ (∀ i, IsCompact (C i)) ∧
      (∀ i, IsConnected (C i)) := by
  classical
  obtain ⟨x, e, s, r, _hee, hdata, hcov, hlf, hcl, _hstar⟩ := exists_star_cover (X := X)
  refine ⟨{n : ℕ // (r n).Nonempty}, fun i => r i.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hlf.comp_injective Subtype.val_injective
  · rw [eq_univ_iff_forall]
    intro y
    have hy : y ∈ ⋃ n, r n := by rw [hcov]; trivial
    obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨⟨n, ⟨y, hn⟩⟩, hn⟩
  · intro i; exact hcl i.1
  · intro i; exact i.2
  · intro i
    rcases hdata i.1 with h0 | ⟨hspos, hsub, hr⟩
    · exact absurd h0 i.2.ne_empty
    · show IsCompact (r i.1)
      rw [hr]
      exact (isCompact_closedBall ((e i.1) (x i.1)) (s i.1)).image_of_continuousOn
        ((e i.1).continuousOn_symm.mono hsub)
  · intro i
    rcases hdata i.1 with h0 | ⟨hspos, hsub, hr⟩
    · exact absurd h0 i.2.ne_empty
    · show IsConnected (r i.1)
      rw [hr]
      exact ((convex_closedBall ((e i.1) (x i.1)) (s i.1)).isConnected
          ⟨_, Metric.mem_closedBall_self (le_of_lt hspos)⟩).image ((e i.1).symm)
        ((e i.1).continuousOn_symm.mono hsub)

/-- **Rung 1 of the topological-surface layer (independent of `IsManifold`): the coordinate-disk
cover package.**

Out of `Commons.Topology.Surface.exists_star_cover` -- a locally finite cover of `X` by closed
coordinate disks whose overlapping members lie in a common chart, the only structural input
available for a surface that is merely `ChartedSpace ℂ X` -- we extract in one place all the data
that the later rungs of the spine construction consume:

* the members are compact closed disks lying in the source of their own chart (and are, nonempty,
  the homeomorphic image of a round closed ball of a chart, so they really are *disks*);
* any two intersecting members lie in a common chart (the *star* = planarity property);
* every member has finitely many neighbours, i.e. the intersection graph is locally finite;
* every clique of the intersection graph lies in the source of a single chart (planarity of
  clusters).

This is the rung everything above it sits on: the arc family of the spine is built by joining the
centres of neighbouring members, and both the local finiteness of that arc family and the planarity
of the charts in which its arcs are drawn come from the four properties above. -/
theorem exists_chartDiskCover_structure
    {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ConnectedSpace X]
    [ChartedSpace ℂ X] :
    ∃ (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (r : ℕ → Set X),
      (∀ n, e n ∈ atlas ℂ X) ∧
      (⋃ n, r n = Set.univ) ∧
      LocallyFinite r ∧
      (∀ n, IsClosed (r n)) ∧
      (∀ n, IsCompact (r n)) ∧
      (∀ n, r n ⊆ (e n).source) ∧
      (∀ n, (r n).Nonempty →
        ∃ (c : ℂ) (ρ : ℝ), 0 < ρ ∧ Metric.closedBall c ρ ⊆ (e n).target ∧
          r n = (e n).symm '' Metric.closedBall c ρ) ∧
      (∀ n m, (r n ∩ r m).Nonempty → r n ∪ r m ⊆ (e n).source ∩ (e m).source) := by
  -- RUNG PLAN of the topological-surface layer (each rung is a separate commons lemma; the ones
  -- marked DONE are proved here, the others are requested separately from the fleet):
  --
  -- R1  (DONE) `exists_chartDiskCover_structure`: a locally finite cover of `X` by compact closed
  --     chart disks, contained in their own chart, any two intersecting members lying in a common
  --     chart (the star/planarity property).
  -- R1b (DONE) `chartDiskCover_finite_neighbours`: every member has finitely many neighbours.
  -- R2a (DONE) `chartDiskCover_isPathConnected`: members are path connected.
  -- R2b (DONE) `chartDiskCover_joinedIn_union`: intersecting members are joined inside their union.
  -- R3a (requested: `Topology/exists_injective_path_between`) a path between distinct points of a
  --     Hausdorff space contains an injective arc (arc extraction).
  -- R3b (next, in this file) injective arcs joining the centres of neighbouring members, one per
  --     edge of a spanning structure of the (locally finite, connected) intersection graph.
  -- R3c (next) local finiteness of the arc family (uses R1b and the spanning structure).
  -- R3d (next) pairwise intersections of the arcs consist of common endpoints (the arcs are made
  --     radial in the charts, so arcs meeting in a member meet only at its centre).
  -- R4  (hard, the crux) the strong deformation retraction of `X` onto the union of the arcs.
  --     With R3a-R3d green this is precisely `spine_arc_input`, hence the reduction chain of this
  --     file collapses the target to R4 alone.
  classical
  obtain ⟨x, e, s, r, hatlas, hdata, hcov, hlf, hcl, hstar⟩ := exists_star_cover (X := X)
  have hcomp : ∀ n, IsCompact (r n) := by
    intro n
    rcases hdata n with h0 | ⟨hspos, hsub, hr⟩
    · rw [h0]; exact isCompact_empty
    · rw [hr]
      exact (isCompact_closedBall ((e n) (x n)) (s n)).image_of_continuousOn
        ((e n).continuousOn_symm.mono hsub)
  have hsub : ∀ n, r n ⊆ (e n).source := by
    intro n z hz
    rcases hdata n with h0 | ⟨hspos, hsubn, hr⟩
    · rw [h0] at hz; exact absurd hz (Set.notMem_empty z)
    · rw [hr] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact (e n).map_target (hsubn hy)
  refine ⟨x, e, r, hatlas, hcov, hlf, hcl, hcomp, hsub, ?_, hstar⟩
  intro n hn
  rcases hdata n with h0 | ⟨hspos, hsubn, hr⟩
  · rw [h0] at hn; exact absurd hn Set.not_nonempty_empty
  · exact ⟨(e n) (x n), s n, hspos, hsubn, hr⟩

/-- **Every member of the coordinate-disk cover has only finitely many neighbours** (so the
intersection graph of the cover is locally finite): a compact member can meet only finitely many
members of a locally finite family. -/
lemma chartDiskCover_finite_neighbours {X : Type*} [TopologicalSpace X] (r : ℕ → Set X)
    (hlf : LocallyFinite r) (hcomp : ∀ n, IsCompact (r n)) (n : ℕ) :
    {m : ℕ | (r m ∩ r n).Nonempty}.Finite :=
  hlf.finite_nonempty_inter_compact (hcomp n)

/-- **Rung 2a.**  Every member of the coordinate-disk cover is path connected: it is the
homeomorphic image of a round closed ball of a chart. -/
lemma chartDiskCover_isPathConnected {X : Type*} [TopologicalSpace X]
    {e : ℕ → OpenPartialHomeomorph X ℂ} {r : ℕ → Set X}
    (hdisk : ∀ n, (r n).Nonempty →
      ∃ (c : ℂ) (ρ : ℝ), 0 < ρ ∧ Metric.closedBall c ρ ⊆ (e n).target ∧
        r n = (e n).symm '' Metric.closedBall c ρ)
    {n : ℕ} (hn : (r n).Nonempty) : IsPathConnected (r n) := by
  obtain ⟨c, ρ, hρ, hsub, hr⟩ := hdisk n hn
  rw [hr]
  exact ((convex_closedBall c ρ).isPathConnected ⟨c, Metric.mem_closedBall_self hρ.le⟩).image'
    ((e n).continuousOn_symm.mono hsub)

/-- **Rung 2b.**  Any two intersecting members of the coordinate-disk cover are joined inside their
union.  This is what the arc family of the spine is built from: composing with the
arc-extraction lemma (`exists_injective_path_between`: a path between distinct points of a Hausdorff
space contains an injective arc) turns it into an injective arc between chosen points of the two
members. -/
lemma chartDiskCover_joinedIn_union {X : Type*} [TopologicalSpace X]
    {e : ℕ → OpenPartialHomeomorph X ℂ} {r : ℕ → Set X}
    (hdisk : ∀ n, (r n).Nonempty →
      ∃ (c : ℂ) (ρ : ℝ), 0 < ρ ∧ Metric.closedBall c ρ ⊆ (e n).target ∧
        r n = (e n).symm '' Metric.closedBall c ρ)
    {n m : ℕ} (h : (r n ∩ r m).Nonempty) {a b : X} (ha : a ∈ r n) (hb : b ∈ r m) :
    JoinedIn (r n ∪ r m) a b := by
  have hpn : IsPathConnected (r n) := chartDiskCover_isPathConnected hdisk ⟨a, ha⟩
  have hpm : IsPathConnected (r m) := chartDiskCover_isPathConnected hdisk ⟨b, hb⟩
  exact (hpn.union hpm h).joinedIn a (Or.inl ha) b (Or.inr hb)

-- NOTE (rung 1, next step): the *planarity of clusters* consequence
-- (a finite subfamily whose members pairwise meet lies in the source of one chart; it follows from
-- `hstar` by picking a member of the subfamily) is recorded here as the next rung to formalise --
-- its natural statement is
--   `∀ S : Finset ℕ, (∀ n m, n ∈ (S : Set ℕ) → m ∈ (S : Set ℕ) → n ≠ m → (r n ∩ r m).Nonempty) →
--      ∃ n, (⋃ m ∈ S, r m) ⊆ (e n).source`
-- and it is the input that makes each *cluster* of the cover planar (a subset of ℂ), which is what
-- lets the planar machinery be run inside a cluster.

/-- **The remaining geometric content, in "local data" form.**

This isolates *exactly* what is still missing for the target: a locally finite closed
cover `K` of the surface with the folds `φ i` needed by the gluing engine
`Commons.Topology.Homotopy.exists_sdr_of_locallyFinite_closed_cover_folds`.  Mathematically this is
the classical statement "a non-compact surface is a regular neighbourhood of a locally finite
graph" (equivalently: it has a locally finite handle decomposition whose 1-handles account for all
of the topology); see `NOTES_spine_sharp_obstructions.md` for the obstructions that any
construction must respect (the H₂ obstruction forces every piece to keep a *free* boundary arc, and
the chart transitions being merely homeomorphisms force the shared boundary arcs to be chosen by
hand).

It is stated in a space-agnostic form (no surface hypotheses) so that it is a clean target for the
commons. -/
theorem spine_geometric_input_of_local_data
    {X : Type*} [TopologicalSpace X]
    (h : ∃ (ι : Type) (K : ι → Set X) (S : Set X) (hS : @Topology.CWComplex X _ S),
      LocallyFinite K ∧ (⋃ i, K i) = Set.univ ∧ (∀ i, IsClosed (K i)) ∧
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ S hS n)) ∧
      (∀ i j, i ≠ j → K i ∩ K j ⊆ S) ∧
      ∃ φ : ∀ i, X × unitInterval → X,
        (∀ i, ContinuousOn (φ i) (K i ×ˢ (Set.univ : Set unitInterval))) ∧
        (∀ i (x : X), x ∈ K i → φ i (x, 0) = x) ∧
        (∀ i (x : X), x ∈ K i → φ i (x, 1) ∈ K i ∧ φ i (x, 1) ∈ S) ∧
        (∀ i (x : X), x ∈ S → ∀ t : unitInterval, φ i (x, t) = x)) :
    ∃ (S : Set X) (hC : @Topology.CWComplex X _ S),
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ S hC n)) ∧
      ∃ H : X × unitInterval → X, Continuous H ∧ (∀ x : X, H (x, 0) = x) ∧
        (∀ x : X, H (x, 1) ∈ S) ∧ (∀ x : X, x ∈ S → ∀ t : unitInterval, H (x, t) = x) := by
  obtain ⟨ι, K, S, hS, hlf, hcov, hcl, hdim, hpair, φ, hφc, hφ0, hφ1, hφfix⟩ := h
  exact Commons.Topology.Homotopy.exists_sdr_of_locallyFinite_closed_cover_folds
    K S hcl hlf hcov hpair hS hdim φ hφc hφ0 hφ1 hφfix


/-- **The (missing) cut-system core.**  A connected, second countable, non-compact surface admits a
locally finite one-sided cut system: a subspace `S` carrying a CW structure with no cells of
dimension `≥ 2`, whose complement's components are locally finite at points of `S` and whose closures
strongly deformation retract onto `S`.

This is the *only* geometric input of the spine theorem, and it is **not proved here**: its
classical proofs run through Radó's triangulability of topological 2-manifolds (or through
smoothness plus a proper Morse function with no local maximum), neither of which is available.
Everything below is therefore stated with `HasCutSystemCore X` as an explicit hypothesis, so that
the whole reduction -- cut system ⟹ cut-system data ⟹ enumerated chamber data ⟹ the spine
statement -- is available to whoever supplies that input (in the smooth case from the project's
disk tiling together with the fold machinery). -/
def HasCutSystemCore (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ (S : Set X) (hS : @Topology.CWComplex X _ S),
    (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ S hS n)) ∧
    (∀ x ∈ S, ∃ W ∈ 𝓝 x,
      {K : Set X | (∃ y ∈ Sᶜ, K = connectedComponentIn Sᶜ y) ∧ (K ∩ W).Nonempty}.Finite) ∧
    (∀ x ∈ Sᶜ, ∃ H : ↥(closure (connectedComponentIn Sᶜ x)) × unitInterval →
        ↥(closure (connectedComponentIn Sᶜ x)),
      Continuous H ∧ (∀ z, H (z, 0) = z) ∧ (∀ z, (H (z, 1) : X) ∈ S) ∧
      (∀ z : ↥(closure (connectedComponentIn Sᶜ x)), (z : X) ∈ S → ∀ t : unitInterval, H (z, t) = z))


/-- The cut-system crux in the assembled form `HasCutSystemData`, *derived* from the reduced crux
`exists_cutSystemCore_of_surface` by `Commons.Topology.hasCutSystemData_of_reduced`. -/
theorem exists_cutSystem_of_surface_of_core {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X] (hX : ¬ CompactSpace X)
    (h : HasCutSystemCore X) :
    ∃ (S : Set X) (hS : @Topology.CWComplex X _ S), HasCutSystemData X S hS := by
  obtain ⟨S, hS, hcell, hlf, hret⟩ := h
  haveI : StronglyLocallyContractibleSpace X :=
    Commons.Topology.Charts.chartedSpace_stronglyLocallyContractible
  haveI : LocallyConnectedSpace X := inferInstance
  exact ⟨S, hS, HasCutSystemData.of_reduced hcell hlf hret⟩

/-- The **enumerated form** of the cut-system crux, *derived* from `exists_cutSystem_of_surface`:
this is the interface consumed by the gluing engines (it is what
`Commons.Topology.Homotopy.sdr_of_chamber_data` and
`spine_geometric_input_of_chamber_data` take as input). -/
theorem exists_chamber_data_of_surface_of_core {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X] (hX : ¬ CompactSpace X)
    (h : HasCutSystemCore X) :
    ∃ (S : Set X) (hS : @Topology.CWComplex X _ S) (c : ℕ → Set X),
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ S hS n)) ∧
      (∀ m n, m ≠ n → Disjoint (c m) (c n)) ∧ (∀ n, Disjoint (c n) S) ∧
      ((⋃ n, c n) ∪ S = Set.univ) ∧ (∀ n, IsOpen (c n)) ∧
      (∀ n ⦃x : X⦄, x ∈ closure (c n) → x ∉ c n → x ∈ S) ∧
      (∀ x : X, ∃ W ∈ 𝓝 x, {n | (c n ∩ W).Nonempty}.Finite) ∧
      (∀ n, ∃ H : ↥(closure (c n)) × unitInterval → ↥(closure (c n)),
        Continuous H ∧ (∀ x, H (x, 0) = x) ∧ (∀ x, (H (x, 1) : X) ∈ S) ∧
        (∀ x : ↥(closure (c n)), (x : X) ∈ S → ∀ t : unitInterval, H (x, t) = x)) := by
  obtain ⟨S, hS, hdata⟩ := exists_cutSystem_of_surface_of_core (X := X) hX h
  haveI : StronglyLocallyContractibleSpace X :=
    Commons.Topology.Charts.chartedSpace_stronglyLocallyContractible
  haveI : LocallyConnectedSpace X := inferInstance
  obtain ⟨c, h1, h2, h3, h4, h5, h6, h7⟩ := exists_chamber_data_of_hasCutSystemData hdata
  exact ⟨S, hS, c, hdata.cells_le_one, h1, h2, h3, h4, h5, h6, h7⟩


theorem spine_of_noncompact_surface_of_core
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] (hX : ¬ CompactSpace X) (h : HasCutSystemCore X) :
    ∃ (G : Set X) (hC : @Topology.CWComplex ↥G _ Set.univ),
      (∀ n : ℕ, Countable (@Topology.CWComplex.cell ↥G _ Set.univ hC n)) ∧
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell ↥G _ Set.univ hC n)) ∧
      Nonempty (ContinuousMap.HomotopyEquiv X ↥G) := by
  obtain ⟨S, hC, hdim, H, hHcont, hH0, hH1, hHfix⟩ :=
    Commons.Topology.Homotopy.spine_geometric_input_of_chamber_data (X := X)
      (exists_chamber_data_of_surface_of_core (X := X) hX h)
  have hScl : IsClosed S := Topology.RelCWComplex.isClosed (C := S) (D := (∅ : Set X))
  obtain ⟨hC', hC'mono⟩ := Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace hScl hC
  refine ⟨S, hC', ?_, ?_, ?_⟩
  · intro n
    exact Commons.Topology.CWComplex.countable_cell_of_secondCountable hC' n
  · intro n hn
    exact hC'mono n (hdim n hn)
  · exact Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract S H hHcont hH0 hH1 hHfix

/-- Every member of a locally finite family of compact sets meets only finitely many others.
Applied to the star cover (`Commons.Topology.Surface.exists_star_cover`) this says that each boundary
circle `∂(r n)` crosses only finitely many other boundary circles, so the wall system `⋃ n, ∂(r n)`
is a locally finite union of Jordan curves with locally finite crossings -- the structural fact
behind every "cut system" design for the topological spine. -/
lemma finite_neighbours_of_starCover {X : Type*} [TopologicalSpace X] (r : ℕ → Set X)
    (hlf : LocallyFinite r) (hcomp : ∀ n, IsCompact (r n)) (n : ℕ) :
    {m : ℕ | (r m ∩ r n).Nonempty}.Finite :=
  hlf.finite_nonempty_inter_compact (hcomp n)

end Commons.Topology.Surface

namespace Commons.Topology.Plane


/-- Determinant (cross product) of two complex numbers viewed as vectors of `ℝ²`. -/
def cdet (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

/-- The two-legged `V` with apex `c` through `a` and `b`. -/
def vLegs (a b c : ℂ) : Set ℂ := segment ℝ c a ∪ segment ℝ c b

lemma cdet_self (u : ℂ) : cdet u u = 0 := by simp only [cdet]; ring

lemma cdet_add_left (u₁ u₂ v : ℂ) : cdet (u₁ + u₂) v = cdet u₁ v + cdet u₂ v := by
  simp only [cdet, Complex.add_re, Complex.add_im]; ring

lemma cdet_add_right (u v₁ v₂ : ℂ) : cdet u (v₁ + v₂) = cdet u v₁ + cdet u v₂ := by
  simp only [cdet, Complex.add_re, Complex.add_im]; ring

lemma cdet_sub_left (u₁ u₂ v : ℂ) : cdet (u₁ - u₂) v = cdet u₁ v - cdet u₂ v := by
  simp only [cdet, Complex.sub_re, Complex.sub_im]; ring

lemma cdet_sub_right (u v₁ v₂ : ℂ) : cdet u (v₁ - v₂) = cdet u v₁ - cdet u v₂ := by
  simp only [cdet, Complex.sub_re, Complex.sub_im]; ring

lemma cdet_smul_left (r : ℝ) (u v : ℂ) : cdet (r • u) v = r * cdet u v := by
  have h1 : (r • u).re = r * u.re := by simpa using (Complex.reCLM.map_smul r u)
  have h2 : (r • u).im = r * u.im := by simpa using (Complex.imCLM.map_smul r u)
  simp only [cdet, h1, h2]; ring

lemma cdet_smul_right (r : ℝ) (u v : ℂ) : cdet u (r • v) = r * cdet u v := by
  have h1 : (r • v).re = r * v.re := by simpa using (Complex.reCLM.map_smul r v)
  have h2 : (r • v).im = r * v.im := by simpa using (Complex.imCLM.map_smul r v)
  simp only [cdet, h1, h2]; ring

/-- **Distinct legs meet only at the centre.**  Two segments emanating from the same point `c` whose
directions are linearly independent (`cdet (a-c) (b-c) ≠ 0`) meet only at `c`.  This is the second
separation hypothesis of the tile fold: it is discharged by choosing the gates with distinct directions
from the tile centre. -/
theorem segment_inter_segment_of_cdet_ne_zero {c a b : ℂ}
    (hdet : cdet (a - c) (b - c) ≠ 0) :
    segment ℝ c a ∩ segment ℝ c b = {c} := by
  classical
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨hxa, hxb⟩
    simp only [segment_eq_image] at hxa hxb
    obtain ⟨s, -, rfl⟩ := hxa
    obtain ⟨t, -, hst⟩ := hxb
    have hEq : s • (a - c) = t • (b - c) := by
      have h' := congrArg (fun z : ℂ => z - c) hst
      have h1 : ((1 - s) • c + s • a) - c = s • (a - c) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      have h2 : ((1 - t) • c + t • b) - c = t • (b - c) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      rw [h1, h2] at h'
      exact h'.symm
    have hzero : s * cdet (a - c) (b - c) = 0 := by
      have h' := congrArg (fun u : ℂ => cdet u (b - c)) hEq
      rwa [cdet_smul_left, cdet_smul_left, cdet_self, mul_zero] at h'
    have hs0 : s = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact h
      · exact absurd h hdet
    subst hs0
    simp
  · rintro x hx
    rw [mem_singleton_iff] at hx
    rw [hx]
    exact ⟨left_mem_segment ℝ c a, left_mem_segment ℝ c b⟩

/-- **The `V`-fold.** A convex plane region `Q` strongly deformation retracts onto the two-legged
`V` with apex `c` through `a`, `b ∈ Q`, fixing the `V` pointwise, provided the directions `a - c`
and `b - c` are linearly independent over `ℝ` (i.e. the `V` is non-degenerate). -/
theorem exists_foldMap_vLegs {Q : Set ℂ} (hQ : Convex ℝ Q) {a b c : ℂ}
    (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q)
    (hdet : cdet (a - c) (b - c) ≠ 0) :
    ∃ ψ : ℂ → ℂ, Continuous ψ ∧ (∀ z ∈ Q, ψ z ∈ vLegs a b c) ∧
      (∀ z ∈ vLegs a b c, ψ z = z) ∧ (∀ z ∈ Q, segment ℝ z (ψ z) ⊆ Q) := by
  classical
  set d : ℝ := cdet (a - c) (b - c) with hd
  have hd0 : d ≠ 0 := hdet
  set lam : ℂ → ℝ := fun z => cdet (z - c) (b - c) / d with hlam
  set mu : ℂ → ℝ := fun z => cdet (a - c) (z - c) / d with hmu
  have hcont1 : Continuous fun z : ℂ => cdet (z - c) (b - c) := by
    simp only [cdet]; fun_prop
  have hcont2 : Continuous fun z : ℂ => cdet (a - c) (z - c) := by
    simp only [cdet]; fun_prop
  have hlam_c : Continuous lam := by rw [hlam]; exact hcont1.div_const d
  have hmu_c : Continuous mu := by rw [hmu]; exact hcont2.div_const d
  set psi : ℂ → ℂ := fun z =>
      c + (min 1 (max 0 (lam z - mu z))) • (a - c)
        + (min 1 (max 0 (mu z - lam z))) • (b - c) with hpsi
  have hpsi_c : Continuous psi := by
    rw [hpsi]
    refine (continuous_const.add ?_).add ?_
    · exact ((continuous_const.min (continuous_const.max (hlam_c.sub hmu_c))).smul continuous_const)
    · exact ((continuous_const.min (continuous_const.max (hmu_c.sub hlam_c))).smul continuous_const)
  -- coordinates of a point of the form `c + s • (a - c) + t • (b - c)`
  have hlam_pt : ∀ s t : ℝ, lam (c + s • (a - c) + t • (b - c)) = s := by
    intro s t
    have h1 : c + s • (a - c) + t • (b - c) - c = s • (a - c) + t • (b - c) := by
      rw [add_assoc, add_sub_cancel_left]
    have h2 : cdet (s • (a - c) + t • (b - c)) (b - c) = s * d := by
      rw [cdet_add_left, cdet_smul_left, cdet_smul_left, cdet_self (b - c), mul_zero, add_zero, hd]
    rw [hlam]
    simp only [h1, h2]
    rw [mul_div_assoc, div_self hd0, mul_one]
  have hmu_pt : ∀ s t : ℝ, mu (c + s • (a - c) + t • (b - c)) = t := by
    intro s t
    have h1 : c + s • (a - c) + t • (b - c) - c = s • (a - c) + t • (b - c) := by
      rw [add_assoc, add_sub_cancel_left]
    have h2 : cdet (a - c) (s • (a - c) + t • (b - c)) = t * d := by
      rw [cdet_add_right, cdet_smul_right, cdet_smul_right, cdet_self (a - c), mul_zero, zero_add, hd]
    rw [hmu]
    simp only [h1, h2]
    rw [mul_div_assoc, div_self hd0, mul_one]
  -- the fold lands on the `V`
  have hpsi_mem : ∀ z : ℂ, psi z ∈ vLegs a b c := by
    intro z
    have h1 : 0 ≤ min 1 (max 0 (lam z - mu z)) := le_min (by norm_num) (le_max_left _ _)
    have h2 : min 1 (max 0 (lam z - mu z)) ≤ 1 := min_le_left _ _
    by_cases hle : mu z ≤ lam z
    · have hz : min 1 (max 0 (mu z - lam z)) = 0 := by
        rw [max_eq_left (by linarith : mu z - lam z ≤ 0)]
        exact min_eq_right zero_le_one
      have hmem : psi z = c + (min 1 (max 0 (lam z - mu z))) • (a - c) := by
        rw [hpsi]
        simp only [hz, zero_smul, add_zero]
      rw [hmem]
      refine Or.inl ?_
      rw [segment_eq_image']
      exact ⟨min 1 (max 0 (lam z - mu z)), ⟨h1, h2⟩, rfl⟩
    · have hle' : lam z ≤ mu z := le_of_not_ge hle
      have h1' : 0 ≤ min 1 (max 0 (mu z - lam z)) := le_min (by norm_num) (le_max_left _ _)
      have h2' : min 1 (max 0 (mu z - lam z)) ≤ 1 := min_le_left _ _
      have hz : min 1 (max 0 (lam z - mu z)) = 0 := by
        rw [max_eq_left (by linarith : lam z - mu z ≤ 0)]
        exact min_eq_right zero_le_one
      have hmem : psi z = c + (min 1 (max 0 (mu z - lam z))) • (b - c) := by
        rw [hpsi]
        simp only [hz, zero_smul, zero_add, add_zero]
      rw [hmem]
      refine Or.inr ?_
      rw [segment_eq_image']
      exact ⟨min 1 (max 0 (mu z - lam z)), ⟨h1', h2'⟩, rfl⟩
  -- the fold fixes the `V`
  have hfix : ∀ z ∈ vLegs a b c, psi z = z := by
    intro z hz
    rcases hz with hz | hz
    · rw [segment_eq_image'] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      have hmu0 : mu (c + r • (a - c)) = 0 := by
        simpa using hmu_pt r 0
      have hlam_r : lam (c + r • (a - c)) = r := by
        simpa using hlam_pt r 0
      have hmax1 : max 0 (lam (c + r • (a - c)) - mu (c + r • (a - c))) = r := by
        rw [hlam_r, hmu0, sub_zero]; exact max_eq_right hr.1
      have hmax2 : max 0 (mu (c + r • (a - c)) - lam (c + r • (a - c))) = 0 := by
        rw [hlam_r, hmu0, zero_sub]; exact max_eq_left (neg_nonpos.mpr hr.1)
      rw [hpsi]
      simp only [hmax1, hmax2, min_eq_right zero_le_one, min_eq_right hr.2, zero_smul, add_zero]
    · rw [segment_eq_image'] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      have hlam0 : lam (c + r • (b - c)) = 0 := by
        simpa using hlam_pt 0 r
      have hmu_r : mu (c + r • (b - c)) = r := by
        simpa using hmu_pt 0 r
      have hmax1 : max 0 (lam (c + r • (b - c)) - mu (c + r • (b - c))) = 0 := by
        rw [hlam0, hmu_r, zero_sub]; exact max_eq_left (neg_nonpos.mpr hr.1)
      have hmax2 : max 0 (mu (c + r • (b - c)) - lam (c + r • (b - c))) = r := by
        rw [hlam0, hmu_r, sub_zero]; exact max_eq_right hr.1
      rw [hpsi]
      simp only [hmax1, hmax2, min_eq_right zero_le_one, min_eq_right hr.2, zero_smul, add_zero]
  have hpsiQ : ∀ z ∈ Q, psi z ∈ Q := by
    intro z _
    rcases hpsi_mem z with h | h
    · exact hQ.segment_subset hc ha h
    · exact hQ.segment_subset hc hb h
  exact ⟨psi, hpsi_c, fun z _ => hpsi_mem z, hfix,
    fun z hz => hQ.segment_subset hz (hpsiQ z hz)⟩

/-- The closed convex cone (sector) with apex `c` spanned by `a - c` and `b - c`. -/
def wedge (a b c : ℂ) : Set ℂ :=
  {z | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ c + s • (a - c) + t • (b - c) = z}

theorem convex_wedge (a b c : ℂ) : Convex ℝ (wedge a b c) := by
  rintro x ⟨s, t, hs, ht, rfl⟩ y ⟨s', t', hs', ht', rfl⟩ k l hk hl hkl
  refine ⟨k * s + l * s', k * t + l * t', by positivity, by positivity, ?_⟩
  have hexp : k • (c + s • (a - c) + t • (b - c)) + l • (c + s' • (a - c) + t' • (b - c))
      = (k + l) • c + (k * s + l * s') • (a - c) + (k * t + l * t') • (b - c) := by
    simp only [smul_add, smul_smul]
    module
  rw [hexp, hkl, one_smul]

theorem mem_wedge_self_left (a b c : ℂ) : a ∈ wedge a b c :=
  ⟨1, 0, zero_le_one, le_rfl, by simp⟩

theorem mem_wedge_self_right (a b c : ℂ) : b ∈ wedge a b c :=
  ⟨0, 1, le_rfl, zero_le_one, by simp⟩

theorem mem_wedge_apex (a b c : ℂ) : c ∈ wedge a b c :=
  ⟨0, 0, le_rfl, le_rfl, by simp⟩

/-- **Sector clamping with the segment clause.**  Inside the closed sector (wedge) with apex `c`
spanned by `a - c` and `b - c`, the `V`-fold of `exists_foldMap_vLegs` clamps every point into the
`V` and its displacement segment stays inside the sector.  This is the first-leg (`A 0 → A 1`) step of
the star-convex fold: convexity of the sector supplies exactly the segment clause that a merely
star-shaped ambient cannot. -/
theorem exists_clamp_wedge {a b c : ℂ} (hdet : cdet (a - c) (b - c) ≠ 0) :
    ∃ ψ : ℂ → ℂ, Continuous ψ ∧ (∀ z ∈ wedge a b c, ψ z ∈ vLegs a b c) ∧
      (∀ z ∈ vLegs a b c, ψ z = z) ∧
      ∀ z ∈ wedge a b c, segment ℝ z (ψ z) ⊆ wedge a b c := by
  obtain ⟨ψ, hψc, hψv, hψfix, hψseg⟩ :=
    exists_foldMap_vLegs (convex_wedge a b c) (mem_wedge_self_left a b c)
      (mem_wedge_self_right a b c) (mem_wedge_apex a b c) hdet
  exact ⟨ψ, hψc, hψv, hψfix, fun z hz => hψseg z hz⟩

/-- **The `V`-fold, strong deformation retraction form.**  A convex plane region strongly
deformation retracts onto a two-legged `V` through an apex, fixing it. -/
theorem vLegs_deformationRetract {Q : Set ℂ} (hQ : Convex ℝ Q) {a b c : ℂ}
    (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q)
    (hdet : cdet (a - c) (b - c) ≠ 0) :
    ∃ H : ↥Q × unitInterval → ↥Q, Continuous H ∧ (∀ x : ↥Q, H (x, 0) = x) ∧
      (∀ x : ↥Q, (H (x, 1) : ℂ) ∈ vLegs a b c) ∧
      (∀ x : ↥Q, (x : ℂ) ∈ vLegs a b c → ∀ t : unitInterval, H (x, t) = x) := by
  obtain ⟨ψ, hc, hm, hf, hseg⟩ := exists_foldMap_vLegs hQ ha hb hc hdet
  exact closure_deformationRetract_of_starShaped Q (vLegs a b c) ψ hc hm hf hseg

/-- A non-degenerate two-legged `V` is a **retract of the plane** (the clamped fold of
`exists_foldMap_vLegs`, taken over `Q = univ`).  Together with `convex_tree_retract` this makes
every "convex tree" (a `U`/spider of edges) an absolute retract, whence `a convex tile folds onto
it` (`convex_deformationRetract_of_isRetract`) -- the elementary-collapse atom of the PL layer. -/
theorem isRetract_vLegs {a b c : ℂ} (hdet : cdet (a - c) (b - c) ≠ 0) :
    IsRetract (vLegs a b c) := by
  obtain ⟨ψ, hc, hm, hf, _⟩ :=
    exists_foldMap_vLegs (Q := Set.univ) convex_univ (mem_univ a) (mem_univ b) (mem_univ c) hdet
  refine ⟨⟨fun z => ⟨ψ z, hm z (mem_univ z)⟩, hc.subtype_mk _⟩, ?_⟩
  intro x
  exact Subtype.ext (hf x x.2)


/-- **A convex plane region folds onto any retract of `ℂ` contained in it.**  If `S ⊆ Q` and `S`
is a retract of `ℂ` (e.g. a "convex tree": a union of straight segments forming a tree), then `Q`
strongly deformation retracts onto `S`, fixing `S`, with straight tracks.  This is the general
"spider/per-cell fold" atom of the planar cut-system designs. -/
theorem convex_deformationRetract_of_isRetract {Q S : Set ℂ} (hQ : Convex ℝ Q) (hS : S ⊆ Q)
    (h : IsRetract S) :
    ∃ H : ↥Q × unitInterval → ↥Q, Continuous H ∧ (∀ x : ↥Q, H (x, 0) = x) ∧
      (∀ x : ↥Q, (H (x, 1) : ℂ) ∈ S) ∧
      (∀ x : ↥Q, (x : ℂ) ∈ S → ∀ t : unitInterval, H (x, t) = x) := by
  obtain ⟨r, hr⟩ := h
  have hcont : Continuous fun z : ℂ => (r z : ℂ) := continuous_subtype_val.comp r.continuous
  refine closure_deformationRetract_of_starShaped Q S (fun z => (r z : ℂ)) hcont ?_ ?_ ?_
  · intro z _
    exact (r z).2
  · intro z hz
    exact congrArg Subtype.val (hr ⟨z, hz⟩)
  · intro z hz
    exact hQ.segment_subset hz (hS (r z).2)

/-- **Elementary collapse of a convex tile onto a sub-tree of its 1-skeleton.**  If `A 0, …, A n`
are convex pieces of a convex tile `Q` whose successive `accumulate`s meet the next piece in a
convex non-empty set (a "convex tree": a `U`, a spider of edges, …), then `Q` strongly deformation
retracts onto their union.  This is the per-cell fold of the PL-collapse atom: a 2-cell collapses
onto a spanning subtree of its boundary. -/
theorem convex_deformationRetract_of_convexTree {Q : Set ℂ} (hQ : Convex ℝ Q) {A : ℕ → Set ℂ}
    {N : ℕ} (hsub : ∀ k, A k ⊆ Q) (hconv : ∀ k, Convex ℝ (A k)) (hcl : ∀ k, IsClosed (A k))
    (hne : ∀ k, (A k).Nonempty)
    (hint : ∀ k, k + 1 < N → Convex ℝ (Set.accumulate A k ∩ A (k + 1)))
    (hintne : ∀ k, k + 1 < N → (Set.accumulate A k ∩ A (k + 1)).Nonempty)
    {n : ℕ} (hn : n < N) :
    ∃ H : ↥Q × unitInterval → ↥Q, Continuous H ∧ (∀ x : ↥Q, H (x, 0) = x) ∧
      (∀ x : ↥Q, (H (x, 1) : ℂ) ∈ Set.accumulate A n) ∧
      (∀ x : ↥Q, (x : ℂ) ∈ Set.accumulate A n → ∀ t : unitInterval, H (x, t) = x) := by
  have hR : IsRetract (Set.accumulate A n) :=
    convex_tree_retract N hconv hcl hne hint hintne n hn
  have hsub' : ∀ n, Set.accumulate A n ⊆ Q := by
    intro n
    induction n with
    | zero => simpa using hsub 0
    | succ m ih => rw [Set.accumulate_succ]; exact Set.union_subset ih (hsub (m + 1))
  exact convex_deformationRetract_of_isRetract hQ (hsub' n) hR

/-- **The convexity-free accumulator.**  A convex plane region `Q` deformation retracts onto the
accumulate of a chain `A` whose members and consecutive meets are merely *retracts of `ℂ`* — no
convexity of the chain members is needed.  This is what makes the tile fold applicable to **walls that
are arcs of a sphere**: `W = D i ∩ D p` sits in `∂(D i)`, hence is not convex in the chart, but it is a
retract of the plane, and the meets in the chain `A 0 = W`, `A (k+1) = [c, g k]` are the singletons
`{g 0}` and `{c}`. -/
theorem deformationRetract_of_retractTree {Q : Set ℂ} (hQ : Convex ℝ Q) {A : ℕ → Set ℂ}
    (hsub : ∀ k, A k ⊆ Q) (hA : ∀ k, IsRetract (A k))
    (hI : ∀ k, IsRetract (Set.accumulate A k ∩ A (k + 1)))
    {n : ℕ} :
    ∃ H : ↥Q × unitInterval → ↥Q, Continuous H ∧ (∀ x : ↥Q, H (x, 0) = x) ∧
      (∀ x : ↥Q, (H (x, 1) : ℂ) ∈ Set.accumulate A n) ∧
      (∀ x : ↥Q, (x : ℂ) ∈ Set.accumulate A n → ∀ t : unitInterval, H (x, t) = x) := by
  have hsub' : ∀ k, Set.accumulate A k ⊆ Q := by
    intro k
    induction k with
    | zero => simpa [Set.accumulate_zero_nat] using hsub 0
    | succ m ih => rw [Set.accumulate_succ]; exact Set.union_subset ih (hsub (m + 1))
  exact convex_deformationRetract_of_isRetract hQ (hsub' n)
    (Commons.Topology.Plane.retract_union_accumulate_of_retracts hA hI n)

/-- **The tile fold with its parent wall, retract form.**  Same statement as
`convex_deformationRetract_of_wall_and_segment`, but the wall `W` is only assumed to be a *retract of
the plane* (e.g. a sphere arc, which is what `W = D i ∩ D p` actually is in the tile's chart) rather
than convex; the convexity is replaced by `IsRetract W` and `IsRetract (W ∩ [c,p])`, and the chain is
fed to the convexity-free accumulator `deformationRetract_of_retractTree`. -/
theorem deformationRetract_of_wall_and_segment {Q W : Set ℂ} (hQ : Convex ℝ Q) (hWQ : W ⊆ Q)
    (hW : IsRetract W) {c p : ℂ} (hc : c ∈ Q) (hp : p ∈ W)
    (hInt : IsRetract (W ∩ segment ℝ c p)) :
    ∃ H : ↥Q × unitInterval → ↥Q, Continuous H ∧ (∀ x : ↥Q, H (x, 0) = x) ∧
      (∀ x : ↥Q, (H (x, 1) : ℂ) ∈ W ∪ segment ℝ c p) ∧
      (∀ x : ↥Q, (x : ℂ) ∈ W ∪ segment ℝ c p → ∀ t : unitInterval, H (x, t) = x) := by
  classical
  have hAcc : Set.accumulate (fun k : ℕ => if k = 0 then W else segment ℝ c p) 1
      = W ∪ segment ℝ c p := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, Set.accumulate_succ, Set.accumulate_zero_nat]
    simp
  have hsegcl : IsClosed (segment ℝ c p) := by
    rw [segment_eq_image]
    exact (isCompact_Icc.image
      (by fun_prop : Continuous fun t : ℝ => (1 - t) • c + t • p)).isClosed
  have hsegret : IsRetract (segment ℝ c p) :=
    convex_retract (convex_segment _ _) hsegcl ⟨c, left_mem_segment ℝ c p⟩
  have hone : ∀ k, 1 ≤ k →
      Set.accumulate (fun k : ℕ => if k = 0 then W else segment ℝ c p) k
        ∩ (fun k : ℕ => if k = 0 then W else segment ℝ c p) (k + 1) = segment ℝ c p := by
    intro k hk
    have hk1 : k = (k - 1) + 1 := by omega
    rw [hk1, Set.accumulate_succ]
    simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
    exact Set.inter_eq_right.mpr fun x hx => Or.inr hx
  have key := deformationRetract_of_retractTree hQ
    (A := fun k : ℕ => if k = 0 then W else segment ℝ c p)
    (fun k => by
      by_cases hk : k = 0
      · subst hk; simpa using hWQ
      · simpa [hk] using hQ.segment_subset hc (hWQ hp))
    (fun k => by
      by_cases hk : k = 0
      · subst hk; simpa using hW
      · simpa [hk] using hsegret)
    (fun k => by
      by_cases hk : k = 0
      · subst hk
        simp only [Set.accumulate_zero_nat, Nat.reduceAdd, ↓reduceIte]
        exact hInt
      · rw [hone k (by omega)]
        exact hsegret)
    (n := 1)
  simpa only [hAcc] using key

/-- **The fan fold.**  A convex plane set `Q` strongly deformation retracts onto a finite "fan" of
segments `[c, g k]` emanating from a point `c ∈ Q`, provided the segments are met one at a time in a
convex way (consecutive meeting sets `(⋃_{j≤k} [c,g j]) ∩ [c,g (k+1)]` are convex — this holds in
particular when the leaves `g k` are ordered angularly around `c` with all gaps `< π`).

This is the **per-tile fold** of the cut-system design: a tile `D` of a locally finite disk tiling is
(in its own chart) a round ball, hence convex, and the part of the spine inside the tile is exactly
such a fan with leaves at the "gates" where the spine leaves the tile. -/
theorem convex_deformationRetract_of_fan {Q : Set ℂ} (hQ : Convex ℝ Q) {c : ℂ} (hc : c ∈ Q)
    (g : ℕ → ℂ) (hg : ∀ k, g k ∈ Q) {N n : ℕ} (hn : n < N)
    (hint : ∀ k, k + 1 < N →
      Convex ℝ (Set.accumulate (fun k => segment ℝ c (g k)) k ∩ segment ℝ c (g (k + 1))))
    (hintne : ∀ k, k + 1 < N →
      (Set.accumulate (fun k => segment ℝ c (g k)) k ∩ segment ℝ c (g (k + 1))).Nonempty) :
    ∃ H : ↥Q × unitInterval → ↥Q, Continuous H ∧ (∀ x : ↥Q, H (x, 0) = x) ∧
      (∀ x : ↥Q, (H (x, 1) : ℂ) ∈ Set.accumulate (fun k => segment ℝ c (g k)) n) ∧
      (∀ x : ↥Q, (x : ℂ) ∈ Set.accumulate (fun k => segment ℝ c (g k)) n →
        ∀ t : unitInterval, H (x, t) = x) :=
  convex_deformationRetract_of_convexTree hQ (A := fun k => segment ℝ c (g k)) (N := N)
    (fun k => hQ.segment_subset hc (hg k)) (fun k => convex_segment _ _)
    (fun k => by
      rw [segment_eq_image]
      exact (isCompact_Icc.image
        (by fun_prop : Continuous fun t : ℝ => (1 - t) • c + t • (g k))).isClosed)
    (fun k => ⟨c, left_mem_segment ℝ c (g k)⟩) hint hintne hn

/-- **The tile fold with its parent wall** (the `R1` step of the cut-system design).  A convex plane
region `Q` strongly deformation retracts onto `W ∪ [c,p]`, where `W` is a convex closed "wall",
`c ∈ Q`, `p ∈ W`, and the segment `[c,p]` meets the wall only at the gate `p` (true whenever
`c ∈ interior Q` and `W ⊆ frontier Q`).

With `convex_deformationRetract_of_fan`, this is the per-tile ingredient of the cascade: a tile of a
locally finite disk tiling folds onto *(the wall shared with its parent)* ∪ *(the fan to its gates)*,
a tree of segments inside the convex tile — note that no tameness of the walls is ever needed, the
wall enters only through the single gate point `p`. -/
theorem convex_deformationRetract_of_wall_and_segment {Q W : Set ℂ} (hQ : Convex ℝ Q)
    (hWQ : W ⊆ Q) (hWc : Convex ℝ W) (hWcl : IsClosed W) (hWne : W.Nonempty)
    {c p : ℂ} (hc : c ∈ Q) (hp : p ∈ W)
    (hseg : ∀ x ∈ segment ℝ c p, x ∈ W → x = p) :
    ∃ H : ↥Q × unitInterval → ↥Q, Continuous H ∧ (∀ x : ↥Q, H (x, 0) = x) ∧
      (∀ x : ↥Q, (H (x, 1) : ℂ) ∈ W ∪ segment ℝ c p) ∧
      (∀ x : ↥Q, (x : ℂ) ∈ W ∪ segment ℝ c p → ∀ t : unitInterval, H (x, t) = x) := by
  set A : ℕ → Set ℂ := fun k => if k = 0 then W else segment ℝ c p with hA
  have hA0 : A 0 = W := by simp [hA]
  have hA1 : A 1 = segment ℝ c p := by simp [hA]
  have hAp : ∀ k, k ≠ 0 → A k = segment ℝ c p := by
    intro k hk; simp [hA, hk]
  have hAcc : Set.accumulate A 1 = W ∪ segment ℝ c p := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, Set.accumulate_succ, Set.accumulate_zero_nat, hA0, hA1]
  have hInt : W ∩ segment ℝ c p = {p} := by
    ext x
    constructor
    · rintro ⟨hxW, hxseg⟩
      exact mem_singleton_iff.mpr (hseg x hxseg hxW)
    · intro hx
      rw [mem_singleton_iff] at hx
      rw [hx]
      exact ⟨hp, right_mem_segment ℝ c p⟩
  have key := convex_deformationRetract_of_convexTree hQ (A := A) (N := 2)
    (fun k => by
      by_cases hk : k = 0
      · subst hk; rw [hA0]; exact hWQ
      · rw [hAp k hk]; exact hQ.segment_subset hc (hWQ hp))
    (fun k => by
      by_cases hk : k = 0
      · subst hk; rw [hA0]; exact hWc
      · rw [hAp k hk]; exact convex_segment _ _)
    (fun k => by
      by_cases hk : k = 0
      · subst hk; rw [hA0]; exact hWcl
      · rw [hAp k hk, segment_eq_image]
        exact (isCompact_Icc.image
          (by fun_prop : Continuous fun t : ℝ => (1 - t) • c + t • p)).isClosed)
    (fun k => by
      by_cases hk : k = 0
      · subst hk; rw [hA0]; exact hWne
      · rw [hAp k hk]; exact ⟨c, left_mem_segment ℝ c p⟩)
    (fun k hk => by
      have hk0 : k = 0 := by omega
      subst hk0
      rw [Set.accumulate_zero_nat, hA0, hA1, hInt]
      exact convex_singleton p)
    (fun k hk => by
      have hk0 : k = 0 := by omega
      subst hk0
      rw [Set.accumulate_zero_nat, hA0, hA1, hInt]
      exact ⟨p, rfl⟩)
    (n := 1) (by norm_num)
  simpa only [hAcc] using key

/-- **The tile fold with its parent wall and its full fan** (the `R1` keystone).  A convex plane
region `Q` strongly deformation retracts onto `W ∪ ⋃_{k<n} [c, g k]`, where `W` is a convex closed
wall, `c ∈ Q`, the first leaf `g 0` lies in `W` with `[c,g 0]` meeting `W` only at that gate, every
later leaf's segment misses `W`, and distinct segments meet only at `c`.

Every convexity obligation of the underlying `accumulate` chain `A 0 = W`, `A (k+1) = [c,g k]`
collapses to a *singleton*: `W ∩ [c,g 0] = {g 0}` by the gate condition, and
`(⋃_{j≤k} A j) ∩ [c,g (k+1)] = {c}` by "later legs miss `W`" plus leg separation. -/
theorem deformationRetract_of_wall_and_fan {Q W : Set ℂ} (hQ : Convex ℝ Q) (hWQ : W ⊆ Q)
    (hW : IsRetract W) {c : ℂ} (hc : c ∈ Q)
    (g : ℕ → ℂ) (hg : ∀ k, g k ∈ Q) (hgW : g 0 ∈ W)
    (hseg0 : ∀ x ∈ segment ℝ c (g 0), x ∈ W → x = g 0)
    (haway : ∀ k, 0 < k → ∀ x ∈ segment ℝ c (g k), x ∈ W → False)
    (hlegs : ∀ k l, k ≠ l → ∀ x ∈ segment ℝ c (g k), x ∈ segment ℝ c (g l) → x = c)
    {n : ℕ} (hn : 0 < n) :
    ∃ H : ↥Q × unitInterval → ↥Q, Continuous H ∧ (∀ x : ↥Q, H (x, 0) = x) ∧
      (∀ x : ↥Q, (H (x, 1) : ℂ) ∈ W ∪ ⋃ k ∈ Finset.range n, segment ℝ c (g k)) ∧
      (∀ x : ↥Q, (x : ℂ) ∈ W ∪ ⋃ k ∈ Finset.range n, segment ℝ c (g k) →
        ∀ t : unitInterval, H (x, t) = x) := by
  set A : ℕ → Set ℂ := fun k => if k = 0 then W else segment ℝ c (g (k - 1)) with hA
  have hA0 : A 0 = W := by simp [hA]
  have hAk : ∀ k, A (k + 1) = segment ℝ c (g k) := by
    intro k; simp [hA]
  -- subsets of the accumulated chain, in range form
  have hAcc : ∀ m, Set.accumulate A m ⊆ W ∪ ⋃ j ∈ Finset.range m, segment ℝ c (g j) := by
    intro m
    induction m with
    | zero => simp [Set.accumulate_zero_nat, hA0]
    | succ m ih =>
      rw [Set.accumulate_succ, hAk m]
      intro x hx
      rcases hx with hx | hx
      · rcases ih hx with h | h
        · exact Or.inl h
        · exact Or.inr (by
            rcases mem_iUnion₂.mp h with ⟨j, hj, hxj⟩
            exact mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by
              have := Finset.mem_range.mp hj; omega), hxj⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨m, Finset.mem_range.mpr (by omega), hx⟩)
  -- the two singleton meets
  have h1 : Set.accumulate A 0 ∩ A (0 + 1) = {g 0} := by
    rw [Set.accumulate_zero_nat, hA0, hAk 0]
    ext x
    constructor
    · rintro ⟨hxW, hxseg⟩
      exact mem_singleton_iff.mpr (hseg0 x hxseg hxW)
    · intro hx
      rw [mem_singleton_iff] at hx
      rw [hx]
      exact ⟨hgW, right_mem_segment ℝ c (g 0)⟩
  have h2 : ∀ j, Set.accumulate A (j + 1) ∩ A (j + 1 + 1) = {c} := by
    intro j
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxacc, hxseg⟩
      rw [hAk (j + 1)] at hxseg
      rcases hAcc (j + 1) hxacc with hxW | hxu
      · exact (haway (j + 1) (by omega) x hxseg hxW).elim
      · rcases mem_iUnion₂.mp hxu with ⟨l, hl, hxl⟩
        exact hlegs l (j + 1) (by have := Finset.mem_range.mp hl; omega) x hxl hxseg
    · intro x hx
      rw [mem_singleton_iff] at hx
      rw [hx]
      refine ⟨?_, ?_⟩
      · rw [Set.accumulate_succ]
        exact Or.inr (by rw [hAk j]; exact left_mem_segment ℝ c (g j))
      · rw [hAk (j + 1)]; exact left_mem_segment ℝ c (g (j + 1))
  -- the whole-chain identity at index `n`
  have hAccn : Set.accumulate A n = W ∪ ⋃ j ∈ Finset.range n, segment ℝ c (g j) := by
    refine Subset.antisymm (hAcc n) ?_
    intro x hx
    rcases hx with hxW | hxu
    · rw [Set.accumulate_eq_biInter_lt]
      exact mem_iUnion₂.mpr ⟨0, by omega, by rwa [hA0]⟩
    · rcases mem_iUnion₂.mp hxu with ⟨j, hj, hxj⟩
      rw [Set.accumulate_eq_biInter_lt]
      refine mem_iUnion₂.mpr ⟨j + 1, by have := Finset.mem_range.mp hj; omega, ?_⟩
      rw [hAk j]; exact hxj
  obtain ⟨H, hHc, hH0, hH1, hHfix⟩ := deformationRetract_of_retractTree hQ (A := A)
    (fun k => by
      by_cases hk : k = 0
      · subst hk; rw [hA0]; exact hWQ
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hAk j]; exact hQ.segment_subset hc (hg j))
    (fun k => by
      by_cases hk : k = 0
      · subst hk; rw [hA0]; exact hW
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hAk j]
        exact convex_retract (convex_segment _ _) (by
          rw [segment_eq_image]
          exact (isCompact_Icc.image
            (by fun_prop : Continuous fun t : ℝ => (1 - t) • c + t • (g j))).isClosed)
          ⟨c, left_mem_segment ℝ c (g j)⟩)
    (fun k => by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0; rw [h1]
        exact convex_retract (convex_singleton _) isClosed_singleton ⟨g 0, rfl⟩
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [show j + 1 + 1 = j + 1 + 1 from rfl, h2 j]
        exact convex_retract (convex_singleton _) isClosed_singleton ⟨c, rfl⟩)
    (n := n)
  refine ⟨H, hHc, hH0, ?_, ?_⟩
  · intro x
    rw [← hAccn]
    exact hH1 x
  · intro x hx t
    exact hHfix x (by rw [hAccn]; exact hx) t

/-- **Two-piece collapse step (the PL glueing rung).**

Let `K = K' ∪ T` where `T` is a tile with `T ∩ K' ⊆ C` for a one-dimensional subcomplex `C ⊆ K'`,
and suppose that `K'` deformation retracts onto `C` (the induction hypothesis of a collapse) while
`T` deformation retracts onto `T ∩ K'` (the per-tile fold, Rung 0: `T ∩ K'` is a "U"/tree, never a
loop).  Then `K` deformation retracts onto `C`.

This is the step that makes the PL collapse iterable: it is
`Commons.Topology.Homotopy.exists_sdr_of_locallyFinite_closed_cover_folds` applied to the two
closed pieces of the space `↥K`. -/
theorem sdr_of_two_piece_collapse {K K' T C : Set ℂ}
    (hK'cl : IsClosed K') (hTcl : IsClosed T) (hK : K = K' ∪ T)
    (hCsub : C ⊆ K') (hTC : T ∩ K' ⊆ C)
    (hC : Topology.CWComplex (X := {x : ↥K | (x : ℂ) ∈ C}) Set.univ)
    (hdim : ∀ n : ℕ, 2 ≤ n →
      IsEmpty (Topology.CWComplex.cell (X := {x : ↥K | (x : ℂ) ∈ C}) Set.univ n))
    (hK'SDR : ∃ H : ↥K' × unitInterval → ↥K', Continuous H ∧ (∀ x : ↥K', H (x, 0) = x) ∧
      (∀ x : ↥K', (H (x, 1) : ℂ) ∈ C) ∧ (∀ x : ↥K', (x : ℂ) ∈ C → ∀ t : unitInterval, H (x, t) = x))
    (hTSDR : ∃ H : ↥T × unitInterval → ↥T, Continuous H ∧ (∀ x : ↥T, H (x, 0) = x) ∧
      (∀ x : ↥T, (H (x, 1) : ℂ) ∈ T ∩ K') ∧
      (∀ x : ↥T, (x : ℂ) ∈ T ∩ K' → ∀ t : unitInterval, H (x, t) = x)) :
    ∃ H : ↥K × unitInterval → ↥K, Continuous H ∧ (∀ x : ↥K, H (x, 0) = x) ∧
      (∀ x : ↥K, (H (x, 1) : ℂ) ∈ C) ∧ (∀ x : ↥K, (x : ℂ) ∈ C → ∀ t : unitInterval, H (x, t) = x) := by
  classical
  have hTsubK : T ⊆ K := by rw [hK]; exact subset_union_right
  have hK'subK : K' ⊆ K := by rw [hK]; exact subset_union_left
  have hCsubK : C ⊆ K := fun x hx => hK'subK (hCsub hx)
  -- the two pieces, as subsets of `↥K`
  have hpK : IsClosed ({x : ↥K | (x : ℂ) ∈ K'} : Set ↥K) := hK'cl.preimage continuous_subtype_val
  have hpT : IsClosed ({x : ↥K | (x : ℂ) ∈ T} : Set ↥K) := hTcl.preimage continuous_subtype_val
  let piece : Bool → Set ↥K := fun b => if b then {x : ↥K | (x : ℂ) ∈ K'}
                                              else {x : ↥K | (x : ℂ) ∈ T}
  have hpiece_true : piece true = {x : ↥K | (x : ℂ) ∈ K'} := rfl
  have hpiece_false : piece false = {x : ↥K | (x : ℂ) ∈ T} := rfl
  obtain ⟨Hk, hHkc, hHk0, hHk1, hHkfix⟩ := hK'SDR
  obtain ⟨Ht, hHtc, hHt0, hHt1, hHtfix⟩ := hTSDR
  -- global folds on `↥K`, extended by the identity off their pieces
  let φK : ↥K × unitInterval → ↥K := fun q =>
    if h : (q.1 : ℂ) ∈ K' then
      ⟨(Hk (⟨q.1.1, h⟩, q.2) : ↥K'), hK'subK (Hk (⟨q.1.1, h⟩, q.2)).2⟩
    else q.1
  let φT : ↥K × unitInterval → ↥K := fun q =>
    if h : (q.1 : ℂ) ∈ T then
      ⟨(Ht (⟨q.1.1, h⟩, q.2) : ↥T), hTsubK (Ht (⟨q.1.1, h⟩, q.2)).2⟩
    else q.1
  let φ : Bool → ↥K × unitInterval → ↥K := fun b q => if b then φK q else φT q
  have hφK_c : ContinuousOn φK ((piece true) ×ˢ (univ : Set unitInterval)) := by
    rw [hpiece_true]
    have hqK : ∀ q : ↥({x : ↥K | (x : ℂ) ∈ K'} ×ˢ (univ : Set unitInterval)), (q.1.1 : ℂ) ∈ K' :=
      fun q => by
        have h' := q.2
        simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_ofPred_eq] at h'
        exact h'
    have hcont : Continuous fun q : ↥({x : ↥K | (x : ℂ) ∈ K'} ×ˢ (univ : Set unitInterval)) =>
        (⟨(Hk ((⟨(q.1.1 : ℂ), hqK q⟩ : ↥K'), q.1.2) : ↥K'),
          hK'subK (Hk ((⟨(q.1.1 : ℂ), hqK q⟩ : ↥K'), q.1.2)).2⟩ : ↥K) := by
      refine Continuous.subtype_mk ?_ _
      exact Continuous.comp continuous_subtype_val
        (Continuous.comp hHkc (Continuous.prodMk
          (Continuous.subtype_mk
            (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)) hqK)
          (continuous_snd.comp continuous_subtype_val)))
    rw [continuousOn_iff_continuous_domRestrict]
    have hgoal : Continuous (({x : ↥K | (x : ℂ) ∈ K'} ×ˢ (univ : Set unitInterval)).domRestrict φK) :=
      Continuous.congr hcont (fun q => by
        have hq : (q.1.1 : ℂ) ∈ K' := by
          have h' := q.2
          simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_ofPred_eq] at h'
          exact h'
        simp only [Set.domRestrict_apply, φK]
        rw [dif_pos hq])
    exact hgoal
  have hφT_c : ContinuousOn φT ((piece false) ×ˢ (univ : Set unitInterval)) := by
    rw [hpiece_false]
    have hqT : ∀ q : ↥({x : ↥K | (x : ℂ) ∈ T} ×ˢ (univ : Set unitInterval)), (q.1.1 : ℂ) ∈ T :=
      fun q => by
        have h' := q.2
        simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_ofPred_eq] at h'
        exact h'
    have hcont : Continuous fun q : ↥({x : ↥K | (x : ℂ) ∈ T} ×ˢ (univ : Set unitInterval)) =>
        (⟨(Ht ((⟨(q.1.1 : ℂ), hqT q⟩ : ↥T), q.1.2) : ↥T),
          hTsubK (Ht ((⟨(q.1.1 : ℂ), hqT q⟩ : ↥T), q.1.2)).2⟩ : ↥K) := by
      refine Continuous.subtype_mk ?_ _
      exact Continuous.comp continuous_subtype_val
        (Continuous.comp hHtc (Continuous.prodMk
          (Continuous.subtype_mk
            (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)) hqT)
          (continuous_snd.comp continuous_subtype_val)))
    rw [continuousOn_iff_continuous_domRestrict]
    have hgoal : Continuous (({x : ↥K | (x : ℂ) ∈ T} ×ˢ (univ : Set unitInterval)).domRestrict φT) :=
      Continuous.congr hcont (fun q => by
        have hq : (q.1.1 : ℂ) ∈ T := by
          have h' := q.2
          simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_ofPred_eq] at h'
          exact h'
        simp only [Set.domRestrict_apply, φT]
        rw [dif_pos hq])
    exact hgoal
  have hKc : ∀ i, IsClosed (piece i) := by
    intro i
    cases i with
    | true => rw [hpiece_true]; exact hpK
    | false => rw [hpiece_false]; exact hpT
  have hlf : LocallyFinite piece := by
    intro x
    exact ⟨univ, Filter.univ_mem, Set.Finite.subset Set.finite_univ (fun i _ => Set.mem_univ i)⟩
  have hcov : (⋃ i, piece i) = univ := by
    rw [eq_univ_iff_forall]
    intro x
    rw [mem_iUnion]
    by_cases hx : (x : ℂ) ∈ K'
    · exact ⟨true, by rw [hpiece_true]; exact hx⟩
    · have hxT : (x : ℂ) ∈ T := by
        have : (x : ℂ) ∈ K' ∪ T := by rw [← hK]; exact x.2
        exact this.resolve_left hx
      exact ⟨false, by rw [hpiece_false]; exact hxT⟩
  have hKC : ∀ i j, i ≠ j → piece i ∩ piece j ⊆ {x : ↥K | (x : ℂ) ∈ C} := by
    intro i j hij x hx
    rcases hx with ⟨hxi, hxj⟩
    cases i with
    | true =>
        rw [hpiece_true] at hxi
        cases j with
        | true => exact absurd rfl hij
        | false => rw [hpiece_false] at hxj; exact hTC ⟨hxj, hxi⟩
    | false =>
        rw [hpiece_false] at hxi
        cases j with
        | true => rw [hpiece_true] at hxj; exact hTC ⟨hxi, hxj⟩
        | false => exact absurd rfl hij
  have hφc : ∀ i, ContinuousOn (φ i) (piece i ×ˢ (univ : Set unitInterval)) := by
    intro i
    cases i with
    | true => exact hφK_c
    | false => exact hφT_c
  have hφ0 : ∀ i ⦃x : ↥K⦄, x ∈ piece i → φ i (x, 0) = x := by
    intro i x hx
    cases i with
    | true =>
        rw [hpiece_true, Set.mem_ofPred_eq] at hx
        show φK (x, 0) = x
        simp only [φK]
        rw [dif_pos hx]
        apply Subtype.ext
        show ((Hk (⟨(x : ℂ), hx⟩, (0 : unitInterval))) : ℂ) = (x : ℂ)
        rw [hHk0 ⟨(x : ℂ), hx⟩]
    | false =>
        rw [hpiece_false, Set.mem_ofPred_eq] at hx
        show φT (x, 0) = x
        simp only [φT]
        rw [dif_pos hx]
        apply Subtype.ext
        show ((Ht (⟨(x : ℂ), hx⟩, (0 : unitInterval))) : ℂ) = (x : ℂ)
        rw [hHt0 ⟨(x : ℂ), hx⟩]
  have hφ1 : ∀ i ⦃x : ↥K⦄, x ∈ piece i →
      φ i (x, 1) ∈ piece i ∧ φ i (x, 1) ∈ {x : ↥K | (x : ℂ) ∈ C} := by
    intro i x hx
    cases i with
    | true =>
        rw [hpiece_true, Set.mem_ofPred_eq] at hx
        constructor
        · show (φK (x, 1) : ℂ) ∈ K'
          simp only [φK]
          rw [dif_pos hx]
          exact (Hk (⟨x, hx⟩, 1)).2
        · show (φK (x, 1) : ℂ) ∈ C
          simp only [φK]
          rw [dif_pos hx]
          exact hHk1 ⟨x, hx⟩
    | false =>
        rw [hpiece_false, Set.mem_ofPred_eq] at hx
        constructor
        · show (φT (x, 1) : ℂ) ∈ T
          simp only [φT]
          rw [dif_pos hx]
          exact (Ht (⟨x, hx⟩, 1)).2
        · show (φT (x, 1) : ℂ) ∈ C
          simp only [φT]
          rw [dif_pos hx]
          exact hTC (hHt1 ⟨x, hx⟩)
  have hφfix : ∀ i ⦃x : ↥K⦄, x ∈ {x : ↥K | (x : ℂ) ∈ C} → ∀ t : unitInterval, φ i (x, t) = x := by
    intro i x hx t
    have hxC : (x : ℂ) ∈ C := by simpa using hx
    have hxK' : (x : ℂ) ∈ K' := hCsub hxC
    cases i with
    | true =>
        show φK (x, t) = x
        simp only [φK]
        rw [dif_pos hxK']
        apply Subtype.ext
        show ((Hk (⟨(x : ℂ), hxK'⟩, t)) : ℂ) = (x : ℂ)
        rw [hHkfix ⟨(x : ℂ), hxK'⟩ hxC t]
    | false =>
        show φT (x, t) = x
        by_cases hxT : (x : ℂ) ∈ T
        · simp only [φT]
          rw [dif_pos hxT]
          apply Subtype.ext
          show ((Ht (⟨(x : ℂ), hxT⟩, t)) : ℂ) = (x : ℂ)
          rw [hHtfix ⟨(x : ℂ), hxT⟩ ⟨hxT, hxK'⟩ t]
        · simp only [φT]
          rw [dif_neg hxT]
  -- item (1): name the two pieces (distinct from the closedness lemmas `hpK`/`hpT`)
  set pT : Set ↥K := {x : ↥K | (x : ℂ) ∈ T} with hTdef
  set pK : Set ↥K := {x : ↥K | (x : ℂ) ∈ K'} with hKdef
  -- the glued homotopy: fold the tile `T` first for points of `T`, else fold `K'`
  let H : ↥K × unitInterval → ↥K := fun p => if h : (p.1 : ℂ) ∈ T then φT p else φK p
  -- the `piece`-based inputs, restated on `pT`/`pK`
  have hφT_c' : ContinuousOn φT (pT ×ˢ (univ : Set unitInterval)) := by
    rw [← hpiece_false]; exact hφT_c
  have hφK_c' : ContinuousOn φK (pK ×ˢ (univ : Set unitInterval)) := by
    rw [← hpiece_true]; exact hφK_c
  have hcT : ContinuousOn H (pT ×ˢ (univ : Set unitInterval)) := by
    refine hφT_c'.congr ?_
    intro p hp
    have hpT : (p.1.1 : ℂ) ∈ T := by
      have h := (Set.mem_prod.mp hp).1
      rwa [hTdef] at h
    simp only [H]
    rw [dif_pos hpT]
  have hcK : ContinuousOn H (pK ×ˢ (univ : Set unitInterval)) := by
    refine hφK_c'.congr ?_
    intro p hp
    have hpK : (p.1.1 : ℂ) ∈ K' := by
      have h := (Set.mem_prod.mp hp).1
      rwa [hKdef] at h
    by_cases hpT : (p.1.1 : ℂ) ∈ T
    · have hC : (p.1.1 : ℂ) ∈ C := hTC ⟨hpT, hpK⟩
      have h1 : φK p = p.1 := hφfix true (x := p.1) hC p.2
      have h2 : φT p = p.1 := hφfix false (x := p.1) hC p.2
      simp only [H]
      rw [dif_pos hpT, h1, h2]
    · simp only [H]
      rw [dif_neg hpT]
  have hcover : pT ×ˢ (univ : Set unitInterval) ∪ pK ×ˢ (univ : Set unitInterval) = univ := by
    rw [eq_univ_iff_forall]
    intro p
    by_cases hpT : (p.1 : ℂ) ∈ T
    · exact Or.inl ⟨hpT, mem_univ _⟩
    · have hpK' : (p.1 : ℂ) ∈ K' :=
        ((congrArg (fun s : Set ℂ => (p.1 : ℂ) ∈ s) hK).mp p.1.2).resolve_right hpT
      exact Or.inr ⟨hpK', mem_univ _⟩
  have hHcont : Continuous H := by
    rw [← continuousOn_univ, ← hcover]
    exact hcT.union_of_isClosed hcK
      (by rw [hTdef]; exact hpT.prod isClosed_univ)
      (by rw [hKdef]; exact hpK.prod isClosed_univ)
  have hH0 : ∀ x : ↥K, H (x, 0) = x := by
    intro x
    by_cases hxT : (x : ℂ) ∈ T
    · simp only [H, dif_pos hxT]
      exact hφ0 false (by rw [hpiece_false, Set.mem_ofPred_eq]; exact hxT)
    · simp only [H, dif_neg hxT]
      refine hφ0 true ?_
      rw [hpiece_true, Set.mem_ofPred_eq]
      exact ((congrArg (fun s : Set ℂ => (x : ℂ) ∈ s) hK).mp x.2).resolve_right hxT
  have hH1 : ∀ x : ↥K, (H (x, 1) : ℂ) ∈ C := by
    intro x
    by_cases hxT : (x : ℂ) ∈ T
    · simp only [H, dif_pos hxT]
      exact (hφ1 false (by rw [hpiece_false, Set.mem_ofPred_eq]; exact hxT)).2
    · simp only [H, dif_neg hxT]
      refine (hφ1 true ?_).2
      rw [hpiece_true, Set.mem_ofPred_eq]
      exact ((congrArg (fun s : Set ℂ => (x : ℂ) ∈ s) hK).mp x.2).resolve_right hxT
  have hHfix : ∀ x : ↥K, (x : ℂ) ∈ C → ∀ t : unitInterval, H (x, t) = x := by
    intro x hxC t
    have hxK' : (x : ℂ) ∈ K' := hCsub hxC
    by_cases hxT : (x : ℂ) ∈ T
    · simp only [H, dif_pos hxT]
      exact hφfix false (x := x) hxC t
    · simp only [H, dif_neg hxT]
      exact hφfix true (x := x) hxC t
  exact ⟨H, hHcont, hH0, hH1, hHfix⟩


/-- **Rung 2, one elementary collapse step.**

`K = ⋃ j, T j` is a union of tiles, `T i` is a closed convex tile, and `K' = ⋃ j ≠ i, T j` is the
union of the remaining tiles.  If `K'` deformation retracts onto the one-dimensional subcomplex `C`,
the tile meets `K'` inside `C`, and the free part `T i ∩ K'` is a retract of the plane (a "U"/tree,
supplied in practice by `convex_tree_retract`), then `K` deformation retracts onto `C` as well.

This is the single step of which Rung 2 (the finite complex collapse) is the well-founded iteration:
`T i` is the tile being collapsed, and `K'` carries the induction hypothesis. -/
theorem collapse_step_of_tile {ι : Type*} [DecidableEq ι] (T : ι → Set ℂ) (i : ι) {C : Set ℂ}
    (hTconv : Convex ℝ (T i)) (hTcl : IsClosed (T i))
    (hK'cl : IsClosed (⋃ j ∈ ({i}ᶜ : Set ι), T j))
    (hCsub : C ⊆ (⋃ j ∈ ({i}ᶜ : Set ι), T j))
    (hTC : T i ∩ (⋃ j ∈ ({i}ᶜ : Set ι), T j) ⊆ C)
    (hC : Topology.CWComplex (X := {x : ↥(⋃ j, T j) | (x : ℂ) ∈ C}) Set.univ)
    (hdim : ∀ n : ℕ, 2 ≤ n →
      IsEmpty (Topology.CWComplex.cell (X := {x : ↥(⋃ j, T j) | (x : ℂ) ∈ C}) Set.univ n))
    (hK'SDR : ∃ H : ↥(⋃ j ∈ ({i}ᶜ : Set ι), T j) × unitInterval →
        ↥(⋃ j ∈ ({i}ᶜ : Set ι), T j),
      Continuous H ∧ (∀ x : ↥(⋃ j ∈ ({i}ᶜ : Set ι), T j), H (x, 0) = x) ∧ (∀ x : ↥(⋃ j ∈ ({i}ᶜ : Set ι), T j), (H (x, 1) : ℂ) ∈ C) ∧
      (∀ x : ↥(⋃ j ∈ ({i}ᶜ : Set ι), T j), (x : ℂ) ∈ C → ∀ t, H (x, t) = x))
    (hret : IsRetract (T i ∩ (⋃ j ∈ ({i}ᶜ : Set ι), T j))) :
    ∃ H : ↥(⋃ j, T j) × unitInterval → ↥(⋃ j, T j),
      Continuous H ∧ (∀ x : ↥(⋃ j, T j), H (x, 0) = x) ∧ (∀ x : ↥(⋃ j, T j), (H (x, 1) : ℂ) ∈ C) ∧
      (∀ x : ↥(⋃ j, T j), (x : ℂ) ∈ C → ∀ t, H (x, t) = x) := by
  have hU : (⋃ j, T j) = (⋃ j ∈ ({i}ᶜ : Set ι), T j) ∪ T i := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · exact Or.inr (by rwa [hji] at hj)
      · exact Or.inl (mem_iUnion₂.mpr ⟨j, by simpa [Set.mem_compl_singleton_iff] using hji, hj⟩)
    · rcases hx with h | h
      · obtain ⟨j, -, hj⟩ := mem_iUnion₂.mp h
        exact mem_iUnion.mpr ⟨j, hj⟩
      · exact mem_iUnion.mpr ⟨i, h⟩
  exact sdr_of_two_piece_collapse hK'cl hTcl hU hCsub hTC hC hdim hK'SDR
    (convex_deformationRetract_of_isRetract hTconv (fun x hx => hx.1) hret)


/-- **Rung 2, the collapse step in `Finset` form** (the shape the `Finset.induction` needs).

`T i` is one tile of the finite family `s`, the rest of the family is
`K' = ⋃ j ∈ s.erase i, T j`, and `K = ⋃ j ∈ s, T j = K' ∪ T i`.  Given an SDR of `↥K'` onto `C`
(the induction hypothesis), the hypotheses of `collapse_step_of_tile`, and the tile fold from
Rung 0, `K` deformation retracts onto `C`. -/
theorem collapse_step_of_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (T : ι → Set ℂ) (i : ι)
    (hi : i ∈ s) {C : Set ℂ}
    (hTconv : Convex ℝ (T i)) (hTcl : IsClosed (T i))
    (hK'cl : IsClosed (⋃ j ∈ ((s.erase i : Finset ι) : Set ι), T j))
    (hCsub : C ⊆ (⋃ j ∈ ((s.erase i : Finset ι) : Set ι), T j))
    (hTC : T i ∩ (⋃ j ∈ ((s.erase i : Finset ι) : Set ι), T j) ⊆ C)
    (hC : Topology.CWComplex (X := {x : ↥(⋃ j ∈ (s : Set ι), T j) | (x : ℂ) ∈ C}) Set.univ)
    (hdim : ∀ n : ℕ, 2 ≤ n → IsEmpty
      (Topology.CWComplex.cell (X := {x : ↥(⋃ j ∈ (s : Set ι), T j) | (x : ℂ) ∈ C}) Set.univ n))
    (hK'SDR : ∃ H : ↥(⋃ j ∈ ((s.erase i : Finset ι) : Set ι), T j) × unitInterval →
        ↥(⋃ j ∈ ((s.erase i : Finset ι) : Set ι), T j),
      Continuous H ∧ (∀ x : ↥(⋃ j ∈ ((s.erase i : Finset ι) : Set ι), T j), H (x, 0) = x) ∧ (∀ x : ↥(⋃ j ∈ ((s.erase i : Finset ι) : Set ι), T j), (H (x, 1) : ℂ) ∈ C) ∧
      (∀ x : ↥(⋃ j ∈ ((s.erase i : Finset ι) : Set ι), T j), (x : ℂ) ∈ C → ∀ t, H (x, t) = x))
    (hret : IsRetract (T i ∩ (⋃ j ∈ ((s.erase i : Finset ι) : Set ι), T j))) :
    ∃ H : ↥(⋃ j ∈ (s : Set ι), T j) × unitInterval → ↥(⋃ j ∈ (s : Set ι), T j),
      Continuous H ∧ (∀ x : ↥(⋃ j ∈ (s : Set ι), T j), H (x, 0) = x) ∧ (∀ x : ↥(⋃ j ∈ (s : Set ι), T j), (H (x, 1) : ℂ) ∈ C) ∧
      (∀ x : ↥(⋃ j ∈ (s : Set ι), T j), (x : ℂ) ∈ C → ∀ t, H (x, t) = x) := by
  have hU : (⋃ j ∈ (s : Set ι), T j) =
      (⋃ j ∈ ((s.erase i : Finset ι) : Set ι), T j) ∪ T i := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨j, hjs, hj⟩ := mem_iUnion₂.mp hx
      by_cases hji : j = i
      · exact Or.inr (by rwa [hji] at hj)
      · exact Or.inl (mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hjs⟩, hj⟩)
    · rcases hx with h | h
      · obtain ⟨j, hj, hjt⟩ := mem_iUnion₂.mp h
        exact mem_iUnion₂.mpr ⟨j, (Finset.mem_erase.mp hj).2, hjt⟩
      · exact mem_iUnion₂.mpr ⟨i, hi, h⟩
  exact sdr_of_two_piece_collapse hK'cl hTcl hU hCsub hTC hC hdim hK'SDR
    (convex_deformationRetract_of_isRetract hTconv (fun x hx => hx.1) hret)


/-- `x.re ^ 2 ≤ 1` for a point of the closed unit disk. -/
lemma reSq_le_one_of_norm_le_one {x : ℂ} (hx : ‖x‖ ≤ 1) : x.re ^ 2 ≤ 1 := by
  have h1 : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  nlinarith [sq_nonneg x.im, norm_nonneg x, hx]

/-- **The closed unit disk folds onto its closed upper semicircle.**

The explicit "vertical push" `ψ z = ⟨z.re, √(1 - z.re²)⟩` is continuous, fixes the closed upper
semicircle `{z : ℂ | ‖z‖ = 1 ∧ 0 ≤ z.im}` pointwise, and moves every point of the closed unit disk
along a vertical segment onto it.  Hence the closed unit disk strongly deformation retracts onto
that arc, fixing it.

This is the basic "free boundary arc" fold of a `2`-cell: the piece's spine part is a *proper* arc
of its boundary, which is exactly the case that the `H₂` obstruction leaves open (see
`Work/Topology/Surface/NOTES_spine_sharp_obstructions.md`, O1: if the spine part were the whole
boundary circle, no such fold could exist). -/
theorem disk_deformationRetract_upperArc :
    ∃ H : ((↥(Metric.closedBall (0:ℂ) 1)) × unitInterval) → (↥(Metric.closedBall (0:ℂ) 1)),
      Continuous H ∧ (∀ x : (↥(Metric.closedBall (0:ℂ) 1)), H (x, 0) = x) ∧
      (∀ x : (↥(Metric.closedBall (0:ℂ) 1)),
        ((H (x, 1) : (↥(Metric.closedBall (0:ℂ) 1))) : ℂ) ∈
          {z : ℂ | ‖z‖ = 1 ∧ 0 ≤ z.im}) ∧
      (∀ x : (↥(Metric.closedBall (0:ℂ) 1)),
        ((x : (↥(Metric.closedBall (0:ℂ) 1))) : ℂ) ∈ {z : ℂ | ‖z‖ = 1 ∧ 0 ≤ z.im} →
          ∀ t, H (x, t) = x) := by
  set T : Set ℂ := {z : ℂ | ‖z‖ = 1 ∧ 0 ≤ z.im} with hT
  set ψ : ℂ → ℂ := fun z => (z.re : ℂ) + (Real.sqrt (1 - z.re ^ 2) : ℂ) * Complex.I with hψ
  have hcont : Continuous ψ := by
    rw [hψ]
    exact (Complex.continuous_ofReal.comp Complex.continuous_re).add
      ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
        (continuous_const.sub (Complex.continuous_re.pow 2)))).mul continuous_const)
  have hψre : ∀ z : ℂ, (ψ z).re = z.re := by
    intro z; rw [hψ]; simp [Complex.add_re, Complex.mul_re]
  have hψim : ∀ z : ℂ, (ψ z).im = Real.sqrt (1 - z.re ^ 2) := by
    intro z; rw [hψ]; simp [Complex.add_im, Complex.mul_im]
  have hmaps : ∀ z ∈ Metric.closedBall (0:ℂ) 1, ψ z ∈ T := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    have hzre := reSq_le_one_of_norm_le_one hz
    have hs : Real.sqrt (1 - z.re ^ 2) ^ 2 = 1 - z.re ^ 2 := Real.sq_sqrt (by linarith)
    have hn2 : ‖ψ z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hψre z, hψim z]; nlinarith [hs]
    have hnorm : ‖ψ z‖ = 1 := by nlinarith [norm_nonneg (ψ z)]
    exact ⟨hnorm, by rw [hψim z]; exact Real.sqrt_nonneg _⟩
  have hfix : ∀ z ∈ T, ψ z = z := by
    intro z hz
    rw [hT] at hz
    obtain ⟨hn, him⟩ := hz
    have hn2 : z.re ^ 2 + z.im ^ 2 = 1 := by
      have h := Complex.sq_norm z
      rw [hn] at h
      rw [Complex.normSq_apply] at h
      nlinarith [h]
    have hsq : z.im ^ 2 = 1 - z.re ^ 2 := by linarith
    have him' : z.im = Real.sqrt (1 - z.re ^ 2) := by
      have h1 := Real.sq_sqrt (show (0:ℝ) ≤ 1 - z.re ^ 2 by linarith [hsq, sq_nonneg (z.im)])
      have h2 := Real.sqrt_nonneg (1 - z.re ^ 2)
      nlinarith [h1, h2, hsq, him, sq_nonneg (z.im - Real.sqrt (1 - z.re ^ 2)),
        sq_nonneg (z.im + Real.sqrt (1 - z.re ^ 2))]
    have : ψ z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by rw [hψ, him']
    rw [this, Complex.re_add_im]
  have hseg : ∀ z ∈ Metric.closedBall (0:ℂ) 1, segment ℝ z (ψ z) ⊆ Metric.closedBall (0:ℂ) 1 := by
    intro z hz
    have hmemT := hmaps z hz
    have hmem : ψ z ∈ Metric.closedBall (0:ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right]
      rw [hT] at hmemT
      rw [hmemT.1]
    exact (convex_closedBall (0:ℂ) 1).segment_subset hz hmem
  obtain ⟨H, hHc, hH0, hH1, hHfix⟩ :=
    closure_deformationRetract_of_starShaped
      (Metric.closedBall (0:ℂ) 1) T ψ hcont hmaps hfix hseg
  exact ⟨H, hHc, hH0, hH1, hHfix⟩


/-- The norm of `I / 2`. -/
lemma norm_I_div_two : ‖(Complex.I / 2 : ℂ)‖ = 1 / 2 := by
  rw [div_eq_mul_inv, norm_mul, Complex.norm_I, one_mul, norm_inv]
  norm_num

/-- `‖((t / 2 : ℝ) : ℂ)‖ = |t| / 2`. -/
lemma norm_ofReal_div_two (t : ℝ) : ‖(((t / 2 : ℝ)) : ℂ)‖ = |t| / 2 := by
  have h : ‖(((t / 2 : ℝ)) : ℂ)‖ ^ 2 = (t / 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
  nlinarith [norm_nonneg (((t / 2 : ℝ)) : ℂ), abs_nonneg t, sq_abs t]

/-- **The first piece of the planar crescent decomposition: a diameter cut.**

The closed unit disk is the union of its closed upper and lower half-disks, each of which is convex,
hence homeomorphic to the closed unit disk, and whose interiors are disjoint.  This is the simplest
complete instance of the "clean lemma" of the planar crescent decomposition (a compact planar region
bounded by Jordan curves is a finite union of closed disks with disjoint interiors); the general case
additionally needs the Schoenflies-type statement that the closure of a Jordan domain is a disk. -/
theorem exists_disk_decomposition_of_closedBall :
    ∃ (Q : Fin 2 → Set ℂ),
      (⋃ i, Q i) = Metric.closedBall (0:ℂ) 1 ∧
      (∀ i, Nonempty (Metric.closedBall (0:ℂ) 1 ≃ₜ (Q i : Set ℂ))) ∧
      interior (Q 0) ∩ interior (Q 1) = ∅ := by
  let Q : Fin 2 → Set ℂ := fun i =>
    if i = 0 then Metric.closedBall (0:ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im}
    else Metric.closedBall (0:ℂ) 1 ∩ {z : ℂ | z.im ≤ 0}
  have hQ0 : Q 0 = Metric.closedBall (0:ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im} := by simp [Q]
  have hQ1 : Q 1 = Metric.closedBall (0:ℂ) 1 ∩ {z : ℂ | z.im ≤ 0} := by simp [Q]
  have h0or1 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by intro i; fin_cases i <;> simp
  have hconv : ∀ i, Convex ℝ (Q i) := by
    intro i
    have key : ∀ (s : Set ℝ), Convex ℝ s → Convex ℝ {z : ℂ | (z.im) ∈ s} := fun s hs =>
      hs.linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
    rcases h0or1 i with rfl | rfl
    · rw [hQ0]; exact (convex_closedBall (0:ℂ) 1).inter (key _ (convex_Ici 0))
    · rw [hQ1]; exact (convex_closedBall (0:ℂ) 1).inter (key _ (convex_Iic 0))
  -- the two explicit balls inside the interiors
  have hupp : Metric.ball (Complex.I / 2) (1 / 4) ⊆ Q 0 := by
    rw [hQ0]
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h2 : |(w - Complex.I / 2).im| ≤ ‖w - Complex.I / 2‖ :=
      Complex.abs_im_le_norm (w - Complex.I / 2)
    have h3 : (w - Complex.I / 2).im = w.im - 1 / 2 := by simp
    rw [h3, abs_le] at h2
    have h1 : ‖w‖ ≤ ‖w - Complex.I / 2‖ + 1 / 2 := by
      calc ‖w‖ = ‖(w - Complex.I / 2) + Complex.I / 2‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖w - Complex.I / 2‖ + ‖(Complex.I / 2 : ℂ)‖ := norm_add_le _ _
        _ = ‖w - Complex.I / 2‖ + 1 / 2 := by rw [norm_I_div_two]
    have hnorm : ‖w‖ < 1 := by
      calc ‖w‖ ≤ ‖w - Complex.I / 2‖ + 1 / 2 := h1
        _ < 1 / 4 + 1 / 2 := by linarith [hw]
        _ < 1 := by norm_num
    exact ⟨by rw [mem_closedBall, dist_zero_right]; exact le_of_lt hnorm,
      by show (0:ℝ) ≤ w.im; linarith [h2.1, hw]⟩
  have hlowp : Metric.ball (-(Complex.I / 2)) (1 / 4) ⊆ Q 1 := by
    rw [hQ1]
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h2 : |(w + Complex.I / 2).im| ≤ ‖w + Complex.I / 2‖ :=
      Complex.abs_im_le_norm (w + Complex.I / 2)
    have h3 : (w + Complex.I / 2).im = w.im + 1 / 2 := by simp
    rw [h3, abs_le] at h2
    have hw' : ‖w + Complex.I / 2‖ < 1 / 4 := by rw [sub_neg_eq_add] at hw; exact hw
    have h1 : ‖w‖ ≤ ‖w + Complex.I / 2‖ + 1 / 2 := by
      calc ‖w‖ = ‖(w + Complex.I / 2) - Complex.I / 2‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖w + Complex.I / 2‖ + ‖(Complex.I / 2 : ℂ)‖ := norm_sub_le _ _
        _ = ‖w + Complex.I / 2‖ + 1 / 2 := by rw [norm_I_div_two]
    have hnorm : ‖w‖ < 1 := by
      calc ‖w‖ ≤ ‖w + Complex.I / 2‖ + 1 / 2 := h1
        _ < 1 / 4 + 1 / 2 := by linarith [hw']
        _ < 1 := by norm_num
    exact ⟨by rw [mem_closedBall, dist_zero_right]; exact le_of_lt hnorm,
      by show w.im ≤ (0:ℝ); linarith [h2.2, hw']⟩
  refine ⟨Q, ?_, ?_, ?_⟩
  · ext z
    rw [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rcases h0or1 i with rfl | rfl
      · rw [hQ0] at hi; exact hi.1
      · rw [hQ1] at hi; exact hi.1
    · intro hz
      by_cases h : 0 ≤ z.im
      · exact ⟨0, by rw [hQ0]; exact ⟨hz, h⟩⟩
      · exact ⟨1, by rw [hQ1]; exact ⟨hz, (not_le.mp h).le⟩⟩
  · intro i
    have hne : (interior (Q i)).Nonempty := by
      rcases h0or1 i with rfl | rfl
      · exact ⟨Complex.I / 2,
          interior_maximal hupp isOpen_ball (Metric.mem_ball_self (by norm_num))⟩
      · exact ⟨-(Complex.I / 2),
          interior_maximal hlowp isOpen_ball (Metric.mem_ball_self (by norm_num))⟩
    have hbdd : Bornology.IsBounded (Q i) := by
      rcases h0or1 i with rfl | rfl
      · rw [hQ0]; exact Bornology.IsBounded.subset isBounded_closedBall inter_subset_left
      · rw [hQ1]; exact Bornology.IsBounded.subset isBounded_closedBall inter_subset_left
    have hcl : IsClosed (Q i) := by
      rcases h0or1 i with rfl | rfl
      · rw [hQ0]
        exact isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)
      · rw [hQ1]
        exact isClosed_closedBall.inter (isClosed_le Complex.continuous_im continuous_const)
    obtain ⟨e⟩ := Commons.Topology.Surface.homeomorph_closedBall_of_convex (hconv i) hne hbdd hcl
    exact ⟨e.symm⟩
  · -- the two interiors are separated by the real axis
    have hsep : ∀ z ∈ interior (Q 0), 0 < z.im := by
      intro z hz
      have hz0 : 0 ≤ z.im := (interior_subset hz).2
      rcases lt_or_eq_of_le hz0 with h | h
      · exact h
      · exfalso
        obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz)
        have hmove : z - (((ε / 2 : ℝ)) : ℂ) * Complex.I ∈ interior (Q 0) := by
          refine hεsub ?_
          rw [mem_ball, dist_eq_norm]
          have hnorm : ‖z - ((ε / 2 : ℝ) : ℂ) * Complex.I - z‖ = |ε| / 2 := by
            rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one]
            exact norm_ofReal_div_two ε
          rw [hnorm]
          have : |ε| = ε := abs_of_pos hε
          rw [this]; linarith
        have hge : 0 ≤ (z - ((ε / 2 : ℝ) : ℂ) * Complex.I).im := (interior_subset hmove).2
        have him : (z - ((ε / 2 : ℝ) : ℂ) * Complex.I).im = -ε / 2 := by
          simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
          rw [h]; ring
        rw [him] at hge
        linarith
    have hsep' : ∀ z ∈ interior (Q 1), z.im < 0 := by
      intro z hz
      have hz0 : z.im ≤ 0 := (interior_subset hz).2
      rcases lt_or_eq_of_le hz0 with h | h
      · exact h
      · exfalso
        obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz)
        have hmove : z + (((ε / 2 : ℝ)) : ℂ) * Complex.I ∈ interior (Q 1) := by
          refine hεsub ?_
          rw [mem_ball, dist_eq_norm]
          have hnorm : ‖z + ((ε / 2 : ℝ) : ℂ) * Complex.I - z‖ = |ε| / 2 := by
            rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one]
            exact norm_ofReal_div_two ε
          rw [hnorm]
          have : |ε| = ε := abs_of_pos hε
          rw [this]; linarith
        have hge : (z + ((ε / 2 : ℝ) : ℂ) * Complex.I).im ≤ 0 := (interior_subset hmove).2
        have him : (z + ((ε / 2 : ℝ) : ℂ) * Complex.I).im = ε / 2 := by
          simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
          rw [h]; ring
        rw [him] at hge
        linarith
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz0, hz1⟩
    have h1 := hsep z hz0
    have h2 := hsep' z hz1
    linarith

/-- **A line cut of a convex region gives two closed disks.**

Let `Q ⊆ ℂ` be convex, closed and bounded, `l : ℂ →L[ℝ] ℝ` a nonzero linear functional and `c : ℝ`.
If each of the two pieces `Q ∩ {l ≥ c}` and `Q ∩ {l ≤ c}` has nonempty interior (i.e. the line
`l = c` really cuts `Q`), then `Q` is the union of those two pieces, each is homeomorphic to the
closed unit disk (they are convex), and their interiors are disjoint. -/
theorem exists_disk_decomposition_of_convex_line
    {Q : Set ℂ} (hQconv : Convex ℝ Q) (hQcl : IsClosed Q) (hQbdd : Bornology.IsBounded Q)
    (l : ℂ →L[ℝ] ℝ) (c : ℝ) (hv : ∃ v : ℂ, l v ≠ 0)
    (hne₀ : (interior (Q ∩ {z : ℂ | c ≤ l z})).Nonempty)
    (hne₁ : (interior (Q ∩ {z : ℂ | l z ≤ c})).Nonempty) :
    ∃ (P : Fin 2 → Set ℂ),
      (⋃ i, P i) = Q ∧
      (∀ i, Nonempty (Metric.closedBall (0:ℂ) 1 ≃ₜ (P i : Set ℂ))) ∧
      interior (P 0) ∩ interior (P 1) = ∅ := by
  let P : Fin 2 → Set ℂ := fun i =>
    if i = 0 then Q ∩ {z : ℂ | c ≤ l z} else Q ∩ {z : ℂ | l z ≤ c}
  have hP0 : P 0 = Q ∩ {z : ℂ | c ≤ l z} := by simp [P]
  have hP1 : P 1 = Q ∩ {z : ℂ | l z ≤ c} := by simp [P]
  have h0or1 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by intro i; fin_cases i <;> simp
  have hlin : ∀ (z : ℂ) (t : ℝ) (u : ℂ), l (z + t • u) = l z + t * l u := by
    intro z t u
    rw [map_add, map_smul, smul_eq_mul]
  -- the two pieces are nonzero vectors away from the cut line
  refine ⟨P, ?_, ?_, ?_⟩
  · -- union
    ext z
    rw [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rcases h0or1 i with rfl | rfl
      · rw [hP0] at hi; exact hi.1
      · rw [hP1] at hi; exact hi.1
    · intro hz
      by_cases h : c ≤ l z
      · exact ⟨0, by rw [hP0]; exact ⟨hz, h⟩⟩
      · exact ⟨1, by rw [hP1]; exact ⟨hz, (not_le.mp h).le⟩⟩
  · intro i
    have hne : (interior (P i)).Nonempty := by
      rcases h0or1 i with rfl | rfl
      · rw [hP0]; exact hne₀
      · rw [hP1]; exact hne₁
    have hconv : Convex ℝ (P i) := by
      rcases h0or1 i with rfl | rfl
      · rw [hP0]
        exact hQconv.inter ((convex_Ici c).linear_preimage (l : ℂ →ₗ[ℝ] ℝ))
      · rw [hP1]
        exact hQconv.inter ((convex_Iic c).linear_preimage (l : ℂ →ₗ[ℝ] ℝ))
    have hbdd : Bornology.IsBounded (P i) := by
      rcases h0or1 i with rfl | rfl
      · rw [hP0]; exact hQbdd.subset inter_subset_left
      · rw [hP1]; exact hQbdd.subset inter_subset_left
    have hcl : IsClosed (P i) := by
      rcases h0or1 i with rfl | rfl
      · rw [hP0]; exact hQcl.inter (isClosed_Ici.preimage l.continuous)
      · rw [hP1]; exact hQcl.inter (isClosed_Iic.preimage l.continuous)
    obtain ⟨e⟩ := Commons.Topology.Surface.homeomorph_closedBall_of_convex hconv hne hbdd hcl
    exact ⟨e.symm⟩
  · -- the interiors live strictly on the two sides of the cut
    obtain ⟨v, hvne⟩ := hv
    have hsign : ∃ u : ℂ, l u < 0 := by
      rcases lt_or_gt_of_ne (Ne.symm hvne) with h | h
      · exact ⟨-v, by simpa using h⟩
      · exact ⟨v, h⟩
    rw [hP0, hP1]
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz0, hz1⟩
    have hz0' : z ∈ Q ∩ {z : ℂ | c ≤ l z} := interior_subset hz0
    have hz1' : z ∈ Q ∩ {z : ℂ | l z ≤ c} := interior_subset hz1
    have hzc : l z = c := le_antisymm hz1'.2 hz0'.2
    obtain ⟨u, hu⟩ := hsign
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz0)
    have hmove : z + ((ε / 2) / (2 * ‖u‖ + 1)) • u ∈ interior (Q ∩ {z : ℂ | c ≤ l z}) := by
      refine hεsub ?_
      rw [mem_ball, dist_eq_norm]
      have hnorm : ‖z + ((ε / 2) / (2 * ‖u‖ + 1)) • u - z‖ =
          |(ε / 2) / (2 * ‖u‖ + 1)| * ‖u‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      rw [hnorm]
      have hnum : 0 < ε / 2 := by linarith
      have hu0 : 0 < ‖u‖ := by
        refine norm_pos_iff.mpr fun h0 => hu.ne ?_
        rw [h0, map_zero]
      have hb : |(ε / 2) / (2 * ‖u‖ + 1)| * ‖u‖ ≤ ε / 4 := by
        have ht : 0 < (ε / 2) / (2 * ‖u‖ + 1) := div_pos hnum (by positivity)
        rw [abs_of_pos ht]
        have hmul : (ε / 2) / (2 * ‖u‖ + 1) * (2 * ‖u‖ + 1) = ε / 2 := by
          field_simp
        have hle : ‖u‖ ≤ 2 * ‖u‖ + 1 := by linarith [norm_nonneg u]
        nlinarith [ht, mul_le_mul_of_nonneg_left hle ht.le, hmul]
      linarith
    have hge : c ≤ l (z + ((ε / 2) / (2 * ‖u‖ + 1)) • u) := (interior_subset hmove).2
    have hval : l (z + ((ε / 2) / (2 * ‖u‖ + 1)) • u) =
        c + ((ε / 2) / (2 * ‖u‖ + 1)) * l u := by
      rw [hlin z _ u, hzc]
    rw [hval] at hge
    have hpos : 0 < (ε / 2) / (2 * ‖u‖ + 1) := div_pos (by linarith) (by positivity)
    nlinarith [mul_neg_of_pos_of_neg hpos hu]

/-! ## Ingredients of the crosscut assembling induction (R1)

The planar crescent decomposition proceeds by cutting regions along crosscuts.  The two reusable
ingredients proved here are:

* two points in *different* components of a non-preconnected set (used to pick the two "sides" of a
  crosscut, given `crosscut_complement_not_preconnected`);
* the fact that a component of the complement of a *closed* set `S` has its frontier inside `S`,
  hence its closure inside `component ∪ S` (used to show that the two sides of a crosscut have
  disjoint interiors, since a point of `component₁` cannot lie in `closure component₂`). -/

lemma exists_two_points_distinct_components {U : Set ℂ} (hne : ¬ IsPreconnected U) :
    ∃ x ∈ U, ∃ y ∈ U, connectedComponentIn U x ≠ connectedComponentIn U y := by
  by_contra h
  push_neg at h
  have hU : U.Nonempty := by
    rcases U.eq_empty_or_nonempty with h0 | h0
    · exact absurd (h0 ▸ isPreconnected_empty) hne
    · exact h0
  obtain ⟨x0, hx0⟩ := hU
  have hUeq : U = connectedComponentIn U x0 := by
    refine Subset.antisymm (fun y hy => ?_) (connectedComponentIn_subset U x0)
    rw [h x0 hx0 y hy]
    exact mem_connectedComponentIn hy
  exact hne (hUeq ▸ (isConnected_connectedComponentIn_iff.mpr hx0).isPreconnected)

lemma frontier_connectedComponentIn_subset' {S : Set ℂ} (hS : IsClosed S) (x : ℂ) :
    frontier (connectedComponentIn Sᶜ x) ⊆ S := by
  intro z hz
  rw [frontier] at hz
  exact Commons.Topology.Jordan.frontier_connectedComponentIn_subset hS x z hz.1 hz.2

lemma closure_connectedComponentIn_subset_union {S : Set ℂ} (hS : IsClosed S) (x : ℂ) :
    closure (connectedComponentIn Sᶜ x) ⊆ connectedComponentIn Sᶜ x ∪ S := by
  rw [closure_eq_self_union_frontier]
  exact union_subset subset_union_left
    ((frontier_connectedComponentIn_subset' hS x).trans subset_union_right)

/-- **The crosscut assembling step of the planar crescent decomposition.**

Let `β` be a crosscut of the round ball `ball c r` (a Jordan arc with its two endpoints on the
sphere and its interior inside the ball).  Then there are two closed sets `Q0, Q1` — the closures of
the two components of `ball c r \ range β`, chosen as the components of two points that
`crosscut_complement_not_preconnected` guarantees lie in different components — such that:

* both are closed and contained in `closedBall c r`, and together they cover **all** of
  `closedBall c r` (so `Q0 ∪ Q1 = closedBall c r`);
* their interiors are disjoint.

The cover of the open part `ball c r \ range β` is `crosscut_complement_at_most_two` on the triple
of points; the remaining points are the crosscut itself (`crosscut_component_closure` for its
interior points, and for its two endpoints the radial limit argument below) and the sphere (for a
sphere point `z` the radial points `c + t • (z - c)` lie in the ball, hence in `closure Q0 ∪
closure Q1`; if `z` were outside one of them, `IsClosed.mem_of_tendsto` would put it inside the
other).  Disjointness of the interiors uses `closure_connectedComponentIn_subset_union`: a point of
`closure C0` that also lies in `closure C1` must already lie in `C0 ∩ C1`, impossible for two
different components.  Combined with the Schoenflies hook (`closure of a Jordan domain ≅ closed
disk`) this gives the two-disk decomposition of the ball along the crosscut. -/
theorem exists_two_closed_pieces_of_crosscut
    {c : ℂ} {r : ℝ} (hr : 0 < r) (β : C(Set.Icc (0:ℝ) 1, ℂ)) (hβ : Function.Injective β)
    (h0 : β 0 ∈ Metric.sphere c r) (h1 : β 1 ∈ Metric.sphere c r)
    (hint : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 → β t ∈ Metric.ball c r)
    (h01 : β 0 ≠ β 1) :
    ∃ Q0 Q1 : Set ℂ,
      IsClosed Q0 ∧ IsClosed Q1 ∧
      (Metric.ball c r \ Set.range β ⊆ Q0 ∪ Q1) ∧
      Q0 ⊆ Metric.closedBall c r ∧ Q1 ⊆ Metric.closedBall c r ∧
      Disjoint (interior Q0) (interior Q1) ∧
      -- with `Q i ⊆ closedBall`, this is `Q0 ∪ Q1 = closedBall c r`
      Metric.closedBall c r ⊆ Q0 ∪ Q1 := by
  classical
  set U : Set ℂ := Metric.ball c r \ Set.range β with hU
  have hβcl : IsClosed (Set.range β) := (isCompact_range β.continuous).isClosed
  have hUopen : IsOpen U := isOpen_ball.sdiff hβcl
  have hcompl : Uᶜ = (Metric.ball c r)ᶜ ∪ Set.range β := by
    rw [hU, compl_sdiff, union_comm]
  have hnotprec : ¬ IsPreconnected U :=
    Commons.Topology.Jordan.crosscut_complement_not_preconnected c hr β hβ h0 h1 hint
  obtain ⟨x, hxU, y, hyU, hxy⟩ := exists_two_points_distinct_components hnotprec
  have hxball : x ∈ Metric.ball c r := hxU.1
  have hyball : y ∈ Metric.ball c r := hyU.1
  have hxβ : x ∉ Set.range β := hxU.2
  have hyβ : y ∉ Set.range β := hyU.2
  have hC0U : connectedComponentIn U x ⊆ U := connectedComponentIn_subset U x
  have hC1U : connectedComponentIn U y ⊆ U := connectedComponentIn_subset U y
  have hUsub : U ⊆ closure (connectedComponentIn U x) ∪ closure (connectedComponentIn U y) := by
    intro z hz
    have hzball : z ∈ Metric.ball c r := hz.1
    have hzβ : z ∉ Set.range β := hz.2
    rcases Commons.Topology.Jordan.crosscut_complement_at_most_two c hr β hβ h0 h1 hint
      hxball hyball hzball hxβ hyβ hzβ with hxy' | hyz | hxz
    · exact absurd hxy' hxy
    · rw [hyz]; exact Or.inr (subset_closure (mem_connectedComponentIn hz))
    · rw [hxz]; exact Or.inl (subset_closure (mem_connectedComponentIn hz))
  refine ⟨closure (connectedComponentIn U x), closure (connectedComponentIn U y),
    isClosed_closure, isClosed_closure, ?_, ?_, ?_, ?_, ?_⟩
  · exact hUsub
  · exact closure_minimal (hC0U.trans (fun z hz => ball_subset_closedBall hz.1)) isClosed_closedBall
  · exact closure_minimal (hC1U.trans (fun z hz => ball_subset_closedBall hz.1)) isClosed_closedBall
  · -- disjoint interiors
    rw [disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz0, hz1⟩
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_interior.inter isOpen_interior).mem_nhds ⟨hz0, hz1⟩)
    have hne0 : ((Metric.ball z ε) ∩ connectedComponentIn U x).Nonempty :=
      (mem_closure_iff_nhds.mp (interior_subset hz0)) (Metric.ball z ε)
        (Metric.ball_mem_nhds z hε)
    obtain ⟨w0, hw0ball, hw0C0⟩ := hne0
    have hw0Q1 : w0 ∈ closure (connectedComponentIn U y) :=
      interior_subset (hεsub hw0ball).2
    have hb : closure (connectedComponentIn U y) ⊆ connectedComponentIn U y ∪ Uᶜ := by
      simpa [compl_compl] using closure_connectedComponentIn_subset_union hUopen.isClosed_compl y
    rcases hb hw0Q1 with hmem | hmem
    · exact hxy ((connectedComponentIn_eq hw0C0).trans (connectedComponentIn_eq hmem).symm)
    · rw [hcompl] at hmem
      rcases hmem with hnb | hβ
      · exact hnb (hC0U hw0C0).1
      · exact (hC0U hw0C0).2 hβ

  · -- the closed ball is covered
    -- (a) interior points of the crosscut lie on the first side
    have hcross : ∀ t : Set.Icc (0:ℝ) 1, t ≠ 0 → t ≠ 1 →
        β t ∈ closure (connectedComponentIn U x) := fun t ht0 ht1 =>
      Commons.Topology.Jordan.crosscut_component_closure hr β hβ h0 h1 hint hxU t ht0 ht1
    -- (b) the sphere is covered, by a radial limit argument
    have hsphere : Metric.sphere c r ⊆
        closure (connectedComponentIn U x) ∪ closure (connectedComponentIn U y) := by
      intro z hz
      have hzc : ‖z - c‖ = r := by
        rw [Metric.mem_sphere, dist_eq_norm] at hz
        exact hz
      by_contra hcon
      rw [mem_union, not_or] at hcon
      have hpath : Filter.Tendsto (fun t : ℝ => c + t • (z - c)) (𝓝[<] (1:ℝ)) (𝓝 z) := by
        have hcont : Continuous fun t : ℝ => c + t • (z - c) := by fun_prop
        have h1 : Filter.Tendsto (fun t : ℝ => c + t • (z - c)) (𝓝 (1:ℝ))
            (𝓝 (c + (1:ℝ) • (z - c))) := hcont.continuousAt
        have : c + (1:ℝ) • (z - c) = z := by simp
        rw [this] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      have hout : ∀ᶠ t in 𝓝[<] (1:ℝ),
          c + t • (z - c) ∉ closure (connectedComponentIn U x) :=
        hpath.eventually (isClosed_closure.isOpen_compl.mem_nhds hcon.1)
      have hin : ∀ᶠ t in 𝓝[<] (1:ℝ),
          c + t • (z - c) ∈ closure (connectedComponentIn U x) ∪
            closure (connectedComponentIn U y) := by
        filter_upwards [Ioo_mem_nhdsLT (show (1:ℝ) / 2 < 1 by norm_num)] with t ht
        have hval : ‖c + t • (z - c) - c‖ = t * r := by
          rw [show c + t • (z - c) - c = t • (z - c) by abel, norm_smul, Real.norm_eq_abs,
            abs_of_pos (by linarith [ht.1]), hzc]
        have htball : c + t • (z - c) ∈ Metric.ball c r := by
          rw [mem_ball, dist_eq_norm, hval]
          nlinarith [ht.2]
        rcases em (c + t • (z - c) ∈ Set.range β) with hβ' | hβ'
        · obtain ⟨s, hs⟩ := hβ'
          have hsne0 : s ≠ 0 := by
            intro hs0
            have hzt : c + t • (z - c) = β 0 := by rw [← hs, hs0]
            have hsp : (β 0 : ℂ) ∈ Metric.sphere c r := h0
            rw [← hzt] at hsp
            rw [Metric.mem_sphere, dist_eq_norm, hval] at hsp
            nlinarith [ht.2, hr]
          have hsne1 : s ≠ 1 := by
            intro hs1
            have hzt : c + t • (z - c) = β 1 := by rw [← hs, hs1]
            have hsp : (β 1 : ℂ) ∈ Metric.sphere c r := h1
            rw [← hzt] at hsp
            rw [Metric.mem_sphere, dist_eq_norm, hval] at hsp
            nlinarith [ht.2, hr]
          exact Or.inl (hs ▸ hcross s hsne0 hsne1)
        · exact hUsub ⟨htball, hβ'⟩
      have hge : ∀ᶠ t in 𝓝[<] (1:ℝ),
          c + t • (z - c) ∈ closure (connectedComponentIn U y) := by
        filter_upwards [hin, hout] with t ht_in ht_out
        rcases ht_in with h | h
        · exact absurd h ht_out
        · exact h
      exact hcon.2 (isClosed_closure.mem_of_tendsto hpath hge)
    -- (c) combine
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    by_cases hzb : z ∈ Metric.ball c r
    · rcases em (z ∈ Set.range β) with hβ' | hβ'
      · obtain ⟨s, hs⟩ := hβ'
        rw [mem_ball, dist_eq_norm] at hzb
        have hsne0 : s ≠ 0 := by
          intro hs0
          have hz0 : z = β 0 := by rw [← hs, hs0]
          have hsp : z ∈ Metric.sphere c r := by rw [hz0]; exact h0
          rw [Metric.mem_sphere, dist_eq_norm] at hsp
          linarith
        have hsne1 : s ≠ 1 := by
          intro hs1
          have hz1 : z = β 1 := by rw [← hs, hs1]
          have hsp : z ∈ Metric.sphere c r := by rw [hz1]; exact h1
          rw [Metric.mem_sphere, dist_eq_norm] at hsp
          linarith
        exact Or.inl (hs ▸ hcross s hsne0 hsne1)
      · exact hUsub ⟨hzb, hβ'⟩
    · have hzsphere : z ∈ Metric.sphere c r := by
        rw [Metric.mem_sphere, dist_eq_norm]
        rw [mem_ball, dist_eq_norm, not_lt] at hzb
        exact le_antisymm hz hzb
      exact hsphere hzsphere


end Commons.Topology.Plane

namespace Commons.Topology.CWComplex

/-- **A CW structure on a subset of `ℂ` does not depend on the ambient subset.**

If `C ⊆ A ⊆ B ⊆ ℂ` and `C` carries a CW structure inside `↥A`, it carries one inside `↥B`, and the
"no cells of dimension `≥ 2`" clause transports.  The two models of `C` are the same space pointwise
(both are `C` with the subspace topology inherited from `ℂ`), so this is a transport of the structure
along the canonical homeomorphism, via `exists_cwComplex_homeomorph_univ`. -/
theorem cwComplex_transport_ambient_subset {A B C : Set ℂ} (hCA : C ⊆ A) (hAB : A ⊆ B)
    (h : Topology.CWComplex (X := {x : ↥A | (x : ℂ) ∈ C}) Set.univ) :
    ∃ h' : Topology.CWComplex (X := {x : ↥B | (x : ℂ) ∈ C}) Set.univ,
      (∀ n : ℕ, 2 ≤ n →
        IsEmpty (Topology.CWComplex.cell (X := {x : ↥A | (x : ℂ) ∈ C}) Set.univ n)) →
      (∀ n : ℕ, 2 ≤ n →
        IsEmpty (Topology.CWComplex.cell (X := {x : ↥B | (x : ℂ) ∈ C}) Set.univ n)) := by
  have hE : {x : ↥A | (x : ℂ) ∈ C} ≃ₜ {x : ↥B | (x : ℂ) ∈ C} :=
    { toFun := fun x => ⟨⟨x.1.1, hAB x.1.2⟩, x.2⟩
      invFun := fun y => ⟨⟨y.1.1, hCA y.2⟩, y.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  obtain ⟨h', hcell'⟩ := Commons.Topology.CWComplex.exists_cwComplex_homeomorph_univ h hE
  exact ⟨h', fun hdim n hn => ⟨fun a => (hdim n hn).false ((hcell' n).some a)⟩⟩


end Commons.Topology.CWComplex


/-! ## Towards the "no loophole" theorem: a surface is not a one-dimensional CW complex

The requested statement forces `G` to be a **proper** subspace of `X`: it is impossible to make the
whole surface into a CW complex all of whose cells have dimension `≤ 1`.  The argument (provable
with the library as it stands) runs:

* `X` is locally compact Hausdorff and second countable, hence a Baire space; a countable cover of
  `X` by closed cells gives a closed cell with nonempty interior (`BaireSpace` + the
  `Topology.CWComplex.union'` axiom + countability of the cell types);
* `0`-cells are single points, and a nonempty open set of a surface is infinite (no isolated
  points), so they have empty interior;
* `1`-cells are `openCell ∪ F` with `openCell` the (homeomorphic!) image of the model open interval
  `Metric.ball (0 : Fin 1 → ℝ) 1` and `F` finite; an open interval has empty interior in a surface
  (`empty_interior_of_homeomorph_interval_of_chartedSpace` below), and a finite set cannot contain a
  nonempty open set.

The lemmas below are the analytic/topological atoms of that argument; `exp` mapping the half plane
onto the punctured disk replaces any use of invariance of domain.
-/

namespace Commons.Topology.Surface

theorem exp_image_re_lt_halfplane (c : ℝ) :
    Complex.exp '' {w : ℂ | w.re < c} = Metric.ball (0 : ℂ) (Real.exp c) \ {0} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [Set.mem_ofPred_eq] at hw
    refine ⟨?_, Complex.exp_ne_zero w⟩
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
    exact Real.exp_lt_exp.mpr hw
  · rintro ⟨hz, hz0⟩
    refine ⟨Complex.log z, ?_, Complex.exp_log hz0⟩
    simp only [Set.mem_ofPred_eq, Complex.log_re]
    rw [Metric.mem_ball, dist_zero_right] at hz
    simpa [Real.log_exp] using
      (Real.log_lt_log_iff (norm_pos_iff.mpr hz0) (Real.exp_pos c)).mpr hz

theorem isPreconnected_ball_diff_center (c : ℂ) (r : ℝ) (hr : 0 < r) :
    IsPreconnected (Metric.ball c r \ {c}) := by
  have hconv : Convex ℝ {w : ℂ | w.re < Real.log r} := by
    rw [convex_iff_forall_pos]
    intro u hu v hv a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hu hv ⊢
    have hre : (a • u + b • v : ℂ).re = a * u.re + b * v.re := by
      simp [Complex.add_re]
    rw [hre]
    have h1 : a * u.re < a * Real.log r := mul_lt_mul_of_pos_left hu ha
    have h2 : b * v.re < b * Real.log r := mul_lt_mul_of_pos_left hv hb
    have h3 : a * Real.log r + b * Real.log r = Real.log r := by
      rw [← add_mul, hab, one_mul]
    linarith
  have himg : IsPreconnected (Complex.exp '' {w : ℂ | w.re < Real.log r}) :=
    hconv.isPreconnected.image Complex.exp Complex.continuous_exp.continuousOn
  rw [exp_image_re_lt_halfplane (Real.log r), Real.exp_log hr] at himg
  have h := himg.image (fun z : ℂ => c + z) (continuous_const.add continuous_id).continuousOn
  have heq : (fun z : ℂ => c + z) '' (Metric.ball (0 : ℂ) r \ {0}) = Metric.ball c r \ {c} := by
    ext z
    rw [mem_sdiff, mem_singleton_iff, mem_image]
    constructor
    · rintro ⟨w, ⟨hw, hw0⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball] at hw ⊢
        simpa [dist_eq_norm] using hw
      · intro h
        exact hw0 (by simpa using congrArg (fun t => t - c) h)
    · rintro ⟨hz, hzc⟩
      refine ⟨z - c, ⟨?_, ?_⟩, by ring⟩
      · rw [Metric.mem_ball] at hz ⊢
        simpa [dist_eq_norm] using hz
      · simpa using sub_ne_zero.mpr hzc
  rwa [heq] at h

/-- Preconnectedness transports to a subtype: if `t ⊆ s` is preconnected in `α`, then
`{x : ↥s | x.1 ∈ t}` is preconnected. -/
theorem isPreconnected_preimage_subtype {α : Type*} [TopologicalSpace α] {s t : Set α}
    (hts : t ⊆ s) (ht : IsPreconnected t) :
    IsPreconnected (Subtype.val ⁻¹' t : Set ↥s) := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | htne
  · rw [Set.preimage_empty]; exact isPreconnected_empty
  · obtain ⟨p, hp⟩ := htne
    let g : α → ↥s := fun a => if ha : a ∈ s then ⟨a, ha⟩ else ⟨p, hts hp⟩
    have hgval : ∀ a (ha : a ∈ t), g a = (⟨a, hts ha⟩ : ↥s) := by
      intro a ha
      show (if h : a ∈ s then ⟨a, h⟩ else ⟨p, hts hp⟩) = (⟨a, hts ha⟩ : ↥s)
      rw [dif_pos (hts ha)]
    have hcont : Continuous fun c : ↥t => (⟨c.1, hts c.2⟩ : ↥s) :=
      continuous_subtype_val.subtype_mk (fun c => hts c.2)
    have hgcont : ContinuousOn g t := by
      rw [continuousOn_iff_continuous_domRestrict]
      convert hcont using 1
      funext c
      simpa only [Set.domRestrict_apply] using hgval c.1 c.2
    have h := ht.image g hgcont
    have hset : g '' t = (Subtype.val ⁻¹' t : Set ↥s) := by
      ext b
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [hgval a ha]
        exact ha
      · intro hb
        refine ⟨b.1, hb, ?_⟩
        rw [hgval b.1 hb]
    rwa [hset] at h

/-- An open subset of the model space `Fin 1 → ℝ` containing a point `t` contains points on both
sides of `t`, measured by the coordinate `0`. -/
theorem exists_mem_lt_gt_of_isOpen_pi {V : Set (Fin 1 → ℝ)} (hV : IsOpen V)
    {t : Fin 1 → ℝ} (ht : t ∈ V) :
    (∃ u ∈ V, u 0 < t 0) ∧ (∃ v ∈ V, t 0 < v 0) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds ht)
  constructor
  · refine ⟨fun _ => t 0 - ε / 2, hsub ?_, by linarith⟩
    rw [Metric.mem_ball, dist_pi_lt_iff (by linarith)]
    rw [Fin.forall_fin_one, Real.dist_eq, abs_lt]
    constructor <;> linarith
  · refine ⟨fun _ => t 0 + ε / 2, hsub ?_, by linarith⟩
    rw [Metric.mem_ball, dist_pi_lt_iff (by linarith)]
    rw [Fin.forall_fin_one, Real.dist_eq, abs_lt]
    constructor <;> linarith

/-- The same statement for the model open interval itself (`Fin 1 → ℝ` with unit ball). -/
theorem exists_mem_lt_gt_of_isOpen_interval {V : Set ↥(Metric.ball (0 : Fin 1 → ℝ) 1)}
    (hV : IsOpen V) {t : ↥(Metric.ball (0 : Fin 1 → ℝ) 1)} (ht : t ∈ V) :
    (∃ u ∈ V, u.1 0 < t.1 0) ∧ (∃ v ∈ V, t.1 0 < v.1 0) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds ht)
  have ht0 : |t.1 0| < 1 := by
    have h1 : dist (t.1 0) (0 : ℝ) ≤ dist t.1 (0 : Fin 1 → ℝ) := by
      have := (dist_pi_le_iff (dist_nonneg : 0 ≤ dist t.1 (0 : Fin 1 → ℝ))).mp le_rfl
      simpa using this (0 : Fin 1)
    have h2 : dist t.1 (0 : Fin 1 → ℝ) < 1 := Metric.mem_ball.mp t.2
    simpa [Real.dist_eq] using lt_of_le_of_lt h1 h2
  have hconst : ∀ c : ℝ, |c| < 1 → ((fun _ : Fin 1 => c) : Fin 1 → ℝ) ∈
      Metric.ball (0 : Fin 1 → ℝ) 1 := by
    intro c hc
    rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num)]
    intro i
    fin_cases i
    simpa [Real.dist_eq] using hc
  have hdist : ∀ c : ℝ, dist ((fun _ : Fin 1 => c) : Fin 1 → ℝ) t.1 ≤ |c - t.1 0| := by
    intro c
    refine (dist_pi_le_iff (abs_nonneg _)).mpr fun i => ?_
    fin_cases i
    simp [Real.dist_eq]
  set δ : ℝ := min (ε / 2) ((1 - |t.1 0|) / 2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδ1 : δ ≤ (1 - |t.1 0|) / 2 := min_le_right _ _
  constructor
  · have hb : |t.1 0 - δ| < 1 := by
      have h3 : |t.1 0 - δ| ≤ |t.1 0| + δ := by
        simpa [abs_of_pos hδ] using abs_sub_le (t.1 0) 0 δ
      have h4 : |t.1 0| + δ ≤ (1 + |t.1 0|) / 2 := by linarith
      linarith
    refine ⟨⟨fun _ => t.1 0 - δ, hconst _ hb⟩, hsub ?_, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq]
      have h := hdist (t.1 0 - δ)
      have h4 : |(t.1 0 - δ) - t.1 0| = δ := by
        rw [show (t.1 0 - δ) - t.1 0 = -δ from by ring, abs_neg, abs_of_pos hδ]
      rw [h4] at h
      exact lt_of_le_of_lt h (by linarith)
    · show t.1 0 - δ < t.1 0
      linarith
  · have hb : |t.1 0 + δ| < 1 := by
      have h3 : |t.1 0 + δ| ≤ |t.1 0| + δ := by
        simpa [sub_neg_eq_add, abs_of_pos hδ] using abs_sub_le (t.1 0) 0 (-δ)
      have h4 : |t.1 0| + δ ≤ (1 + |t.1 0|) / 2 := by linarith
      linarith
    refine ⟨⟨fun _ => t.1 0 + δ, hconst _ hb⟩, hsub ?_, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq]
      have h := hdist (t.1 0 + δ)
      have h4 : |(t.1 0 + δ) - t.1 0| = δ := by
        rw [show (t.1 0 + δ) - t.1 0 = δ from by ring, abs_of_pos hδ]
      rw [h4] at h
      exact lt_of_le_of_lt h (by linarith)
    · show t.1 0 < t.1 0 + δ
      linarith


/-- **Thinness of an interval: the sharp no-loophole step.**

Let `β` be an open set containing `z` such that `β \ {z}` is preconnected, and let `β ⊆ A` where
`A` is homeomorphic to the model open interval `Metric.ball (0 : Fin 1 → ℝ) 1`.  Then `z` is not an
interior point of `A`.  (Informally: the disk-like set `β \ {z}` is preconnected, but its image
under the homeomorphism onto the interval is separated by the two sides of a point of an open
subset of the interval.) -/
theorem not_mem_interior_of_homeomorph_interval {X : Type*} [TopologicalSpace X]
    {A β : Set X} {z : X} (hβA : β ⊆ A) (hzβ : z ∈ β) (hβopen : IsOpen β)
    (hβpre : IsPreconnected (β \ {z}))
    (h : Nonempty (↥A ≃ₜ ↥(Metric.ball (0 : Fin 1 → ℝ) 1))) : z ∉ interior A := by
  intro hz
  obtain ⟨H⟩ := h
  let Φ : ↥β → ↥(Metric.ball (0 : Fin 1 → ℝ) 1) := fun b => H ⟨b.1, hβA b.2⟩
  have hΦinj : Function.Injective Φ := by
    intro b b' hbb
    have h1 : (⟨b.1, hβA b.2⟩ : ↥A) = ⟨b'.1, hβA b'.2⟩ := H.injective hbb
    exact Subtype.ext (congrArg (fun a : ↥A => (a : X)) h1)
  have hΦcont : Continuous Φ := by
    have h1 : Continuous fun b : ↥β => (⟨b.1, hβA b.2⟩ : ↥A) :=
      continuous_subtype_val.subtype_mk (fun b => hβA b.2)
    exact H.continuous.comp h1
  have hSopen : IsOpen {a : ↥A | (a : X) ∈ β} :=
    hβopen.preimage (continuous_subtype_val : Continuous (Subtype.val : ↥A → X))
  have himge : Φ '' (Set.univ : Set ↥β) = H '' {a : ↥A | (a : X) ∈ β} := by
    ext y
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨⟨b.1, hβA b.2⟩, b.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a.1, ha⟩, trivial, rfl⟩
  have hopen : IsOpen (Φ '' (Set.univ : Set ↥β)) := by
    rw [himge]
    exact H.isOpenMap _ hSopen
  have hPpre : IsPreconnected {b : ↥β | b ≠ z} := by
    have hsub : IsPreconnected (Subtype.val ⁻¹' (β \ {z}) : Set ↥β) :=
      isPreconnected_preimage_subtype (s := β) (t := β \ {z}) (fun w hw => hw.1) hβpre
    convert hsub using 1
    ext b
    rw [mem_preimage, mem_sdiff, mem_singleton_iff, mem_setOf_eq]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  set t : ↥(Metric.ball (0 : Fin 1 → ℝ) 1) := Φ ⟨z, hzβ⟩ with ht
  have hset : {b : ↥β | b ≠ z} = (Set.univ : Set ↥β) \ {⟨z, hzβ⟩} := by
    ext b
    rw [mem_setOf_eq, mem_sdiff, mem_singleton_iff]
    simp only [mem_univ, true_and]
    constructor
    · intro hb hb'
      exact hb (congrArg (fun a : ↥β => (a : X)) hb')
    · intro hb hz'
      exact hb (Subtype.ext hz')
  have hsplit : Φ '' {b : ↥β | b ≠ z} = Φ '' Set.univ \ {t} := by
    rw [hset, Set.image_sdiff hΦinj, Set.image_singleton]
  have hpre : IsPreconnected (Φ '' Set.univ \ {t}) := by
    rw [← hsplit]
    exact hPpre.image Φ hΦcont.continuousOn
  have htmem : t ∈ Φ '' (Set.univ : Set ↥β) := ⟨⟨z, hzβ⟩, trivial, rfl⟩
  obtain ⟨⟨u₀, hu₀mem, hu₀lt⟩, ⟨v₀, hv₀mem, hv₀gt⟩⟩ :=
    exists_mem_lt_gt_of_isOpen_interval hopen htmem
  have hu₀ne : u₀ ≠ t := fun hh => absurd (hh ▸ hu₀lt) (lt_irrefl _)
  have hv₀ne : v₀ ≠ t := fun hh => absurd (hh ▸ hv₀gt) (lt_irrefl _)
  have hu₀s : u₀ ∈ Φ '' Set.univ \ {t} := ⟨hu₀mem, hu₀ne⟩
  have hv₀s : v₀ ∈ Φ '' Set.univ \ {t} := ⟨hv₀mem, hv₀ne⟩
  set u : Set ↥(Metric.ball (0 : Fin 1 → ℝ) 1) := {y | y.1 0 ≤ t.1 0} with hudef
  set v : Set ↥(Metric.ball (0 : Fin 1 → ℝ) 1) := {y | t.1 0 ≤ y.1 0} with hvdef
  have hval : Continuous (Subtype.val : ↥(Metric.ball (0 : Fin 1 → ℝ) 1) → (Fin 1 → ℝ)) :=
    continuous_subtype_val
  have hucl : IsClosed u :=
    isClosed_le ((continuous_apply 0).comp hval) continuous_const
  have hvcl : IsClosed v :=
    isClosed_le continuous_const ((continuous_apply 0).comp hval)
  have hsu : Φ '' Set.univ \ {t} ⊆ u ∪ v := by
    rintro y -
    rcases lt_or_ge (y.1 0) (t.1 0) with hh | hh
    · exact Or.inl hh.le
    · exact Or.inr hh
  have hdisj : (Φ '' Set.univ \ {t}) ∩ (u ∩ v) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro y ⟨⟨-, hyne⟩, hy1, hy2⟩
    refine hyne (Subtype.ext (funext fun i => ?_))
    fin_cases i
    exact le_antisymm hy1 hy2
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre) u v hucl hvcl hsu hdisj with hsub | hsub
  · exact (not_le.mpr hv₀gt) (hsub hv₀s)
  · exact (not_le.mpr hu₀lt) (hsub hu₀s)

/-- Plane-domain corollary: a set in `ℂ` that lies in an open set and is homeomorphic to the model
open interval has empty interior. -/
theorem empty_interior_of_homeomorph_interval {U A : Set ℂ} (hU : IsOpen U) (hA : A ⊆ U)
    (h : Nonempty (↥A ≃ₜ ↥(Metric.ball (0 : Fin 1 → ℝ) 1))) : interior A = ∅ := by
  rw [← not_nonempty_iff_eq_empty]
  rintro ⟨z, hz⟩
  obtain ⟨ε, hε, hεA⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  obtain ⟨ε', hε', hε'U⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hA (interior_subset hz)))
  set ρ : ℝ := min ε ε' with hρdef
  have hρpos : 0 < ρ := lt_min hε hε'
  have hballA : Metric.ball z ρ ⊆ A := fun w hw =>
    hεA (Metric.ball_subset_ball (min_le_left _ _) hw)
  have hzρ : z ∈ Metric.ball z ρ := by simpa using hρpos
  exact (not_mem_interior_of_homeomorph_interval hballA hzρ Metric.isOpen_ball
    (isPreconnected_ball_diff_center z ρ hρpos) h) hz

/-- **A set homeomorphic to an open interval has empty interior in a surface** (`ChartedSpace ℂ X`,
no smoothness needed).  The chart ball supplies the open `β` with preconnected punctured version. -/
theorem empty_interior_of_homeomorph_interval_of_chartedSpace {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {A : Set X}
    (h : Nonempty (↥A ≃ₜ ↥(Metric.ball (0 : Fin 1 → ℝ) 1))) : interior A = ∅ := by
  rw [← not_nonempty_iff_eq_empty]
  rintro ⟨z, hz⟩
  obtain ⟨V, hVA, hVopen, hzV⟩ := mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  set e : OpenPartialHomeomorph X ℂ := chartAt ℂ z with he
  have hzsrc : z ∈ e.source := mem_chart_source ℂ z
  have hze : e z ∈ e.target := e.map_source hzsrc
  have hpre : (⇑e.symm) ⁻¹' V ∈ nhds (e z) :=
    (e.continuousAt_symm hze).preimage_mem_nhds
      (by rw [e.left_inv hzsrc]; exact hVopen.mem_nhds hzV)
  obtain ⟨ρ, hρ, hρsub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hpre (e.open_target.mem_nhds hze))
  set β : Set X := e.source ∩ (⇑e) ⁻¹' Metric.ball (e z) ρ with hβdef
  have hβopen : IsOpen β := e.isOpen_inter_preimage Metric.isOpen_ball
  have hzβ : z ∈ β := by
    refine ⟨hzsrc, ?_⟩
    show (⇑e) z ∈ Metric.ball ((⇑e) z) ρ
    rw [Metric.mem_ball]
    simpa using hρ
  have hβA : β ⊆ A := by
    rintro y ⟨hysrc, hyB⟩
    have h1 : e.symm (e y) ∈ V := (hρsub hyB).1
    rw [e.left_inv hysrc] at h1
    exact hVA h1
  have hβpre : IsPreconnected (β \ {z}) := by
    have himg : β \ {z} = e.symm '' (Metric.ball (e z) ρ \ {e z}) := by
      ext y
      constructor
      · rintro ⟨⟨hysrc, hyB⟩, hyz⟩
        refine ⟨e y, ⟨hyB, ?_⟩, e.left_inv hysrc⟩
        intro hh
        refine hyz ?_
        rw [Set.mem_singleton_iff] at hh ⊢
        rw [← e.left_inv hysrc, hh, e.left_inv hzsrc]
      · rintro ⟨w, ⟨hwB, hwne⟩, rfl⟩
        refine ⟨⟨e.map_target ((hρsub hwB).2), ?_⟩, ?_⟩
        · show (⇑e) (e.symm w) ∈ Metric.ball ((⇑e) z) ρ
          rw [e.right_inv ((hρsub hwB).2)]; exact hwB
        · intro hh
          refine hwne ?_
          have h2 := congrArg (⇑e) hh
          rwa [e.right_inv ((hρsub hwB).2)] at h2
    rw [himg]
    exact (isPreconnected_ball_diff_center (e z) ρ hρ).image (⇑e.symm)
      (e.continuousOn_symm.mono (fun w hw => (hρsub hw.1).2))
  exact (not_mem_interior_of_homeomorph_interval hβA hzβ hβopen hβpre h) hz

theorem not_isOpen_singleton_of_chartedSpace {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) : ¬ IsOpen ({x} : Set X) := by
  intro hopen
  set e : OpenPartialHomeomorph X ℂ := chartAt ℂ x with he
  have hxsrc : x ∈ e.source := mem_chart_source ℂ x
  have hxe : e x ∈ e.target := e.map_source hxsrc
  have hpre : (⇑e.symm) ⁻¹' ({x} ∩ e.source) ∈ nhds (e x) :=
    (e.continuousAt_symm hxe).preimage_mem_nhds
      ((hopen.inter e.open_source).mem_nhds ⟨by rw [e.left_inv hxsrc]; rfl,
        by rw [e.left_inv hxsrc]; exact hxsrc⟩)
  obtain ⟨ρ, hρ, hρsub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hpre (e.open_target.mem_nhds hxe))
  obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := e x) (r := ρ / 2)).mpr (by linarith)
  have hwball : w ∈ Metric.ball (e x) ρ := by
    rw [Metric.mem_ball, hw]; linarith
  have hsub := hρsub hwball
  have hwin : w = e x := by
    have h1 : e.symm w ∈ ({x} : Set X) ∩ e.source := hsub.1
    have h2 : e.symm w = x := Set.mem_singleton_iff.mp h1.1
    rw [← e.right_inv hsub.2, h2]
  rw [Metric.mem_sphere] at hw
  rw [hwin, dist_self] at hw
  linarith

/-- Consequently the punctured neighbourhood filter at every point is nontrivial. -/
theorem punctured_nhds_neBot_of_chartedSpace {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (x : X) : (nhdsWithin x {x}ᶜ).NeBot :=
  Filter.neBot_iff.mpr fun hbot =>
    not_isOpen_singleton_of_chartedSpace x ((isOpen_singleton_iff_punctured_nhds x).mpr hbot)

/-- **A finite set of a space without isolated points contains no nonempty open set**: a nonempty
open finite set has an open singleton. -/
theorem exists_isOpen_singleton_of_isOpen_finite {X : Type*} [TopologicalSpace X] [T1Space X]
    {V : Set X} (hV : IsOpen V) (hne : V.Nonempty) (hfin : V.Finite) :
    ∃ y ∈ V, IsOpen ({y} : Set X) := by
  classical
  have key : ∀ T : Finset X, IsOpen ((T : Set X)) → T.Nonempty →
      ∃ y ∈ (T : Set X), IsOpen ({y} : Set X) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _ hne; exact absurd hne (by simp)
    | insert a s has ih =>
      intro hTopen hne
      by_cases ha : IsOpen ({a} : Set X)
      · exact ⟨a, Finset.mem_insert_self a s, ha⟩
      · have hsopen : IsOpen ((s : Set X)) := by
          have h1 : ((s : Set X)) = ((insert a s : Finset X) : Set X) \ {a} := by
            ext y
            simp only [mem_sdiff, mem_singleton_iff, Finset.mem_coe, Finset.mem_insert]
            constructor
            · intro hy; exact ⟨Or.inr hy, fun h => has (h ▸ hy)⟩
            · rintro ⟨hy, hya⟩
              rcases hy with rfl | hy
              · exact absurd rfl hya
              · exact hy
          rw [h1]
          exact hTopen.sdiff isClosed_singleton
        have hsne : s.Nonempty := by
          rcases s.eq_empty_or_nonempty with h | h
          · exfalso
            apply ha
            have h2 : ((insert a s : Finset X) : Set X) = ({a} : Set X) := by
              rw [h]; simp
            rw [← h2]; exact hTopen
          · exact h
        obtain ⟨y, hy, hyopen⟩ := ih hsopen hsne
        exact ⟨y, Finset.mem_insert_of_mem hy, hyopen⟩
  have hne' : hfin.toFinset.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, by rw [← Finset.mem_coe, hfin.coe_toFinset]; exact hy⟩
  obtain ⟨y, hy, hyopen⟩ := key hfin.toFinset (by rw [hfin.coe_toFinset]; exact hV) hne'
  exact ⟨y, by rwa [hfin.coe_toFinset] at hy, hyopen⟩

/-- Adjoining a finite set does not create interior, in a space without isolated points. -/
theorem interior_union_finite_eq_empty {X : Type*} [TopologicalSpace X] [T1Space X]
    (hiso : ∀ x : X, (nhdsWithin x {x}ᶜ).NeBot) {A F : Set X} (hA : interior A = ∅)
    (hF : F.Finite) : interior (A ∪ F) = ∅ := by
  rw [← not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  obtain ⟨V, hVA, hVopen, hxV⟩ := mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  rcases (V \ F).eq_empty_or_nonempty with hemp | hne
  · -- V ⊆ F, so V is a nonempty open finite set: it has an open singleton
    have hVF : V ⊆ F := by
      intro y hy
      by_contra h
      have h2 : y ∈ V \ F := ⟨hy, h⟩
      rw [hemp] at h2
      exact absurd h2 (by simp)
    obtain ⟨y, hyV, hyopen⟩ := exists_isOpen_singleton_of_isOpen_finite hVopen ⟨x, hxV⟩
      (hF.subset hVF)
    exact (hiso y).ne ((isOpen_singleton_iff_punctured_nhds y).mp hyopen)
  · obtain ⟨y, hy⟩ := hne
    have hsub : V \ F ⊆ A := fun z hz => (hVA hz.1).resolve_right hz.2
    have : y ∈ interior A := interior_maximal hsub (hVopen.sdiff hF.isClosed) hy
    rw [hA] at this
    exact this

/-- **The open `1`-cell of a CW complex is homeomorphic to the model open interval.** -/
theorem nonempty_homeomorph_openCell_one {X : Type*} [TopologicalSpace X] {C : Set X}
    [hC : Topology.CWComplex C] (j : Topology.CWComplex.cell C 1) :
    Nonempty (↥(Metric.ball (0 : Fin 1 → ℝ) 1) ≃ₜ
      ↥((hC.map 1 j) '' Metric.ball (0 : Fin 1 → ℝ) 1)) := by
  have hsrc : (hC.map 1 j).source = Metric.ball (0 : Fin 1 → ℝ) 1 := hC.source_eq 1 j
  have htrg : (hC.map 1 j).target = (hC.map 1 j) '' Metric.ball (0 : Fin 1 → ℝ) 1 := by
    rw [← PartialEquiv.image_source_eq_target, hsrc]
  have hmem : ∀ z : ↥((hC.map 1 j) '' Metric.ball (0 : Fin 1 → ℝ) 1),
      (hC.map 1 j).symm z.1 ∈ Metric.ball (0 : Fin 1 → ℝ) 1 := by
    intro z
    have hz : z.1 ∈ (hC.map 1 j).target := by rw [htrg]; exact z.2
    simpa [hsrc] using (hC.map 1 j).map_target hz
  refine ⟨Homeomorph.mk
    { toFun := fun y => ⟨(hC.map 1 j) y.1, ⟨y.1, y.2, rfl⟩⟩
      invFun := fun z => ⟨(hC.map 1 j).symm z.1, hmem z⟩
      left_inv := fun y => Subtype.ext ((hC.map 1 j).left_inv (by rw [hsrc]; exact y.2))
      right_inv := fun z => Subtype.ext ((hC.map 1 j).right_inv (by rw [htrg]; exact z.2)) }
    ?_ ?_⟩
  · have h1 : ContinuousOn (⇑(hC.map 1 j)) (Metric.closedBall (0 : Fin 1 → ℝ) 1) :=
      hC.continuousOn 1 j
    have h2 : Continuous fun y : ↥(Metric.ball (0 : Fin 1 → ℝ) 1) =>
        (⇑(hC.map 1 j)) y.1 := by
      have := h1.mono Metric.ball_subset_closedBall
      rwa [continuousOn_iff_continuous_domRestrict] at this
    exact h2.subtype_mk _
  · have h1 : ContinuousOn (⇑(hC.map 1 j).symm) (hC.map 1 j).target :=
      hC.continuousOn_symm 1 j
    rw [htrg] at h1
    have h2 : Continuous fun z : ↥((hC.map 1 j) '' Metric.ball (0 : Fin 1 → ℝ) 1) =>
        (⇑(hC.map 1 j).symm) z.1 := by
      rwa [continuousOn_iff_continuous_domRestrict] at h1
    exact h2.subtype_mk _


/-- The open `1`-cell of a *relative* CW complex is homeomorphic to the model open interval. -/
theorem nonempty_homeomorph_map_ball_one {X : Type*} [TopologicalSpace X] {C : Set X}
    [hC : Topology.RelCWComplex C (∅ : Set X)] (j : Topology.RelCWComplex.cell C 1) :
    Nonempty (↥(Metric.ball (0 : Fin 1 → ℝ) 1) ≃ₜ
      ↥((Topology.RelCWComplex.map (C := C) 1 j) '' Metric.ball (0 : Fin 1 → ℝ) 1)) := by
  have hsrc : (Topology.RelCWComplex.map (C := C) 1 j).source
      = Metric.ball (0 : Fin 1 → ℝ) 1 := Topology.RelCWComplex.source_eq 1 j
  have htrg : (Topology.RelCWComplex.map (C := C) 1 j).target
      = (Topology.RelCWComplex.map (C := C) 1 j) '' Metric.ball (0 : Fin 1 → ℝ) 1 := by
    rw [← PartialEquiv.image_source_eq_target, hsrc]
  have hmem : ∀ z : ↥((Topology.RelCWComplex.map (C := C) 1 j)
        '' Metric.ball (0 : Fin 1 → ℝ) 1),
      (Topology.RelCWComplex.map (C := C) 1 j).symm z.1 ∈ Metric.ball (0 : Fin 1 → ℝ) 1 := by
    intro z
    have hz : z.1 ∈ (Topology.RelCWComplex.map (C := C) 1 j).target := by rw [htrg]; exact z.2
    simpa [hsrc] using (Topology.RelCWComplex.map (C := C) 1 j).map_target hz
  refine ⟨Homeomorph.mk
    { toFun := fun y => ⟨(Topology.RelCWComplex.map (C := C) 1 j) y.1, ⟨y.1, y.2, rfl⟩⟩
      invFun := fun z => ⟨(Topology.RelCWComplex.map (C := C) 1 j).symm z.1, hmem z⟩
      left_inv := fun y => Subtype.ext
        ((Topology.RelCWComplex.map (C := C) 1 j).left_inv (by rw [hsrc]; exact y.2))
      right_inv := fun z => Subtype.ext
        ((Topology.RelCWComplex.map (C := C) 1 j).right_inv (by rw [htrg]; exact z.2)) }
    ?_ ?_⟩
  · have h1 : ContinuousOn (⇑(Topology.RelCWComplex.map (C := C) 1 j))
        (Metric.closedBall (0 : Fin 1 → ℝ) 1) := Topology.RelCWComplex.continuousOn 1 j
    have h2 : Continuous fun y : ↥(Metric.ball (0 : Fin 1 → ℝ) 1) =>
        (⇑(Topology.RelCWComplex.map (C := C) 1 j)) y.1 := by
      have := h1.mono Metric.ball_subset_closedBall
      rwa [continuousOn_iff_continuous_domRestrict] at this
    exact h2.subtype_mk _
  · have h1 : ContinuousOn (⇑(Topology.RelCWComplex.map (C := C) 1 j).symm)
        (Topology.RelCWComplex.map (C := C) 1 j).target :=
      Topology.RelCWComplex.continuousOn_symm 1 j
    rw [htrg] at h1
    have h2 : Continuous fun z : ↥((Topology.RelCWComplex.map (C := C) 1 j)
          '' Metric.ball (0 : Fin 1 → ℝ) 1) =>
        (⇑(Topology.RelCWComplex.map (C := C) 1 j).symm) z.1 := by
      rwa [continuousOn_iff_continuous_domRestrict] at h1
    exact h2.subtype_mk _

/-- **No loop-hole (relative form): a surface is not a one-dimensional CW complex.** -/
theorem not_relCwComplex_oneDim_of_chartedSpace {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [Nonempty X]
    [hC : Topology.RelCWComplex (Set.univ : Set X) (∅ : Set X)]
    (hcnt : ∀ n : ℕ, Countable (Topology.RelCWComplex.cell (Set.univ : Set X) n))
    (hdim : ∀ n : ℕ, 2 ≤ n → IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set X) n)) :
    False := by
  classical
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : BaireSpace X := BaireSpace.of_t2Space_locallyCompactSpace
  have hclosed : ∀ p : Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n,
      IsClosed ((Topology.RelCWComplex.map p.1 p.2) '' Metric.closedBall (0 : Fin p.1 → ℝ) 1) :=
    fun p => (IsCompact.image_of_continuousOn (isCompact_closedBall (0 : Fin p.1 → ℝ) 1)
      (Topology.RelCWComplex.continuousOn p.1 p.2)).isClosed
  have hcov : (⋃ p : Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n,
      (Topology.RelCWComplex.map p.1 p.2) '' Metric.closedBall (0 : Fin p.1 → ℝ) 1)
      = (Set.univ : Set X) := by
    have h := Topology.RelCWComplex.union (C := (Set.univ : Set X)) (D := (∅ : Set X))
    rw [Set.empty_union] at h
    rw [Set.iUnion_sigma'] at h
    simpa only [Topology.RelCWComplex.closedCell] using h
  haveI : Countable (Σ n : ℕ, Topology.RelCWComplex.cell (Set.univ : Set X) n) := by
    have h2 : ∀ n : ℕ, Countable (Topology.RelCWComplex.cell (Set.univ : Set X) n) := hcnt
    infer_instance
  obtain ⟨p, hp⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun p : Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n =>
      (Topology.RelCWComplex.map p.1 p.2) '' Metric.closedBall (0 : Fin p.1 → ℝ) 1) hclosed hcov
  rcases p with ⟨n, j⟩
  rcases lt_or_ge n 2 with hn | hn
  swap
  · exact (hdim n hn).false j
  · interval_cases n
    · -- a 0-cell is a single point
      have hpt : (Topology.RelCWComplex.map 0 j) '' Metric.closedBall (0 : Fin 0 → ℝ) 1
          = {((Topology.RelCWComplex.map 0 j) default : X)} := by
        have h0 : (default : Fin 0 → ℝ) = 0 := Subsingleton.elim _ _
        refine Set.eq_singleton_iff_unique_mem.mpr
          ⟨⟨default, by simp [Metric.mem_closedBall, h0]⟩, ?_⟩
        rintro y ⟨w, -, rfl⟩
        exact congrArg (fun t => ((Topology.RelCWComplex.map 0 j) t : X))
          (Subsingleton.elim w default)
      rw [hpt] at hp
      haveI := punctured_nhds_neBot_of_chartedSpace ((Topology.RelCWComplex.map 0 j) default)
      rw [interior_singleton] at hp
      rcases hp with ⟨y, hy⟩
      exact absurd hy (by simp)
    · -- a 1-cell is an open interval plus a finite set
      have hdecomp : (Topology.RelCWComplex.map 1 j) '' Metric.closedBall (0 : Fin 1 → ℝ) 1
          = (Topology.RelCWComplex.map 1 j) '' Metric.ball (0 : Fin 1 → ℝ) 1
            ∪ ((Topology.RelCWComplex.map 1 j) '' Metric.sphere (0 : Fin 1 → ℝ) 1) := by
        rw [← Metric.ball_union_sphere, Set.image_union]
      obtain ⟨I, hI⟩ := Topology.RelCWComplex.mapsTo (C := (Set.univ : Set X)) (D := (∅ : Set X)) 1 j
      have hsub : ((Topology.RelCWComplex.map 1 j) '' Metric.sphere (0 : Fin 1 → ℝ) 1) ⊆
          ⋃ i ∈ I 0, {((Topology.RelCWComplex.map 0 i) default : X)} := by
        intro y hy
        obtain ⟨w, hw, rfl⟩ := hy
        have h1 := hI hw
        simp only [Set.mem_union, Set.mem_empty_iff_false, false_or] at h1
        obtain ⟨m, h1⟩ := Set.mem_iUnion.mp h1
        obtain ⟨hm, h1⟩ := Set.mem_iUnion.mp h1
        obtain ⟨i, hi, h1⟩ := Set.mem_iUnion₂.mp h1
        obtain ⟨u, -, hwu⟩ := h1
        obtain rfl : m = 0 := by omega
        refine Set.mem_iUnion₂.mpr ⟨i, hi, Set.mem_singleton_iff.mpr ?_⟩
        rw [← hwu, Subsingleton.elim u default]
      have hfin : ((Topology.RelCWComplex.map 1 j) '' Metric.sphere (0 : Fin 1 → ℝ) 1).Finite :=
        ((I 0).finite_toSet.biUnion fun i _ => Set.finite_singleton _).subset hsub
      have hthin : interior ((Topology.RelCWComplex.map 1 j) '' Metric.ball (0 : Fin 1 → ℝ) 1)
          = ∅ :=
        empty_interior_of_homeomorph_interval_of_chartedSpace
          ((nonempty_homeomorph_map_ball_one (C := (Set.univ : Set X)) j).map
            fun e => e.symm)
      rw [hdecomp, interior_union_finite_eq_empty
        (fun x => punctured_nhds_neBot_of_chartedSpace x) hthin hfin] at hp
      rcases hp with ⟨y, hy⟩
      exact absurd hy (by simp)

/-- **No loop-hole: a surface is not a one-dimensional CW complex** (absolute CW complex form). -/
theorem not_cwComplex_oneDim_of_chartedSpace {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [Nonempty X]
    (hC : Topology.CWComplex (Set.univ : Set X))
    (hcnt : ∀ n : ℕ, Countable (hC.cell n))
    (hdim : ∀ n : ℕ, 2 ≤ n → IsEmpty (hC.cell n)) : False := by
  letI := hC
  haveI : Topology.RelCWComplex (Set.univ : Set X) (∅ : Set X) :=
    Topology.CWComplex.instRelCWComplex (Set.univ : Set X)
  exact @not_relCwComplex_oneDim_of_chartedSpace X _ _ _ _
    (Topology.CWComplex.instRelCWComplex (Set.univ : Set X)) hcnt hdim


/-- **The nerve (adjacency graph) of a locally finite closed cover of a preconnected space is
connected.**  This is the combinatorial input of the "forest spine" construction: it says that a
locally finite closed cover by nonempty sets of a connected space has a connected dual graph, hence
admits a spanning tree. -/
theorem relation_reflTransGen_of_locallyFinite_closed_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} {D : ι → Set X} (hcl : ∀ i, IsClosed (D i)) (hlf : LocallyFinite D)
    (hne : ∀ i, (D i).Nonempty) (hcov : (⋃ i, D i) = Set.univ)
    (hpc : IsPreconnected (Set.univ : Set X)) (i j : ι) :
    Relation.ReflTransGen (fun a b => (D a ∩ D b).Nonempty) i j := by
  classical
  by_contra hij
  set K : Set ι := {a | Relation.ReflTransGen (fun a b => (D a ∩ D b).Nonempty) i a} with hKdef
  have hiK : i ∈ K := Relation.ReflTransGen.refl
  have hstep : ∀ a ∈ K, ∀ b, (D a ∩ D b).Nonempty → b ∈ K := fun a ha b hab => ha.tail hab
  have hlfK : LocallyFinite (fun a : K => D a.1) := by
    intro x
    obtain ⟨t, ht, hfin⟩ := hlf x
    refine ⟨t, ht, ?_⟩
    have himg : (Subtype.val '' {a : K | (D a.1 ∩ t).Nonempty}) ⊆ {i : ι | (D i ∩ t).Nonempty} := by
      rintro i ⟨a, ha, rfl⟩
      exact ha
    exact (hfin.subset himg).of_finite_image (fun a _ b _ hab => Subtype.val_injective hab)
  have hlfKc : LocallyFinite (fun a : {a // a ∉ K} => D a.1) := by
    intro x
    obtain ⟨t, ht, hfin⟩ := hlf x
    refine ⟨t, ht, ?_⟩
    have himg : (Subtype.val '' {a : {a // a ∉ K} | (D a.1 ∩ t).Nonempty}) ⊆
        {i : ι | (D i ∩ t).Nonempty} := by
      rintro i ⟨a, ha, rfl⟩
      exact ha
    exact (hfin.subset himg).of_finite_image (fun a _ b _ hab => Subtype.val_injective hab)
  have hclosedU : IsClosed (⋃ a : K, D a.1) :=
    hlfK.isClosed_iUnion fun a => hcl a.1
  have hclosedV : IsClosed (⋃ a : {a // a ∉ K}, D a.1) :=
    hlfKc.isClosed_iUnion fun a => hcl a.1
  have hunion : (⋃ a : K, D a.1) ∪ (⋃ a : {a // a ∉ K}, D a.1) = Set.univ := by
    rw [← hcov]
    refine le_antisymm ?_ ?_
    · rintro x (hx | hx)
      · exact mem_iUnion.mpr ⟨(mem_iUnion.mp hx).choose.1, (mem_iUnion.mp hx).choose_spec⟩
      · exact mem_iUnion.mpr ⟨(mem_iUnion.mp hx).choose.1, (mem_iUnion.mp hx).choose_spec⟩
    · intro x hx
      rcases mem_iUnion.mp hx with ⟨a, ha⟩
      by_cases h : a ∈ K
      · exact Or.inl (mem_iUnion.mpr ⟨⟨a, h⟩, ha⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨a, h⟩, ha⟩)
  have hdisj : (⋃ a : K, D a.1) ∩ (⋃ a : {a // a ∉ K}, D a.1) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    rcases mem_iUnion.mp hx1 with ⟨a, ha⟩
    rcases mem_iUnion.mp hx2 with ⟨b, hb⟩
    exact b.2 (hstep a.1 a.2 b.1 ⟨x, ha, hb⟩)
  have hUne : (⋃ a : K, D a.1).Nonempty := by
    obtain ⟨x, hx⟩ := hne i
    exact ⟨x, mem_iUnion.mpr ⟨⟨i, hiK⟩, hx⟩⟩
  have hVne : (⋃ a : {a // a ∉ K}, D a.1).Nonempty := by
    obtain ⟨x, hx⟩ := hne j
    exact ⟨x, mem_iUnion.mpr ⟨⟨j, hij⟩, hx⟩⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpc)
      (⋃ a : K, D a.1) (⋃ a : {a // a ∉ K}, D a.1) hclosedU hclosedV
      (by rw [hunion]) (by rw [univ_inter, hdisj]) with hsub | hsub
  · obtain ⟨x, hx⟩ := hVne
    have : x ∈ (⋃ a : K, D a.1) ∩ (⋃ a : {a // a ∉ K}, D a.1) := ⟨hsub trivial, hx⟩
    rw [hdisj] at this
    exact this
  · obtain ⟨x, hx⟩ := hUne
    have : x ∈ (⋃ a : K, D a.1) ∩ (⋃ a : {a // a ∉ K}, D a.1) := ⟨hx, hsub trivial⟩
    rw [hdisj] at this
    exact this

/-- **A connected relation has a spanning tree** (packaging of Mathlib's
`SimpleGraph.Connected.exists_isTree_le`, and the combinatorial input of every "wall system" design:
the walls of a spine are indexed by the edges of a spanning tree of the dual graph). -/
theorem exists_isTree_spanning_of_connected_relation {ι : Type*} [Nonempty ι] {R : ι → ι → Prop}
    (hconn : ∀ a b, Relation.ReflTransGen R a b) :
    ∃ T : SimpleGraph ι, T ≤ SimpleGraph.fromRel R ∧ T.IsTree := by
  have hreach : ∀ a b, Relation.ReflTransGen (SimpleGraph.fromRel R).Adj a b := by
    intro a b
    induction hconn a b with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        rename_i b c
        by_cases h : b = c
        · subst h; exact ih
        · exact ih.tail ⟨h, Or.inl hbc⟩
  have hconn' : (SimpleGraph.fromRel R).Connected :=
    ⟨fun a b => (SimpleGraph.reachable_iff_reflTransGen a b).mpr (hreach a b)⟩
  obtain ⟨T, hT, hTtree⟩ := hconn'.exists_isTree_le
  exact ⟨T, hT, hTtree⟩

/-- **The dual graph of a locally finite closed cover of a preconnected space by nonempty closed
sets has a spanning tree.**  The vertices are the members of the cover and two members are adjacent
when they meet; `exists_isTree_spanning_of_connected_relation` upgrades the connectedness
(`relation_reflTransGen_of_locallyFinite_closed_cover`) to a tree. -/
theorem exists_isTree_of_locallyFinite_closed_cover {X : Type*} [TopologicalSpace X] [Nonempty X]
    {ι : Type*} {D : ι → Set X} (hcl : ∀ i, IsClosed (D i)) (hlf : LocallyFinite D)
    (hne : ∀ i, (D i).Nonempty) (hcov : (⋃ i, D i) = Set.univ)
    (hpc : IsPreconnected (Set.univ : Set X)) :
    ∃ T : SimpleGraph ι, (∀ a b, T.Adj a b → (D a ∩ D b).Nonempty) ∧ T.IsTree := by
  have hι : Nonempty ι := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have hx : x ∈ ⋃ i, D i := by rw [hcov]; exact mem_univ x
    obtain ⟨i, -⟩ := mem_iUnion.mp hx
    exact ⟨i⟩
  obtain ⟨T, hT, hTtree⟩ := exists_isTree_spanning_of_connected_relation (ι := ι)
    (R := fun a b => (D a ∩ D b).Nonempty)
    (fun a b => relation_reflTransGen_of_locallyFinite_closed_cover hcl hlf hne hcov hpc a b)
  refine ⟨T, ?_, hTtree⟩
  intro a b hab
  have h := hT hab
  rw [SimpleGraph.fromRel_adj] at h
  rcases h with ⟨-, h | h⟩
  · exact h
  · rwa [Set.inter_comm] at h

/-- **The rooted-tree parent step.**  In a tree `T` rooted at `r`, every vertex `v ≠ r` has a neighbour
`w` one step closer to the root: `T.dist w r + 1 = T.dist v r`.  This is what orients the spanning tree
of the tiling's dual graph away from a root, i.e. what gives every tile its parent (and hence the wall
it folds onto) in the cut-system cascade.

Proof: `hT.connected.exists_walk_length_eq_dist` gives a shortest walk `p` from `v` to `r`; matching on
`p`, the `cons` case exposes the first step `v – w` and the tail `q`, and the tail is shortest because a
shortest walk from `w` to `r` together with the edge gives `T.dist v r ≤ T.dist w r + 1`, while
`T.dist w r ≤ q.length` and `T.dist v r = q.length + 1`; `omega` finishes. -/
theorem exists_parent_dist_succ {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) (r : V) {v : V}
    (hv : v ≠ r) : ∃ w : V, T.Adj v w ∧ T.dist w r + 1 = T.dist v r := by
  have hconn : T.Connected := hT.connected
  obtain ⟨p, hp⟩ := (hconn v r).exists_walk_length_eq_dist
  match p with
  | .nil => exact absurd rfl hv
  | .cons h q =>
    rename_i w
    refine ⟨w, h, ?_⟩
    have hlen : (SimpleGraph.Walk.cons h q).length = q.length + 1 := rfl
    have hv' : T.dist v r = q.length + 1 := by rw [← hp]; exact hlen
    have hq : T.dist w r ≤ q.length := SimpleGraph.dist_le q
    obtain ⟨ρ, hρ⟩ := (hconn w r).exists_walk_length_eq_dist
    have hup : T.dist v r ≤ T.dist w r + 1 := by
      have hcons : (SimpleGraph.Walk.cons h ρ).length = ρ.length + 1 := rfl
      have := SimpleGraph.dist_le (SimpleGraph.Walk.cons h ρ)
      omega
    omega

/-- **Tile data for the cut-system cascade.**  From the smooth disk tiling
(`Commons.Topology.Surface.exists_locallyFinite_disk_tiling`) and the spanning tree of its dual graph
(`exists_isTree_of_locallyFinite_closed_cover`) we obtain in one package: the tiling structure, the
compactness and nonemptiness of every tile, a chosen **centre** in each tile, finiteness of the set of
tiles meeting a given tile (local finiteness + compactness), and the tree with its nonempty walls
(one gate point per tree edge can be chosen from the wall nonemptiness).

The three separation hypotheses of the fold (`convex_deformationRetract_of_wall_and_fan`) are what
must be verified next; the one input not yet available from the tiling's statement is
`(interior (D i)).Nonempty`, which is needed for the centre to be an *interior* point. -/
theorem exists_tile_data {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    ∃ (ι : Type) (D : ι → Set X) (c : ι → X) (T : SimpleGraph ι),
      LocallyFinite D ∧ (⋃ i, D i) = Set.univ ∧ (∀ i, IsClosed (D i)) ∧
      (∀ i, IsCompact (D i)) ∧ (∀ i, (D i).Nonempty) ∧ (∀ i, c i ∈ D i) ∧
      (∀ i, {j | (D j ∩ D i).Nonempty}.Finite) ∧
      (∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅) ∧
      T.IsTree ∧ (∀ a b, T.Adj a b → (D a ∩ D b).Nonempty) := by
  classical
  obtain ⟨ι, D, hlf, hcov, hcl, hdisk, hdisj⟩ :=
    Commons.Topology.Surface.exists_locallyFinite_disk_tiling (X := X)
  have hne : ∀ i, (D i).Nonempty := by
    intro i
    obtain ⟨e⟩ := hdisk i
    exact ⟨((e ⟨0, Metric.mem_closedBall_self (by norm_num)⟩ : ↥(D i)) : X),
      (e ⟨0, Metric.mem_closedBall_self (by norm_num)⟩).2⟩
  have hcomp : ∀ i, IsCompact (D i) := by
    intro i
    obtain ⟨e⟩ := hdisk i
    haveI : CompactSpace ↥(Metric.closedBall (0:ℂ) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)
    exact isCompact_iff_compactSpace.mpr e.compactSpace
  haveI : Nonempty X := ConnectedSpace.toNonempty
  obtain ⟨T, hT, hTtree⟩ := exists_isTree_of_locallyFinite_closed_cover (D := D) hcl hlf hne hcov
    (isPreconnected_univ : IsPreconnected (Set.univ : Set X))
  choose c hc using fun i => hne i
  have hfin : ∀ i, {j | (D j ∩ D i).Nonempty}.Finite := fun i =>
    hlf.finite_nonempty_inter_compact (hcomp i)
  exact ⟨ι, D, c, T, hlf, hcov, hcl, hcomp, hne, hc, hfin, hdisj, hTtree, hT⟩

/-- **Parent-wall gates** (the first separation hypothesis of the fold, in data form).  Given the
tiling and the spanning tree of its dual, every tree edge `{i,j}` carries a **gate point** lying in
the corresponding wall `D i ∩ D j`; for a tile whose parent is `p` this is the point `g 0` of
`convex_deformationRetract_of_wall_and_fan`, and `g 0 ∈ W` is precisely
`gate ⟨(i,parent), adj⟩ ∈ D i ∩ D parent`. -/
theorem exists_parent_gate {X : Type*} {ι : Type*} {D : ι → Set X} {T : SimpleGraph ι}
    (hwall : ∀ a b, T.Adj a b → (D a ∩ D b).Nonempty) :
    ∃ gate : {p : ι × ι // T.Adj p.1 p.2} → X,
      ∀ p, gate p ∈ D p.1.1 ∩ D p.1.2 := by
  classical
  choose gate hgate using hwall
  exact ⟨fun p => gate p.1.1 p.1.2 p.2, fun p => hgate p.1.1 p.1.2 p.2⟩

/-- **The gate condition, discharged geometrically.**  If `Q` is convex, `c` is an interior point,
`p ∈ Q`, and `x ∈ [c,p]` with `x ≠ p`, then `x ∈ interior Q`.  Consequently, whenever the wall sits
in the frontier of the tile (`W ⊆ frontier Q`), the segment `[c,p]` meets `W` only at the gate `p` —
which is exactly the hypothesis `hseg0` of `convex_deformationRetract_of_wall_and_fan`. -/
theorem segment_diff_right_subset_interior {Q : Set ℂ} (hQ : Convex ℝ Q) {c p x : ℂ}
    (hc : c ∈ interior Q) (hp : p ∈ Q) (hx : x ∈ segment ℝ c p) (hxp : x ≠ p) :
    x ∈ interior Q := by
  rw [segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have ht1 : t < 1 := by
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact h
    · exfalso; apply hxp
      rw [h]; simp
  have ha : 0 < 1 - t := by linarith
  have hb : 0 ≤ t := ht.1
  have hab : (1 - t) + t = 1 := by ring
  have := hQ.combo_interior_self_mem_interior (x := c) (y := p) hc hp ha hb hab
  convert this using 2

/-- **The gate condition, final form.**  For convex `Q`, the segment from an interior point `c` to a
point `p ∈ Q` meets the *frontier* of `Q` at most in the endpoint `p`.  Applied to a wall
`W ⊆ frontier (D i)` this is exactly the hypothesis `hseg0` of the tile fold: the first leg meets the
parent wall only at the gate. -/
theorem segment_inter_frontier_subset_singleton {Q : Set ℂ} (hQ : Convex ℝ Q) {c p : ℂ}
    (hc : c ∈ interior Q) (hp : p ∈ Q) :
    segment ℝ c p ∩ frontier Q ⊆ {p} := by
  rintro x ⟨hxseg, hxfr⟩
  by_cases hxp : x = p
  · exact mem_singleton_iff.mpr hxp
  · have hint : x ∈ interior Q := segment_diff_right_subset_interior hQ hc hp hxseg hxp
    rw [← closure_sdiff_interior] at hxfr
    exact absurd hint hxfr.2

open Commons.Topology.Plane in
/-- A closed dyadic cell is closed in `ℂ`. -/
theorem isClosed_dyadicCell (n : ℕ) (p : ℤ × ℤ) : IsClosed (dyadicCell n p) := by
  have h1 : IsClosed {z : ℂ | (p.1 : ℝ) / 2 ^ n ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have h2 : IsClosed {z : ℂ | z.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n} :=
    isClosed_le Complex.continuous_re continuous_const
  have h3 : IsClosed {z : ℂ | (p.2 : ℝ) / 2 ^ n ≤ z.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have h4 : IsClosed {z : ℂ | z.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n} :=
    isClosed_le Complex.continuous_im continuous_const
  have h5 : dyadicCell n p = {z : ℂ | (p.1 : ℝ) / 2 ^ n ≤ z.re} ∩
      {z : ℂ | z.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n} ∩
      {z : ℂ | (p.2 : ℝ) / 2 ^ n ≤ z.im} ∩
      {z : ℂ | z.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n} := by
    ext z; simp [dyadicCell, and_assoc]
  rw [h5]
  exact ((h1.inter h2).inter h3).inter h4

open Commons.Topology.Plane in
/-- **The maximal dyadic cells tile a plane domain**: a locally finite cover of `U ⊆ ℂ` (open) by
closed dyadic cells contained in `U` with pairwise disjoint interiors.  This is the smoothness-free
version of the input of `Commons.Topology.Surface.exists_locallyFinite_disk_tiling` (which needs
`IsManifold`); each tile is moreover a closed axis-parallel square, hence homeomorphic to the closed
unit disk. -/
theorem exists_locallyFinite_maxCell_cover {U : Set ℂ} (hU : IsOpen U) :
    ∃ (ι : Type) (D : ι → Set ℂ),
      (∀ i, IsClosed (D i)) ∧ (∀ i, D i ⊆ U) ∧ (⋃ i, D i) = U ∧
      (∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅) ∧
      (∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ {i | (D i ∩ Metric.ball x r).Nonempty}.Finite) := by
  classical
  refine ⟨{q : ℕ × (ℤ × ℤ) // dyadicCell q.1 q.2 ⊆ U ∧
      (q.1 = 0 ∨ ¬ dyadicCell (q.1 - 1) (q.2.1 / 2, q.2.2 / 2) ⊆ U)},
    fun i => dyadicCell i.1.1 i.1.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_dyadicCell _ _
  · intro i
    exact i.2.1
  · ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact i.2.1 hi
    · intro hz
      obtain ⟨n, p, hzp, hsub, hmax⟩ := maxCell_mem_of_mem U hU hz
      exact mem_iUnion.mpr ⟨⟨(n, p), hsub, hmax⟩, hzp⟩
  · intro i j hij
    rw [eq_empty_iff_forall_notMem]
    rintro z hz
    obtain ⟨hij1, hij2⟩ := maxCell_interior_disjoint U i.1.1 j.1.1 i.1.2 j.1.2 i.2.1 i.2.2 j.2.1
      j.2.2 ⟨z, hz⟩
    exact hij (Subtype.ext (Prod.ext hij1 hij2))
  · intro x hx
    obtain ⟨r, hr, hfin⟩ := maximal_dyadicCells_locallyFinite U hU x hx
    refine ⟨r, hr, ?_⟩
    have himg : (Subtype.val '' {i : {q : ℕ × (ℤ × ℤ) // dyadicCell q.1 q.2 ⊆ U ∧
        (q.1 = 0 ∨ ¬ dyadicCell (q.1 - 1) (q.2.1 / 2, q.2.2 / 2) ⊆ U)} |
        (dyadicCell i.1.1 i.1.2 ∩ Metric.ball x r).Nonempty}) ⊆
        {q : ℕ × (ℤ × ℤ) | dyadicCell q.1 q.2 ⊆ U ∧
          (q.1 = 0 ∨ ¬ dyadicCell (q.1 - 1) (q.2.1 / 2, q.2.2 / 2) ⊆ U) ∧
          (dyadicCell q.1 q.2 ∩ Metric.ball x r).Nonempty} := by
      rintro q ⟨i, hi, rfl⟩
      exact ⟨i.2.1, i.2.2, hi⟩
    exact (hfin.subset himg).of_finite_image (fun a _ b _ hab => Subtype.val_injective hab)


end Commons.Topology.Surface
