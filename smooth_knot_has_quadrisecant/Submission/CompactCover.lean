import Mathlib
import ChallengeDeps
import Submission.ZeroSetPath

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# Layer A (xviii) — compact-interval covering of a path by chart regions,
and the chart-chain construction

`ZeroSetPath.lean` (Layer A (xvii)) set up the compact-interval
path-following statement `ChartChainLiftOnInterval` and proved its
single-chart base case and the junction one-step agreement.  This module
provides the topological input that statement needs: a **chart cover** of a
compact interval path and the **ordered chart chain** it induces.

1. **`chartAtPoint`** — a bundled chart of the zero set at the point
   `z : ZeroSetPoint r` (choice from `zeroSet1Chart_at_general_position`);
   `chartAtPoint_V_open`, `chartAtPoint_self`.
2. **`chartTimeSet`** — for each time `t` the (open) set of times `u` at
   which the path point `σ u` lies in the chart region of `σ t`
   (`isOpen_chartTimeSet`, `mem_chartTimeSet_self`); these sets cover the
   compact interval.
3. **`finite_chart_cover`** — the compact interval is covered by finitely
   many such chart-time regions (`IsCompact.elim_finite_subcover` on the
   compact interval subtype).
4. **chain construction** — `sortedCoverCharts` (the chart-sigma list of
   the cover, sorted by time), `mem_sortedCoverCharts`,
   `finite_chart_cover_sorted` (every path point lies in some chart of the
   sorted list), and `chainFromList` (builds the `ChartChain` from an
   ordered list of charts).  This is the raw material the Lebesgue-style
   refinement will sort into the adapted chain that the induction of
   `ChartChainLiftOnInterval` consumes.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

namespace LeanEval.KnotTheory.Quadrisecant

/-- A compact interval of real parameters is compact as a topological
space. -/
noncomputable instance compactIntervalCompactSpace (a b : ℝ) :
    CompactSpace (CompactInterval a b) := by
  exact (isCompact_iff_compactSpace).mp (isCompact_Icc (a := a) (b := b))

/-- A bundled chart of the trisecant zero set at the zero-set point `z`
(from the atlas/cover theorem under the torus general-position
hypothesis). -/
noncomputable def chartAtPoint {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (z : ZeroSetPoint r) :
    ZeroSet1Chart r (z : KnotParamTriple) :=
  Classical.choice (zeroSet1Chart_at_general_position h hgp (z : KnotParamTriple) z.2)

/-- The neighbourhood of the chart at `z` is open. -/
lemma chartAtPoint_V_open {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (z : ZeroSetPoint r) :
    IsOpen (chartAtPoint h hgp z).V :=
  (chartAtPoint h hgp z).V_open

/-- The point `z` lies in the neighbourhood of its own chart. -/
lemma chartAtPoint_self {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (z : ZeroSetPoint r) :
    (z : KnotParamTriple) ∈ (chartAtPoint h hgp z).V :=
  (chartAtPoint h hgp z).p_mem

/-- For a time `t`, the set of times `u` whose path point `σ u` lies in
the chart region of the point `σ t`. -/
def chartTimeSet {r : ℝ → Space} {a b : ℝ} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (σ : CompactInterval a b → ZeroSetPoint r)
    (t : CompactInterval a b) : Set (CompactInterval a b) :=
  {u : CompactInterval a b | (σ u : KnotParamTriple) ∈ (chartAtPoint h hgp (σ t)).V}

/-- `chartTimeSet` is open (the path is continuous and the chart region
is open). -/
lemma isOpen_chartTimeSet {r : ℝ → Space} {a b : ℝ} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (σ : CompactInterval a b → ZeroSetPoint r)
    (hσ : Continuous σ) (t : CompactInterval a b) :
    IsOpen (chartTimeSet h hgp σ t) := by
  unfold chartTimeSet
  have hmap : Continuous (fun u : CompactInterval a b => (σ u : KnotParamTriple)) :=
    continuous_subtype_val.comp hσ
  exact IsOpen.preimage hmap (chartAtPoint_V_open h hgp (σ t))

/-- Each time lies in its own chart-time set. -/
lemma mem_chartTimeSet_self {r : ℝ → Space} {a b : ℝ} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (σ : CompactInterval a b → ZeroSetPoint r)
    (t : CompactInterval a b) : t ∈ chartTimeSet h hgp σ t := by
  unfold chartTimeSet
  exact chartAtPoint_self h hgp (σ t)

/-- **Finite chart cover of the compact interval.**  A continuous path in
the zero set over the compact interval `[a,b]` has a finite set of times
whose chart regions cover the whole path. -/
theorem finite_chart_cover {r : ℝ → Space} {a b : ℝ} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (σ : CompactInterval a b → ZeroSetPoint r)
    (hσ : Continuous σ) :
    ∃ I : Finset (CompactInterval a b),
      ∀ u : CompactInterval a b,
        ∃ t : CompactInterval a b, t ∈ I ∧ (σ u : KnotParamTriple) ∈ (chartAtPoint h hgp (σ t)).V := by
  let U : CompactInterval a b → Set (CompactInterval a b) :=
    fun t => chartTimeSet h hgp σ t
  have hcov : (Set.univ : Set (CompactInterval a b)) ⊆ ⋃ t : CompactInterval a b, U t := by
    intro u _
    exact Set.mem_iUnion.mpr ⟨u, mem_chartTimeSet_self h hgp σ u⟩
  rcases (isCompact_univ.elim_finite_subcover U (fun t => isOpen_chartTimeSet h hgp σ hσ t) hcov) with
    ⟨I, hI⟩
  refine ⟨I, ?_⟩
  intro u
  have hu := hI (Set.mem_univ u)
  have hu1 : ∃ t : CompactInterval a b, t ∈ (I : Set (CompactInterval a b)) ∧ u ∈ U t := by
    simpa using hu
  rcases hu1 with ⟨t, htI, hut⟩
  exact ⟨t, by simpa using htI, by simpa [U, chartTimeSet] using hut⟩

/-- The **sorted chart list** of a finite set of cover times: the charts at
the path points `σ t`, ordered by the times. -/
noncomputable def sortedCoverCharts {r : ℝ → Space} {a b : ℝ} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (σ : CompactInterval a b → ZeroSetPoint r)
    (I : Finset (CompactInterval a b)) :
    List (Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) :=
  by
    classical
    exact (I.sort (· ≤ ·)).map (fun t => ⟨(σ t : KnotParamTriple), chartAtPoint h hgp (σ t)⟩)

/-- A cover time's chart appears in the sorted chart list. -/
lemma mem_sortedCoverCharts {r : ℝ → Space} {a b : ℝ} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (σ : CompactInterval a b → ZeroSetPoint r)
    (I : Finset (CompactInterval a b)) (t : CompactInterval a b) (ht : t ∈ I) :
    (⟨(σ t : KnotParamTriple), chartAtPoint h hgp (σ t)⟩ :
        Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) ∈
      sortedCoverCharts h hgp σ I := by
  unfold sortedCoverCharts
  classical
  apply List.mem_map.mpr
  refine ⟨t, ?_, rfl⟩
  exact (Finset.mem_sort (· ≤ ·)).mpr ht

/-- The sorted chart list of a finite cover still covers the whole path:
every path point lies in the region of some chart of the sorted list. -/
theorem finite_chart_cover_sorted {r : ℝ → Space} {a b : ℝ} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (σ : CompactInterval a b → ZeroSetPoint r)
    (_hσ : Continuous σ) (I : Finset (CompactInterval a b))
    (hI : ∀ u : CompactInterval a b, ∃ t : CompactInterval a b, t ∈ I ∧
      (σ u : KnotParamTriple) ∈ (chartAtPoint h hgp (σ t)).V) :
    ∀ u : CompactInterval a b,
      ∃ g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p),
        g ∈ sortedCoverCharts h hgp σ I ∧ (σ u : KnotParamTriple) ∈ g.2.V := by
  intro u
  rcases hI u with ⟨t, htI, hut⟩
  refine ⟨⟨(σ t : KnotParamTriple), chartAtPoint h hgp (σ t)⟩, ?_, hut⟩
  exact mem_sortedCoverCharts h hgp σ I t htI

/-- Build the **chain** of a chart `c₀` followed by an ordered list of
further charts (given as sigma pairs of point and chart). -/
noncomputable def chainFromList {r : ℝ → Space} {p₀ : KnotParamTriple}
    (c₀ : ZeroSet1Chart r p₀) :
    List (Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)) → ChartChain c₀
  | [] => ChartChain.nil c₀
  | ⟨_, c⟩ :: rest => ChartChain.cons c₀ c (chainFromList c rest)

end LeanEval.KnotTheory.Quadrisecant
