import Mathlib
import Submission.Work.ThomBordism.Transversality.Basic
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.mfderiv_surjective_of_submersionAt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A finite chart cover of `closure {0 < χ}` with interior targets

First step of the manifold transport in `volume_badSet_eq_zero` (item 3): the witnesses of the bad
set lie in `{x | 0 < χ x}`, whose closure is compact, so finitely many preferred charts
`chartAt H y` cover them.  For each of those charts, and each *interior* point `x` of its source,
the extended chart value `(chartAt H y).extend I x` lies in the interior of the chart's target —
which is the bookkeeping that makes the chart expression a map on an open subset of the model space
(and, after a linear equivalence, of a Euclidean space).

Both facts are assembled here from
* `IsCompact.elim_finite_subcover` (compactness),
* `IsManifold.chart_mem_maximalAtlas` (atlas membership),
* `isInteriorPoint_iff_of_mem_maximalAtlas` (the interior-point property for arbitrary charts of the
  maximal atlas, proved in `mfderiv_surjective_of_submersionAt.lean`).
-/

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.TransversalApproximation

noncomputable section

/-- **A finite chart cover of the region of positive `χ`, with interior targets.**

There is a finite set `t` of points of `M` such that

* every `x` with `0 < χ x` lies in the source of one of the charts `chartAt H y`, `y ∈ t`;
* for every `y ∈ t` and every *interior* point `x` of `(chartAt H y).source`, the chart value
  `(chartAt H y).extend I x` lies in `interior ((chartAt H y).extend I).target`.

Each `chartAt H y` lies in the maximal atlas, so the two facts combine with
`isInteriorPoint_iff_of_mem_maximalAtlas`. -/
theorem exists_finite_chart_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M] [T2Space M]
    {χ : M → ℝ} (hχ : Continuous χ) :
    ∃ t : Finset M,
      (∀ x : M, 0 < χ x → ∃ y ∈ t, x ∈ (chartAt H y).source) ∧
      (∀ y ∈ t, ∀ x ∈ (chartAt H y).source, I.IsInteriorPoint x →
        (chartAt H y).extend I x ∈ interior ((chartAt H y).extend I).target) := by
  classical
  have hK : IsCompact (closure {x : M | 0 < χ x}) := isClosed_closure.isCompact
  have hcover : closure {x : M | 0 < χ x} ⊆ ⋃ y : M, (chartAt H y).source :=
    fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source H x⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : M => (chartAt H y).source)
    (fun y => (chartAt H y).open_source) hcover
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyt, hyx⟩ := mem_iUnion₂.mp (ht (subset_closure hx))
    exact ⟨y, hyt, hyx⟩
  · intro y _ x hxsrc hint
    exact (isInteriorPoint_iff_of_mem_maximalAtlas (I := I)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
      (IsManifold.chart_mem_maximalAtlas y) hxsrc).mp hint

end

end Work.ThomBordism.Transversality.TransversalApproximation
