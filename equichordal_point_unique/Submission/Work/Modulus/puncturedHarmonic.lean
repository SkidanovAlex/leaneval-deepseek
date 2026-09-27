import Mathlib
import Submission.Work.Modulus.Defs

/-!
# `E` is harmonic on the punctured surface

If `E` is a Green function at `z₀` in the sense of `Work.UnitGreen.IsUnitGreenFunctionAt`, then `E` is
harmonic off `z₀` — this is part of the very definition (`HasGreenFunctionWeak`).  The content of
this module is the *transport* of that statement from `X` to the punctured surface
`puncturedOpens z₀` (the open subset `X ∖ {z₀}`), i.e. the observation that the `ChartedSpace ℂ`
structure of an open subset is given by the restrictions `(chartAt ℂ x).subtypeRestr` of the charts
of the ambient manifold, and that harmonicity is a local statement, so it is insensitive to this
change of charts.

The three chart lemmas about `TopologicalSpace.Opens` below are the whole of the bookkeeping:

* `opensChartAt_apply` — the chart of the subspace at `u` agrees with the ambient chart at `u`;
* `opensChartAt_mem_target` — consequently the value of the ambient chart at `u` lies in the target
  of the chart of the subspace at `u` (this is where `u.2`, i.e. `u ≠ z₀`, is used: the chart of
  `X ∖ {z₀}` has target contained in the set of points of the ambient chart target whose inverse
  image is punctured);
* `opensChartAt_symm_eqOn` — on that target, the inverse of the chart of the subspace is the
  restriction of the inverse of the ambient chart.
-/

open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The chart of an open subset `s` at a point `u` agrees, at `u`, with the ambient chart at `u`:
both are the restriction of the ambient preferred chart. -/
theorem opensChartAt_apply (s : TopologicalSpace.Opens X) (u : s) :
    (chartAt ℂ u) u = (chartAt ℂ (u : X)) (u : X) := by
  rw [TopologicalSpace.Opens.chartAt_eq (x := u), OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- The value of the ambient preferred chart at `u` belongs to the target of the chart of the open
subset `s` at `u`. -/
theorem opensChartAt_mem_target (s : TopologicalSpace.Opens X) (u : s) :
    (chartAt ℂ (u : X)) (u : X) ∈ (chartAt ℂ u).target := by
  rw [TopologicalSpace.Opens.chartAt_eq (x := u), OpenPartialHomeomorph.subtypeRestr_def,
    OpenPartialHomeomorph.trans_target]
  refine ⟨(chartAt ℂ (u : X)).map_source (mem_chart_source ℂ (u : X)), ?_⟩
  rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  show ((chartAt ℂ (u : X)).symm ((chartAt ℂ (u : X)) (u : X)) : X) ∈ (s : Set X)
  rw [(chartAt ℂ (u : X)).left_inv (mem_chart_source ℂ (u : X))]
  exact u.2

/-- On the target of the chart of the open subset `s` at `u`, the inverse of that chart is the
restriction of the inverse of the ambient chart at `u`. -/
theorem opensChartAt_symm_eqOn (s : TopologicalSpace.Opens X) (u : s) {z : ℂ}
    (hz : z ∈ (chartAt ℂ u).target) :
    (((chartAt ℂ u).symm z : s) : X) = (chartAt ℂ (u : X)).symm z := by
  have h := OpenPartialHomeomorph.subtypeRestr_symm_eqOn (chartAt ℂ (u : X)) (U := s) ⟨u⟩
  have hz' : z ∈ ((chartAt ℂ (u : X)).subtypeRestr ⟨u⟩).target := hz
  exact (h hz').symm

end Work.Modulus

namespace Work.Modulus

/-- **A Green function is harmonic on the punctured surface.**

`E` is harmonic off its pole `z₀` by definition of `Work.UnitGreen.IsUnitGreenFunctionAt`; reading this
statement on the open subset `puncturedOpens z₀ = X ∖ {z₀}` is a purely local matter: at a point
`u` of the punctured surface the chart of the subspace is the restriction of the ambient chart
(`opensChartAt_symm_eqOn`), so the two chart representatives of `E` agree near the relevant point. -/
theorem puncturedHarmonic
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) :
    Submission.HarmonicOnX (fun u : (puncturedOpens z₀) => E u.1) Set.univ := by
  intro u _
  change InnerProductSpace.HarmonicAt
    ((fun u : puncturedOpens z₀ => E u.1) ∘ (chartAt ℂ u).symm) ((chartAt ℂ u) u)
  have hxne : (u : X) ≠ z₀ := u.2
  -- harmonicity of `E` at `u` in the ambient surface `X`
  have hEat : InnerProductSpace.HarmonicAt (E ∘ (chartAt ℂ (u : X)).symm)
      ((chartAt ℂ (u : X)) (u : X)) :=
    hE.1.2.1 (u : X) ⟨mem_univ _, by simpa using hxne⟩
  -- the two chart representatives agree near `(chartAt ℂ u) u`
  have heq : ((fun u : puncturedOpens z₀ => E u.1) ∘ (chartAt ℂ u).symm)
      =ᶠ[𝓝 ((chartAt ℂ (u : X)) (u : X))] (E ∘ (chartAt ℂ (u : X)).symm) := by
    filter_upwards [(chartAt ℂ u).open_target.mem_nhds (opensChartAt_mem_target _ u)] with z hz
    simp only [Function.comp_apply]
    rw [opensChartAt_symm_eqOn _ u hz]
  rw [opensChartAt_apply (puncturedOpens z₀) u]
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr hEat

end Work.Modulus
