import Mathlib

/-!
# The chart of a homeomorphism-pushed `ChartedSpace`, and its derivative

If `e : M ≃ₜ M'` is a homeomorphism and `M'` is given the `ChartedSpace` structure pushed forward
from `M` along `e` (`Homeomorph.chartedSpace e`), then near any point the pushed-forward chart at `p`
is the original chart at `e.symm p`, composed with `e.symm`:

> `chartAt H p (f y) = chartAt H (e.symm p) (e.symm (f y))`  for `y` near `z`,

for any curve `f` through the source of the first chart.  `Work.Drive.chartedStructure_contMDiffWithinAt`
proves the corresponding statement for smoothness; this file proves the *pointwise* form, from which
the derivative statement `Work.Drive.fderiv_chartAt_homeomorph_chartedSpace` follows by eventual
equality.

This is the bridge that makes a computation in a transported chart (e.g. the transparent structure
`Work.Drive.cappingCharted` of the capping space, which is `halfLineProjectiveCharted` transported
along `Work.Drive.cappingSpaceHomeoProj`) a computation in the *model* `(0,∞) × ℝP³`.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Topology Filter

/-- **The pushed-forward preferred chart is the original chart composed with `e.symm`.** -/
theorem eventuallyEq_chartAt_homeomorph_chartedSpace
    {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {M' : Type*} [TopologicalSpace M'] (e : M ≃ₜ M')
    {Z : Type*} [TopologicalSpace Z] (f : Z → M') (z : Z) (p : M') (hf : ContinuousAt f z)
    (hz : f z ∈ (@chartAt H _ M' _ (Homeomorph.chartedSpace e) p).source) :
    (fun y => @chartAt H _ M' _ (Homeomorph.chartedSpace e) p (f y))
      =ᶠ[𝓝 z] (fun y => chartAt H (e.symm p) (e.symm (f y))) := by
  letI : ChartedSpace H M' := Homeomorph.chartedSpace e
  let g : M' → M := (Function.Surjective.hasRightInverse e.surjective).choose
  have hg : Function.RightInverse g ⇑e :=
    (Function.Surjective.hasRightInverse e.surjective).choose_spec
  have hgq : g p = e.symm p :=
    e.injective (by rw [hg p, e.apply_symm_apply])
  let L : OpenPartialHomeomorph M' M := e.isLocalHomeomorph.localInverseAt (g p)
  let C : OpenPartialHomeomorph M H := chartAt H (e.symm p)
  have hCeq : (chartAt H (g p) : OpenPartialHomeomorph M H) = C := by rw [hgq]
  have hchart : (chartAt H p : OpenPartialHomeomorph M' H) = L ≫ₕ C := by
    change (e.isLocalHomeomorph.localInverseAt (g p)) ≫ₕ (chartAt H (g p)) = _
    rw [hCeq]
  have hmemz : f z ∈ L.source := by
    rw [hchart] at hz
    exact hz.1
  filter_upwards [hf.preimage_mem_nhds (L.open_source.mem_nhds hmemz)] with y hy
  rw [hchart, OpenPartialHomeomorph.trans_apply]
  have hw : L (f y) = e.symm (f y) := by
    apply e.injective
    rw [IsLocalHomeomorph.apply_localInverseAt_of_mem (hf := e.isLocalHomeomorph) (x := g p) hy,
      e.apply_symm_apply]
  rw [hw]

/-- The special case of the previous lemma in which the chart is taken at the point of the curve. -/
theorem eventuallyEq_chartAt_homeomorph_chartedSpace_self
    {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {M' : Type*} [TopologicalSpace M'] (e : M ≃ₜ M')
    {Z : Type*} [TopologicalSpace Z] (f : Z → M') (z : Z) (hf : ContinuousAt f z) :
    (fun y => @chartAt H _ M' _ (Homeomorph.chartedSpace e) (f z) (f y))
      =ᶠ[𝓝 z] (fun y => chartAt H (e.symm (f z)) (e.symm (f y))) :=
  eventuallyEq_chartAt_homeomorph_chartedSpace e f z (f z) hf
    (@mem_chart_source H M' _ _ (Homeomorph.chartedSpace e) (f z))

/-- **The derivative of the pushed-forward preferred chart.** -/
theorem fderiv_chartAt_homeomorph_chartedSpace
    {H : Type*} [TopologicalSpace H] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {M' : Type*} [TopologicalSpace M'] (e : M ≃ₜ M')
    {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → M') (z : EuclideanSpace ℝ (Fin k)) (p : M')
    (hf : ContinuousAt f z)
    (hz : f z ∈ (@chartAt H _ M' _ (Homeomorph.chartedSpace e) p).source) :
    fderiv ℝ (fun y => @chartAt H _ M' _ (Homeomorph.chartedSpace e) p (f y)) z
      = fderiv ℝ (fun y => chartAt H (e.symm p) (e.symm (f y))) z :=
  (eventuallyEq_chartAt_homeomorph_chartedSpace e f z p hf hz).fderiv_eq

/-- The special case in which the chart is taken at the point of the curve. -/
theorem fderiv_chartAt_homeomorph_chartedSpace_self
    {H : Type*} [TopologicalSpace H] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {M' : Type*} [TopologicalSpace M'] (e : M ≃ₜ M')
    {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → M') (z : EuclideanSpace ℝ (Fin k))
    (hf : ContinuousAt f z) :
    fderiv ℝ (fun y => @chartAt H _ M' _ (Homeomorph.chartedSpace e) (f z) (f y)) z
      = fderiv ℝ (fun y => chartAt H (e.symm (f z)) (e.symm (f y))) z :=
  fderiv_chartAt_homeomorph_chartedSpace e f z (f z) hf
    (@mem_chart_source H M' _ _ (Homeomorph.chartedSpace e) (f z))

end Work.Drive
