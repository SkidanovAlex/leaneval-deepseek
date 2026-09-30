/-
# `chartLCcoords` agrees with the coordinate representative of `lcConn σ` near `x₀`

The candidate coordinate representative `Work.LeviCivita.chartLCcoords x₀ σ` (defined in
`Submission/Work/LeviCivita/Smooth.lean` as "raise the Koszul pairing with the inverse chart
metric") is eventually equal, near `x₀`, to the honest coordinate representative
`ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x x₀ x (lcConn σ x)`
of the Levi-Civita covariant derivative of a section `σ`.

## The argument

Write `e` for the tangent trivialisation at `x₀` and `fv x v = e.symmL ℝ x v = frameVector x₀ x v`
for the chart-frame vector with coordinates `v`.  Two facts are combined.

* **The chart metric is the metric of the frame.**  `chartGram x₀ x a b = ⟪fv x a, fv x b⟫`, and
  for `x` in the chart source `e.symmL ℝ x (e.continuousLinearMapAt ℝ x y) = y`.  Hence for `x`
  in the chart source the coordinate representative of `lcConn σ x` pairs as
  `chartGram x₀ x ((inCoordinates … ) u) w = ⟪lcConn σ x (fv x u), fv x w⟫`.
* **The Koszul pairing is the same pairing.**  `chartPairing x₀ σ x u w` is the double sum, in the
  basis `Module.finBasis ℝ E`, of the same inner products against the *globally smooth* fields
  `smoothFrameField x₀ (b i)`, which agree with the frame near `x₀`
  (`smoothFrameField_eventuallyEq`).  Evaluating the double sum with `Basis.sum_repr` collapses it,
  by bilinearity of `inner`, to `⟪lcConn σ x (fv x u), fv x w⟫`.

Consequently `chartGramCLM x₀ x ∘L (inCoordinates …) = chartPairing x₀ σ x` eventually.  Since the
chart metric is positive definite on the chart source, hence invertible
(`isInvertible_of_posDef`), applying `(chartGramCLM x₀ x).inverse` on the left and using
`ContinuousLinearMap.IsInvertible.inverse_comp_self` gives
`chartLCcoords x₀ σ x = (inCoordinates …)`, which is the claimed eventual equality.
-/
import Mathlib
import Submission.Work.LeviCivita.Smooth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Metric Filter
open Submission.ChartConnection
open Submission.Geodesic

set_option autoImplicit false

namespace Work.LeviCivita

noncomputable section

/-- **Expansion of an inner product against a linear image along a basis.**

For a finite basis `b` of `E`, a continuous linear map `F : E →L X` into a real inner product
space and a continuous linear map `V : X →L X`, the pairing `⟪V (F u), F w⟫` is the double sum of
the pairings of the basis images, weighted by the coordinates of `u` and `w`. -/
private lemma basis_inner_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {X : Type*} [SeminormedAddCommGroup X] [InnerProductSpace ℝ X]
    (b : Module.Basis ι ℝ E) (F : E →L[ℝ] X) (V : X →L[ℝ] X) (u w : E) :
    Inner.inner ℝ (V (F u)) (F w)
      = ∑ i, (b.coord i) u * ∑ j, (b.coord j) w * Inner.inner ℝ (V (F (b i))) (F (b j)) := by
  have hFu : F u = ∑ i, (b.coord i) u • F (b i) := by
    conv_lhs => rw [← b.sum_repr u]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Module.Basis.coord_apply]
  have hFw : F w = ∑ j, (b.coord j) w • F (b j) := by
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Module.Basis.coord_apply]
  have hVF : V (F u) = ∑ i, (b.coord i) u • V (F (b i)) := by
    rw [hFu, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  have step : ∀ i, ∑ j, (b.coord j) w * Inner.inner ℝ (V (F (b i))) (F (b j))
      = Inner.inner ℝ (V (F (b i))) (F w) := by
    intro i
    rw [hFw, inner_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_right]
  calc Inner.inner ℝ (V (F u)) (F w)
      = ∑ i, Inner.inner ℝ ((b.coord i) u • V (F (b i))) (F w) := by rw [hVF, sum_inner]
    _ = ∑ i, (b.coord i) u * Inner.inner ℝ (V (F (b i))) (F w) := by
          exact Finset.sum_congr rfl fun i _ => by
            rw [inner_smul_left, starRingEnd_apply, star_trivial]
    _ = ∑ i, (b.coord i) u * ∑ j, (b.coord j) w * Inner.inner ℝ (V (F (b i))) (F (b j)) := by
          exact Finset.sum_congr rfl fun i _ => by rw [step i]

/-- **The chart metric composed with the coordinate representative of `lcConn σ` is the Koszul
pairing**, at a point `x` of the chart at `x₀` where the globally smooth fields
`smoothFrameField x₀ (b i)` agree with the chart frame `frameVector x₀ · (b i)`. -/
private lemma chartGramCLM_comp_inCoordinates_eq_chartPairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    (x₀ : M) (σ : Π x : M, TangentSpace I x) (x : M)
    (hx : x ∈ (chartAt H x₀).source)
    (hsf : ∀ i, smoothFrameField (I := I) x₀ ((Module.finBasis ℝ E) i) x
              = frameVector (I := I) x₀ x ((Module.finBasis ℝ E) i)) :
    (chartGramCLM (I := I) x₀ x).comp
        (ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x x₀ x
          (lcConn (I := I) (M := M) σ x))
      = chartPairing (I := I) x₀ σ x := by
  ext u w
  rw [ContinuousLinearMap.comp_apply]
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  -- the coordinate representative of `lcConn σ x` in the frame
  have hAu : (ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x x₀ x
        (lcConn (I := I) (M := M) σ x)) u
      = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x
          (lcConn (I := I) (M := M) σ x (frameVector (I := I) x₀ x u)) := rfl
  rw [hAu, chartGramCLM_apply, chartGram_apply]
  -- the metric of the frame reads the vector back
  have hfv : frameVector (I := I) x₀ x
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x
        (lcConn (I := I) (M := M) σ x (frameVector (I := I) x₀ x u)))
      = lcConn (I := I) (M := M) σ x (frameVector (I := I) x₀ x u) :=
    Trivialization.symmL_continuousLinearMapAt _ hbase _
  rw [hfv, chartPairing_apply]
  -- the smooth fields agree with the frame at `x`
  simp only [hsf]
  -- the double sum collapses by bilinearity
  exact basis_inner_expansion (b := Module.finBasis ℝ E)
    (F := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x)
    (V := lcConn (I := I) (M := M) σ x) u w

set_option linter.unusedVariables false in
open scoped Manifold ContDiff Bundle Topology in
theorem chartLCcoords_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    (x₀ : M) {σ : Π x : M, TangentSpace I x} (hσ : ContMDiff I I.tangent ∞ (T% σ)) :
    Work.LeviCivita.chartLCcoords (I := I) x₀ σ =ᶠ[𝓝 x₀]
      (fun x : M ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        x₀ x x₀ x (Work.LeviCivita.lcConn (I := I) (M := M) σ x)) := by
  -- near `x₀` every chart-frame vector is represented by the corresponding smooth field
  have hsf_ev : ∀ᶠ x in 𝓝 x₀, ∀ i, smoothFrameField (I := I) x₀ ((Module.finBasis ℝ E) i) x
      = frameVector (I := I) x₀ x ((Module.finBasis ℝ E) i) := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [smoothFrameField_eventuallyEq (I := I) x₀ ((Module.finBasis ℝ E) i)] with x hx
    rw [hx]
    rfl
  -- and near `x₀` we stay in the chart, where the chart metric is invertible
  have hsrc_ev : ∀ᶠ x in 𝓝 x₀, x ∈ (chartAt H x₀).source :=
    (chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)
  filter_upwards [hsf_ev, hsrc_ev] with x hsf hsrc
  have hG_inv : (chartGramCLM (I := I) x₀ x).IsInvertible :=
    isInvertible_of_posDef _ (fun v hv => chartGram_posDef (I := I) x₀ x hsrc hv)
  have hcomp := chartGramCLM_comp_inCoordinates_eq_chartPairing (I := I) x₀ σ x hsrc hsf
  show (chartGramCLM (I := I) x₀ x).inverse.comp (chartPairing (I := I) x₀ σ x) = _
  rw [← hcomp, ← ContinuousLinearMap.comp_assoc, hG_inv.inverse_comp_self,
    ContinuousLinearMap.id_comp]

end

end Work.LeviCivita
