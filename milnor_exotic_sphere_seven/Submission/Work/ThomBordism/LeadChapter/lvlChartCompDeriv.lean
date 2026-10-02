import Mathlib
import Submission.Work.ThomBordism.CofAtlas.fderiv_transAux_int
import Submission.Work.ThomBordism.CofAtlas.Tdom_comp_Delta

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The derivative of the `Lvl` chart pulled back along an ambient chart

`Work.ThomBordism.LeadChapter.lvlChartCompDeriv` is step 2 of the proof sketch of
`Work.ThomBordism.chapter_K1det`: for a coframed level set `D : CofAtlas.Cof k n M`, an interior
point `x` of the level set, and *any* chart `κ` of the level set at `x`, the derivative at `κ x` of

`u ↦ extChartAt (𝓡∂ 9) x (κ.symm u)`

(the `Lvl` chart at `x`, pulled back along `κ`) is `β_x ∘ Δ_x ∘ A`, where

* `A` is the derivative at `κ x` of the corresponding *ambient* composite
  `u ↦ extChartAt (𝓡∂ (NN k)) (x : M) ((κ.symm u : D.S.Pre) : M)` (hypothesis `hA`);
* `Δ_x = Cof.Delta x (x : M)` is the derivative at `ambExt x x` of the change of coordinates from
  the ambient chart at `x` to the normal-form chart at `x` (`Cof.ambDomChange x`);
* `β_x = Cof.S.chartBeta x` is the projection onto the level-set model space `ℝ⁹`.

The proof is a chain rule.  Near `κ x` the point `κ.symm u` lies in the open source
`D.S.chartSource x` of the `Lvl` chart at `x` and over the source of the ambient chart at `x`, so
there the chart equals the explicit formula `chartFun` (`CofAtlas.lvlExt_eq_chartFun`), which in turn
is `β_x` applied to the normal-form coordinates minus `chartZ x` plus `chartEps x • e₀`; the
normal-form coordinates are the ambient ones (in the ambient chart at `x`) transported by
`ambDomChange x` (`CofAtlas.tcD_apply_extend`).  Differentiating that composite and transferring
along the eventual equality gives the claim.
-/

namespace Work.ThomBordism.LeadChapter

open scoped Manifold ContDiff Topology in
theorem lvlChartCompDeriv (k n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (CofAtlas.NN k)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) ((⊤ : ENat) : WithTop ENat) M]
    (D : CofAtlas.Cof k n M) (x : D.S.Pre)
    (κ : OpenPartialHomeomorph D.S.Pre CofAtlas.E9) (hκ : x ∈ κ.source)
    (A : CofAtlas.E9 →L[ℝ] CofAtlas.ModN k)
    (hA : HasFDerivAt (fun u : CofAtlas.E9 =>
        extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M)
          ((κ.symm u : D.S.Pre) : M)) A (κ x))
    (hint : (x : M) ∈ (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)).interior M) :
    (by
      letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
        Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
      letI : IsManifold (modelWithCornersEuclideanHalfSpace 9)
          ((⊤ : ENat) : WithTop ENat) D.S.Pre :=
        Work.PTGeometric.Lvl.Setup.instIsManifold D.S
      letI : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 D.S.Pre :=
        IsManifold.of_le (n := ((⊤ : ENat) : WithTop ENat)) (by simp)
      exact HasFDerivAt (fun u : CofAtlas.E9 =>
          extChartAt (modelWithCornersEuclideanHalfSpace 9) x (κ.symm u))
        ((D.S.chartBeta x).comp ((D.Delta x (x : M)).comp A)) (κ x)) := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace D.S
  letI : IsManifold (modelWithCornersEuclideanHalfSpace 9)
      ((⊤ : ENat) : WithTop ENat) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instIsManifold D.S
  letI : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 D.S.Pre :=
    IsManifold.of_le (n := ((⊤ : ENat) : WithTop ENat)) (by simp)
  have hκx : (κ.symm (κ x) : D.S.Pre) = x := κ.left_inv hκ
  -- ambient differentiability of the change of normal-form coordinates at the centre
  have hn : (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) ≠ 0 := by simp
  have hambx : D.ambChart x ∈ IsManifold.maximalAtlas (𝓡∂ (CofAtlas.NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    IsManifold.chart_mem_maximalAtlas (x : M)
  have hdomx : D.domChart x ∈ IsManifold.maximalAtlas (𝓡∂ (CofAtlas.NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    Work.PTGeometric.Lvl.Setup.domChartAt_mem_maximalAtlas D.S x
  have hxsrc : (x : M) ∈ (D.domChart x).source :=
    Work.PTGeometric.Lvl.Setup.mem_domChartAt_source D.S x
  have haxsrc : (x : M) ∈ (D.ambChart x).source :=
    mem_chart_source (EuclideanHalfSpace (CofAtlas.NN k)) (x : M)
  have hintAmb : D.ambExt x (x : M) ∈ interior (Set.range (𝓡∂ (CofAtlas.NN k))) :=
    Work.ThomBordism.CofAtlas.tcD_mem_interior_range (𝓡∂ (CofAtlas.NN k)) hn hambx haxsrc hint
  have hD : HasFDerivAt (D.ambDomChange x) (D.Delta x (x : M)) (D.ambExt x (x : M)) :=
    (Work.ThomBordism.CofAtlas.tcD_differentiableAt (𝓡∂ (CofAtlas.NN k)) hn hambx hdomx
      haxsrc hxsrc hintAmb).hasFDerivAt
  have hcoe : (((κ.symm (κ x) : D.S.Pre)) : M) = (x : M) := by rw [hκx]
  have hD' : HasFDerivAt (D.ambDomChange x) (D.Delta x (x : M))
      (D.ambExt x (((κ.symm (κ x) : D.S.Pre)) : M)) := by
    rw [hcoe]
    exact hD
  -- the chain rule for the ambient composite against the local chart
  have hcomp : HasFDerivAt
      ((D.ambDomChange x) ∘ fun u : CofAtlas.E9 => D.ambExt x (((κ.symm u : D.S.Pre)) : M))
      ((D.Delta x (x : M)).comp A) (κ x) := hD'.comp (κ x) hA
  have hg : HasFDerivAt
      (fun w : CofAtlas.ModN k =>
        D.S.chartBeta x w - D.S.chartBeta x (D.S.chartZ x) + D.S.chartEps x • Work.Surgery.e₀ 8)
      (D.S.chartBeta x) (D.ambDomChange x (D.ambExt x (x : M))) :=
    (((D.S.chartBeta x).hasFDerivAt).sub_const _).add_const _
  have hg' : HasFDerivAt
      (fun w : CofAtlas.ModN k =>
        D.S.chartBeta x w - D.S.chartBeta x (D.S.chartZ x) + D.S.chartEps x • Work.Surgery.e₀ 8)
      (D.S.chartBeta x) (D.ambDomChange x (D.ambExt x (((κ.symm (κ x) : D.S.Pre)) : M))) := by
    rw [hcoe]
    exact hg
  have hG : HasFDerivAt
      ((fun w : CofAtlas.ModN k =>
        D.S.chartBeta x w - D.S.chartBeta x (D.S.chartZ x) + D.S.chartEps x • Work.Surgery.e₀ 8) ∘
          ((D.ambDomChange x) ∘ fun u : CofAtlas.E9 => D.ambExt x (((κ.symm u : D.S.Pre)) : M)))
      ((D.S.chartBeta x).comp ((D.Delta x (x : M)).comp A)) (κ x) := hg'.comp (κ x) hcomp
  -- eventually the κ-pullback lies in the chart source and in the ambient chart source
  have hcont : ContinuousAt (fun u : CofAtlas.E9 => (κ.symm u : D.S.Pre)) (κ x) :=
    κ.continuousAt_symm (κ.map_source hκ)
  have hmem1 : (fun u : CofAtlas.E9 => (κ.symm u : D.S.Pre)) ⁻¹' D.S.chartSource x ∈ 𝓝 (κ x) := by
    have h0 : (κ.symm (κ x) : D.S.Pre) ∈ D.S.chartSource x := by
      rw [hκx]
      exact D.mem_chartSource_self x
    exact hcont.preimage_mem_nhds
      ((Work.PTGeometric.Lvl.Setup.chartSource_open D.S x).mem_nhds h0)
  have hmem2 : (fun u : CofAtlas.E9 => (((κ.symm u : D.S.Pre)) : M)) ⁻¹' (D.ambChart x).source
      ∈ 𝓝 (κ x) := by
    have h0 : (((κ.symm (κ x) : D.S.Pre)) : M) ∈ (D.ambChart x).source := by
      rw [hcoe]
      exact mem_chart_source (EuclideanHalfSpace (CofAtlas.NN k)) (x : M)
    exact (continuous_subtype_val.continuousAt.comp hcont).preimage_mem_nhds
      ((D.ambChart x).open_source.mem_nhds h0)
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [hmem1, hmem2] with u hz hza
  have hL : extChartAt (modelWithCornersEuclideanHalfSpace 9) x (κ.symm u)
      = D.S.chartFun x (κ.symm u) := by
    show (D.lvlExt x) (κ.symm u) = D.S.chartFun x (κ.symm u)
    exact Work.ThomBordism.CofAtlas.lvlExt_eq_chartFun D x hz
  show extChartAt (modelWithCornersEuclideanHalfSpace 9) x (κ.symm u)
      = D.S.chartBeta x (D.ambDomChange x (D.ambExt x (((κ.symm u : D.S.Pre)) : M)))
        - D.S.chartBeta x (D.S.chartZ x) + D.S.chartEps x • Work.Surgery.e₀ 8
  rw [hL]
  show D.S.chartFun x (κ.symm u)
      = D.S.chartBeta x (D.ambDomChange x (D.ambExt x (((κ.symm u : D.S.Pre)) : M)))
        - D.S.chartBeta x (D.S.chartZ x) + D.S.chartEps x • Work.Surgery.e₀ 8
  rw [show D.S.chartFun x (κ.symm u)
      = D.S.chartBeta x (D.domExt x (((κ.symm u : D.S.Pre)) : M) - D.S.chartZ x)
        + D.S.chartEps x • Work.Surgery.e₀ 8 from rfl]
  rw [Work.ThomBordism.CofAtlas.tcD_apply_extend (𝓡∂ (CofAtlas.NN k)) (D.ambChart x)
    (D.domChart x) hza, ← map_sub]

end Work.ThomBordism.LeadChapter
