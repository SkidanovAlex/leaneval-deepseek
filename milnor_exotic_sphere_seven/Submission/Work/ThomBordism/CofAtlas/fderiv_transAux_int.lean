import Submission.Work.ThomBordism.CofAtlas.Signs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chain rule for the transition `transAux` of the `Lvl` charts (interior centre)

`Work.ThomBordism.CofAtlas.fderiv_transAux_int`: for the coframed level-set data `D`, two points
`x y` of the level set with `x` an interior point of the ambient manifold `M`, and a point `q` of
the level set lying in the sources of both `Lvl` charts, the derivative of the model-level
transition

`transAux x y y₀ = β_y (domChange x y (chartHmap x y₀)) - β_y (chartZ y) + ε_y • e₀`

at `y₀ = lvlExt x q` is `β_y ∘ d(domChange x y) at (domExt x q) ∘ chartIota x`
`= β_y ∘ Tdom x y q ∘ J_x`.

The content is the chain rule for the decomposition of the transition into the affine map
`chartHmap x` (whose derivative is the constant `chartIota x`), the change of normal-form charts
`domChange x y` (whose derivative at `domExt x q` is `Tdom x y q`), and the linear projection
`chartBeta y`.  The only topological input is that `transAux` is differentiable at `lvlExt x q`,
i.e. that `domChange x y` is differentiable at `domExt x q`: this requires `domExt x q` to be an
*interior* point of the model space, which is the case whenever `q` lies in the source of the
chart at `x` and `x ∉ ∂M`.

Without the interiority hypothesis of the centre the statement is **false**: at a boundary point
of `M` the extended chart transition is the clamping map `z ↦ max (z 0) 0`, which is not
differentiable at the boundary.

The proof is assembled from

* `mem_interior_of_mem_chartSource_of_notMem_boundary` — a point of the source of the chart at an
  interior centre lies over an interior point of `M`;
* `range_mem_nhds_domExt` — `domExt x q` is an interior point of the model space;
* `hasFDerivAt_chartHmap`, `chartHmap_lvlExt` — the affine map `chartHmap x` and its value at
  `lvlExt x q`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

/-! ## The extended chart of the level set at a point of the chart source -/

/-- **The extended `Lvl` chart is the chart function.**  On the source of the chart at `x` the
extended chart of the level set at `x` is the chart function `chartFun x`. -/
theorem lvlExt_eq_chartFun (D : Cof k n M) (x : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x) :
    D.lvlExt x q = D.S.chartFun x q := by
  have h1 : D.lvlExt x q = (𝓡∂ 9) ((D.S.chartAt x) q) := rfl
  rw [h1, Lvl.Setup.chartAt_apply_of_mem D.S x hx]
  exact modelWithCornersEuclideanHalfSpace_apply 9

/-- **`chartHmap` at the extended chart point is the extended normal-form chart.** -/
theorem chartHmap_lvlExt (D : Cof k n M) (x : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x) :
    D.S.chartHmap x (D.lvlExt x q) = D.domExt x (q : M) := by
  rw [lvlExt_eq_chartFun D x hx]
  exact Lvl.Setup.chartHmap_chartFun D.S x hx

/-- **`chartHmap x` is affine**: its derivative is the constant `chartIota x`. -/
theorem hasFDerivAt_chartHmap (D : Cof k n M) (x : D.S.Pre) (t : E9) :
    HasFDerivAt (D.S.chartHmap x) (D.S.chartIota x) t := by
  have h1 : HasFDerivAt (fun s : E9 => (D.S.chartIota x) s
      + (D.S.chartZ x - (D.S.chartIota x) (D.S.chartEps x • Work.Surgery.e₀ 8)))
      (D.S.chartIota x) t :=
    ((D.S.chartIota x).hasFDerivAt).add_const _
  have hfun : (fun s : E9 => (D.S.chartIota x) s
      + (D.S.chartZ x - (D.S.chartIota x) (D.S.chartEps x • Work.Surgery.e₀ 8))) = D.S.chartHmap x := by
    funext s
    rw [Lvl.Setup.chartHmap_apply, map_sub]
    abel_nf
  rwa [hfun] at h1

/-! ## Interiority -/

/-- **A point of the source of the chart at an interior centre is interior.**  If the centre `x` of
a `Lvl` chart is not a boundary point of `M`, then every point `q` of the chart source lies over an
interior point of `M` (the chart is a ball in the normal-form coordinates of radius at most half the
height of the centre, so the height of `q` stays positive). -/
theorem mem_interior_of_mem_chartSource_of_notMem_boundary (D : Cof k n M) (x : D.S.Pre)
    {q : D.S.Pre} (hx : q ∈ D.S.chartSource x)
    (hxi : (x : M) ∉ (𝓡∂ (NN k)).boundary M) :
    (q : M) ∈ (𝓡∂ (NN k)).interior M := by
  -- the point of the chart source has positive normal-form height
  have hball : D.S.chartHmap x (D.lvlExt x q)
      ∈ Metric.ball (D.S.chartZ x) (D.S.chartRho x) := by
    rw [chartHmap_lvlExt D x hx]
    exact hx.2.1.2
  have hcoord : 0 < (D.domExt x (q : M)).ofLp 0 := by
    rw [← chartHmap_lvlExt D x hx]
    exact Lvl.Setup.chartHmap_coord_pos D.S x hxi hball
  -- hence `q` is not a boundary point of `M`
  have hnotbnd : (q : M) ∉ (𝓡∂ (NN k)).boundary M := by
    intro hb
    have h0 : (D.domExt x (q : M)).ofLp 0 = 0 :=
      (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
        (Lvl.Setup.domChartAt_mem_maximalAtlas D.S x) hx.1).mp hb
    rw [h0] at hcoord
    exact absurd hcoord (lt_irrefl 0)
  -- and the complement of the boundary is the interior
  have hnotbnd' : (q : M) ∈ ((𝓡∂ (NN k)).boundary M)ᶜ := hnotbnd
  rw [← ModelWithCorners.compl_interior] at hnotbnd'
  simpa using hnotbnd'

/-- **The normal-form image of a point of the chart source over an interior point is an interior
point of the model space.** -/
theorem range_mem_nhds_domExt (D : Cof k n M) (x : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x) (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    Set.range (𝓡∂ (NN k)) ∈ 𝓝 (D.domExt x (q : M)) := by
  have hn : (((⊤ : ENat) : WithTop ENat) : WithTop ℕ∞) ≠ 0 := by simp
  have hut : D.domExt x (q : M)
      ∈ interior ((D.S.domChartAt x).extend (𝓡∂ (NN k))).target :=
    (Work.ThomBordism.Transversality.Preimage.isInteriorPoint_iff_of_mem_maximalAtlas hn
      (Lvl.Setup.domChartAt_mem_maximalAtlas D.S x) hx.1).mp hint
  refine Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior ?_) interior_subset
  exact OpenPartialHomeomorph.interior_extend_target_subset_interior_range
    (D.S.domChartAt x) hut

/-! ## The chain rule -/

/-- The derivative of the change of normal-form coordinates `domChange x y` at `domExt x q`, when
this point is interior in the model space. -/
theorem hasFDerivAt_domChange (D : Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x) (hy : q ∈ D.S.chartSource y)
    (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    HasFDerivAt (D.domChange x y) (D.Tdom x y (q : M)) (D.domExt x (q : M)) := by
  have hmemI : Set.range (𝓡∂ (NN k)) ∈ 𝓝 (D.domExt x (q : M)) :=
    range_mem_nhds_domExt D x hx hint
  have hnhds : (D.domChange x y).source ∈ 𝓝 (D.domExt x (q : M)) := by
    have h1 := ModelWithCorners.extendCoordChange_source_mem_nhdsWithin'
      (I := 𝓡∂ (NN k)) hx.1 hy.1
    have h2 : 𝓝[(Set.range (𝓡∂ (NN k)))] (D.domExt x (q : M)) = 𝓝 (D.domExt x (q : M)) :=
      nhdsWithin_eq_nhds.mpr hmemI
    rw [← h2]
    exact h1
  have hcont : ContDiffOn ℝ ∞ (D.domChange x y) (D.domChange x y).source :=
    ModelWithCorners.contDiffOn_extendCoordChange
      (Lvl.Setup.domChartAt_mem_maximalAtlas D.S x)
      (Lvl.Setup.domChartAt_mem_maximalAtlas D.S y)
  have hdiff : DifferentiableAt ℝ (D.domChange x y) (D.domExt x (q : M)) :=
    (hcont.contDiffAt hnhds).differentiableAt (by simp)
  exact hdiff.hasFDerivAt

/-- **Chain rule for the transition of the `Lvl` charts** (interior form). -/
theorem fderiv_transAux_of_interior (D : Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x) (hy : q ∈ D.S.chartSource y)
    (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)
      = (D.S.chartBeta y).comp ((D.Tdom x y (q : M)).comp (D.S.chartIota x)) := by
  -- the derivative of the normal-form chart change
  have hTD : HasFDerivAt (D.domChange x y) (D.Tdom x y (q : M)) (D.domExt x (q : M)) :=
    hasFDerivAt_domChange D x y hx hy hint
  -- the affine map `chartHmap x`
  have hch : HasFDerivAt (D.S.chartHmap x) (D.S.chartIota x) (D.lvlExt x q) :=
    hasFDerivAt_chartHmap D x (D.lvlExt x q)
  have hlvl : D.S.chartHmap x (D.lvlExt x q) = D.domExt x (q : M) :=
    chartHmap_lvlExt D x hx
  -- the chain rule
  have hTD' : HasFDerivAt (D.domChange x y) (D.Tdom x y (q : M))
      (D.S.chartHmap x (D.lvlExt x q)) := by
    rw [hlvl]
    exact hTD
  have hcomp : HasFDerivAt (fun z : E9 => D.domChange x y (D.S.chartHmap x z))
      ((D.Tdom x y (q : M)).comp (D.S.chartIota x)) (D.lvlExt x q) :=
    hTD'.comp (D.lvlExt x q) hch
  have hG : HasFDerivAt
      (fun z : E9 => (D.S.chartBeta y) (D.domChange x y (D.S.chartHmap x z)))
      ((D.S.chartBeta y).comp ((D.Tdom x y (q : M)).comp (D.S.chartIota x))) (D.lvlExt x q) :=
    (D.S.chartBeta y).hasFDerivAt.comp (D.lvlExt x q) hcomp
  have htrans : (fun z : E9 => (D.S.chartBeta y) (D.domChange x y (D.S.chartHmap x z))
      - (D.S.chartBeta y) (D.S.chartZ y) + D.S.chartEps y • Work.Surgery.e₀ 8)
      = D.S.transAux x y := rfl
  rw [← htrans, ((hG.sub_const (D.S.chartBeta y (D.S.chartZ y))).add_const
    (D.S.chartEps y • Work.Surgery.e₀ 8)).fderiv]

/-! ## The target -/

theorem fderiv_transAux_int
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x) (hy : q ∈ D.S.chartSource y)
    (hxib : (x : M) ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M) :
    fderiv ℝ (D.S.transAux x y) (D.lvlExt x q)
      = (D.S.chartBeta y).comp ((D.Tdom x y (q : M)).comp (D.S.chartIota x)) :=
  fderiv_transAux_of_interior D x y hx hy
    (mem_interior_of_mem_chartSource_of_notMem_boundary D x hx hxib)

end

end Work.ThomBordism.CofAtlas
