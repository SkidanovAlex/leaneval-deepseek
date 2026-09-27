import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.isCritical_iff_chartRep

/-!
# The Hessian at a critical point, read in two charts

`Work.Drive.Morse.NondegCrit f x` is the assertion that the Hessian of `f` at the critical point
`x`, written in the chart `extChartAt (𝓡 2) x`, is injective.  The present file proves that this
notion does not depend on the chart: for any chart `chartAt p` whose source contains `x`, the
Hessian of the chart representative `y ↦ f ((chartAt p).symm y)` at `(chartAt p) x` is injective
if and only if the Hessian in the chart at `x` is.

The mathematical content is the classical chain rule computation.  Write `φ = chartAt p`,
`ψ = chartAt x`, `u = φ x`, `t = ψ x`, `τ = ψ ∘ φ.symm` (the transition map) and
`g_c = f ∘ c.symm` for a chart `c`.  Near `u` we have `g_φ = g_ψ ∘ τ`, whence
`fderiv (fderiv g_φ) u = fderiv (fderiv (g_ψ ∘ τ)) u`.  Differentiating the identity
`fderiv (g_ψ ∘ τ) = fderiv g_ψ (τ ·) ∘ fderiv τ` with the product rule gives

`H_φ = (compL (D g_ψ (ψ x))) ∘ D²τ + (D τ)ᵀ ∘ (H_ψ ∘ Dτ)`

and the first summand vanishes exactly because `x` is a critical point, i.e. `D g_ψ (ψ x) = 0`.
Hence `H_φ v = (H_ψ (T v)) ∘ T` with `T = fderiv τ u`, and `T` is a linear isomorphism (the
transition map is a local diffeomorphism).  Injectivity transfers across this identity.

The development is self-contained: the only outside input is that the `extChartAt` of the
self model `𝓡 2` is the corresponding `chartAt`, the smoothness of the chart transition map
(obtained from the smoothness of the identity map), and the smoothness of a chart
representative of `f`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

section SelfModelCharts

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- For the self model `𝓡 2` the extended chart at `x` is the chart at `x`. -/
@[simp] lemma extChartAt_self_coe_chart (x : M) :
    ⇑(extChartAt (𝓡 2) x) = ⇑(chartAt (EuclideanSpace ℝ (Fin 2)) x) := by
  funext y; simp [extChartAt, OpenPartialHomeomorph.extend]

/-- For the self model `𝓡 2` the inverse of the extended chart at `x` is the inverse of the
chart at `x`. -/
@[simp] lemma extChartAt_self_symm_coe_chart (x : M) :
    ⇑(extChartAt (𝓡 2) x).symm = ⇑(chartAt (EuclideanSpace ℝ (Fin 2)) x).symm := by
  funext y; simp [extChartAt, OpenPartialHomeomorph.extend]

/-- For the self model `𝓡 2` the target of the extended chart at `x` is the target of the
chart at `x`. -/
@[simp] lemma extChartAt_self_target_chart (x : M) :
    (extChartAt (𝓡 2) x).target = (chartAt (EuclideanSpace ℝ (Fin 2)) x).target := by
  rw [extChartAt_target]; simp

/-- For the self model `𝓡 2` the source of the extended chart at `x` is the source of the
chart at `x`. -/
@[simp] lemma extChartAt_self_source_chart (x : M) :
    (extChartAt (𝓡 2) x).source = (chartAt (EuclideanSpace ℝ (Fin 2)) x).source :=
  extChartAt_source (𝓡 2) x

end SelfModelCharts

section Definitions

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- The chart representative of `f` in the chart at `p`. -/
noncomputable def chartRep (f : M → ℝ) (p : M) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun y => f ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y)

/-- The transition map from the chart at `p` to the chart at `x`, read as a self-map of `ℝ²`. -/
noncomputable def chartTrans (p x : M) :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  fun y => (chartAt (EuclideanSpace ℝ (Fin 2)) x) ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y)

/-- The derivative of the chart representative of `f` at the chart point: the chart expression of
the differential of `f` at `x`. -/
noncomputable def chartDf (f : M → ℝ) (x : M) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  fderiv ℝ (chartRep f x) ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x)

/-- The derivative of the transition map at the chart point. -/
noncomputable def chartDeriv (p x : M) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  fderiv ℝ (chartTrans p x) ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x)

/-- The Hessian of `f` at `x`, read in the chart at `x`. -/
noncomputable def chartHess (f : M → ℝ) (x : M) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
  fderiv ℝ (fderiv ℝ (chartRep f x)) ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x)

end Definitions

section Smoothness

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- The chart representative of a smooth function is smooth on the chart target. -/
lemma contDiffOn_chartRep_center (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ContDiffOn ℝ ∞ (chartRep f x) (chartAt (EuclideanSpace ℝ (Fin 2)) x).target := by
  have hid : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ f Set.univ := ContMDiff.contMDiffOn hf
  have hsrc : (extChartAt 𝓘(ℝ, ℝ) (f x)).source = Set.univ := by
    rw [extChartAt_source]; rfl
  have h := (contMDiffOn_iff.mp hid).2 x (f x)
  rw [hsrc] at h
  simp only [Set.preimage_univ, Set.univ_inter] at h
  have h' : ContDiffOn ℝ ∞ (⇑(extChartAt 𝓘(ℝ, ℝ) (f x)) ∘ f ∘ ⇑(extChartAt (𝓡 2) x).symm)
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target := by
    simpa using h
  refine ContDiffOn.congr h' fun y hy => ?_
  simp [chartRep, Function.comp_def, extChartAt, OpenPartialHomeomorph.extend,
    chartAt_self_eq]

/-- The transition map between two charts is smooth on the overlap of the first chart's target
with the preimage of the second chart's source. -/
lemma contDiffOn_chartTransition (a b : M) :
    ContDiffOn ℝ ∞ (chartTrans a b)
      ((chartAt (EuclideanSpace ℝ (Fin 2)) a).target ∩
        (chartAt (EuclideanSpace ℝ (Fin 2)) a).symm ⁻¹'
          (chartAt (EuclideanSpace ℝ (Fin 2)) b).source) := by
  have hid : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (id : M → M) Set.univ :=
    ContMDiff.contMDiffOn (contMDiff_id (I := 𝓡 2) (M := M) (n := ∞))
  have h := (contMDiffOn_iff.mp hid).2 a b
  simp only [Set.univ_inter, Set.preimage_id] at h
  refine ContDiffOn.congr (h.mono ?_) ?_
  · intro y hy
    simpa using hy
  · intro y hy
    simp [chartTrans]

/-- The transition map between two charts is smooth at the image of a common point. -/
lemma contDiffAt_chartTransition (a b z : M)
    (hz : z ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) a).source)
    (hz' : z ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) b).source) :
    ContDiffAt ℝ ∞ (chartTrans a b) ((chartAt (EuclideanSpace ℝ (Fin 2)) a) z) := by
  refine (contDiffOn_chartTransition a b).contDiffAt ?_
  refine Filter.inter_mem ((chartAt (EuclideanSpace ℝ (Fin 2)) a).open_target.mem_nhds
    ((chartAt (EuclideanSpace ℝ (Fin 2)) a).map_source hz)) ?_
  refine ContinuousAt.preimage_mem_nhds
    ((chartAt (EuclideanSpace ℝ (Fin 2)) a).continuousAt_symm
      ((chartAt (EuclideanSpace ℝ (Fin 2)) a).map_source hz)) ?_
  rw [OpenPartialHomeomorph.left_inv _ hz]
  exact (chartAt (EuclideanSpace ℝ (Fin 2)) b).open_source.mem_nhds hz'

end Smoothness

section Critical

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- The derivative of a transition map between two charts at a common point of their sources is a
linear isomorphism. -/
lemma bijective_fderiv_chartTransition (x p : M)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    Function.Bijective (fderiv ℝ (chartTrans p x) ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x)) := by
  set φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)) :=
    chartAt (EuclideanSpace ℝ (Fin 2)) p with hφ
  set ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)) :=
    chartAt (EuclideanSpace ℝ (Fin 2)) x with hψ
  set τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun y => ψ (φ.symm y) with hτdef
  set σ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun y => φ (ψ.symm y) with hσdef
  have hxp : x ∈ ψ.source := mem_chart_source _ x
  have hτ : DifferentiableAt ℝ τ (φ x) :=
    ((contDiffAt_chartTransition p x x hx hxp).differentiableAt (by simp))
  have hσ : DifferentiableAt ℝ σ (ψ x) :=
    ((contDiffAt_chartTransition x p x hxp hx).differentiableAt (by simp))
  have hσt : φ (ψ.symm (ψ x)) = φ x := by rw [OpenPartialHomeomorph.left_inv _ hxp]
  have hτu : ψ (φ.symm (φ x)) = ψ x := by rw [OpenPartialHomeomorph.left_inv _ hx]
  have hV : {y | ψ.symm y ∈ φ.source} ∩ ψ.target ∈ 𝓝 (ψ x) := by
    refine Filter.inter_mem ?_ (ψ.open_target.mem_nhds (ψ.map_source hxp))
    refine ContinuousAt.preimage_mem_nhds (ψ.continuousAt_symm (ψ.map_source hxp)) ?_
    rw [OpenPartialHomeomorph.left_inv _ hxp]
    exact φ.open_source.mem_nhds hx
  have heq1 : τ ∘ σ =ᶠ[𝓝 (ψ x)] id := by
    filter_upwards [hV] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    change ψ (φ.symm (φ (ψ.symm y))) = id y
    rw [OpenPartialHomeomorph.left_inv _ hy1, OpenPartialHomeomorph.right_inv _ hy2]
    rfl
  have hW : {y | φ.symm y ∈ ψ.source} ∩ φ.target ∈ 𝓝 (φ x) := by
    refine Filter.inter_mem ?_ (φ.open_target.mem_nhds (φ.map_source hx))
    refine ContinuousAt.preimage_mem_nhds (φ.continuousAt_symm (φ.map_source hx)) ?_
    rw [OpenPartialHomeomorph.left_inv _ hx]
    exact ψ.open_source.mem_nhds hxp
  have heq2 : σ ∘ τ =ᶠ[𝓝 (φ x)] id := by
    filter_upwards [hW] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    change φ (ψ.symm (ψ (φ.symm y))) = id y
    rw [OpenPartialHomeomorph.left_inv _ hy1, OpenPartialHomeomorph.right_inv _ hy2]
    rfl
  have hτ₂ : DifferentiableAt ℝ τ (φ (ψ.symm (ψ x))) := hσt ▸ hτ
  have hσ₂ : DifferentiableAt ℝ σ (ψ (φ.symm (φ x))) := hτu ▸ hσ
  have hcomp1 := HasFDerivAt.comp (ψ x) hτ₂.hasFDerivAt hσ.hasFDerivAt
  have hcomp2 := HasFDerivAt.comp (φ x) hσ₂.hasFDerivAt hτ.hasFDerivAt
  have hid : HasFDerivAt (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) (ψ x) := hasFDerivAt_id (ψ x)
  have hid2 : HasFDerivAt (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) (φ x) := hasFDerivAt_id (φ x)
  have hTS := (hcomp1.congr_of_eventuallyEq heq1.symm).unique hid
  have hST := (hcomp2.congr_of_eventuallyEq heq2.symm).unique hid2
  have hTS' : (fderiv ℝ τ (φ x)).comp (fderiv ℝ σ (ψ x))
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
    simpa only [hσt] using hTS
  have hST' : (fderiv ℝ σ (ψ x)).comp (fderiv ℝ τ (φ x))
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
    simpa only [hτu] using hST
  have hgoal : fderiv ℝ (chartTrans p x) ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x)
      = fderiv ℝ τ (φ x) := rfl
  rw [hgoal]
  constructor
  · intro a b hab
    calc a = (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) a := rfl
      _ = ((fderiv ℝ σ (ψ x)).comp (fderiv ℝ τ (φ x))) a := by rw [hST']
      _ = (fderiv ℝ σ (ψ x)) ((fderiv ℝ τ (φ x)) a) := by
            rw [ContinuousLinearMap.comp_apply]
      _ = (fderiv ℝ σ (ψ x)) ((fderiv ℝ τ (φ x)) b) := by rw [hab]
      _ = ((fderiv ℝ σ (ψ x)).comp (fderiv ℝ τ (φ x))) b := by
            rw [ContinuousLinearMap.comp_apply]
      _ = (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) b := by rw [hST']
      _ = b := rfl
  · intro w
    refine ⟨(fderiv ℝ σ (ψ x)) w, ?_⟩
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) =>
      L w) hTS'
    simpa [ContinuousLinearMap.comp_apply] using h

/-- Criticality of `f` at `x` is equivalent to the vanishing of the derivative of the chart
representative of `f` in the chart at `x`. -/
lemma isCritical_iff_chartRep_chartAt (f : M → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Work.Drive.Morse.IsCritical f x ↔ chartDf f x = 0 := by
  have h := isCritical_iff_chartRep f hf x x (mem_extChartAt_source x)
  have h1 : (fun y : EuclideanSpace ℝ (Fin 2) => f ((extChartAt (𝓡 2) x).symm y)) =
      chartRep f x := by
    funext y; simp [chartRep]
  have h2 : (extChartAt (𝓡 2) x) x = (chartAt (EuclideanSpace ℝ (Fin 2)) x) x := by simp
  rw [h1, h2] at h
  exact h

end Critical

section HessianChange

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **The Hessian in two charts, applied to a vector.**  If `x` is a critical point of `f`
(expressed in the chart at `x`), then the Hessian of the chart representative of `f` in any chart
`chartAt p` containing `x` is obtained from the Hessian in the chart at `x` by pre- and
post-composition with the derivative `T` of the transition map:
`H_p v = (H_x (T v)) ∘ T` for every `v`. -/
theorem fderiv_fderiv_chartRep_apply (f : M → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (x p : M)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    (hcrit : chartDf f x = 0)
    (v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ (chartRep f p)) ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x) v
      = ((fderiv ℝ (fderiv ℝ (chartRep f x)) ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x))
          ((fderiv ℝ (chartTrans p x) ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x)) v)).comp
        (fderiv ℝ (chartTrans p x) ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x)) := by
  set φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)) :=
    chartAt (EuclideanSpace ℝ (Fin 2)) p with hφ
  set ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)) :=
    chartAt (EuclideanSpace ℝ (Fin 2)) x with hψ
  set τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun y => ψ (φ.symm y) with hτdef
  set gφ : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => f (φ.symm y) with hgφ
  set gψ : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => f (ψ.symm y) with hgψ
  set Hψ : EuclideanSpace ℝ (Fin 2) →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
    fderiv ℝ (fderiv ℝ gψ) (ψ x) with hHψ
  have hcrit' : fderiv ℝ gψ (ψ x) = 0 := hcrit
  -- smoothness
  have hgψ_sm : ContDiffAt ℝ 2 gψ (ψ x) :=
    ((contDiffOn_chartRep_center f hf x).contDiffAt
      (ψ.open_target.mem_nhds (ψ.map_source (mem_chart_source _ x)))).of_le (by decide)
  have hgψ_sm1 : DifferentiableAt ℝ (fderiv ℝ gψ) (ψ x) :=
    (hgψ_sm.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)
  have hτ_sm : ContDiffAt ℝ 2 τ (φ x) :=
    ((contDiffOn_chartTransition p x).contDiffAt
      (Filter.inter_mem (φ.open_target.mem_nhds (φ.map_source hx))
        (by
          refine ContinuousAt.preimage_mem_nhds (φ.continuousAt_symm (φ.map_source hx)) ?_
          rw [OpenPartialHomeomorph.left_inv _ hx]
          exact ψ.open_source.mem_nhds (mem_chart_source _ x)))).of_le (by decide)
  have hτ_diff : DifferentiableAt ℝ τ (φ x) := hτ_sm.differentiableAt (by decide)
  have hτ_sm1 : DifferentiableAt ℝ (fderiv ℝ τ) (φ x) :=
    (hτ_sm.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)
  have hτφx : τ (φ x) = ψ x := by
    change ψ (φ.symm (φ x)) = ψ x
    rw [OpenPartialHomeomorph.left_inv _ hx]
  -- the open neighbourhood on which `φ.symm` lands in the source of `ψ`
  set V : Set (EuclideanSpace ℝ (Fin 2)) :=
    interior (φ.target ∩ φ.symm ⁻¹' ψ.source) with hV
  have hV_nhds : V ∈ 𝓝 (φ x) := by
    rw [hV, interior_mem_nhds]
    exact Filter.inter_mem (φ.open_target.mem_nhds (φ.map_source hx))
      (by
        refine ContinuousAt.preimage_mem_nhds (φ.continuousAt_symm (φ.map_source hx)) ?_
        rw [OpenPartialHomeomorph.left_inv _ hx]
        exact ψ.open_source.mem_nhds (mem_chart_source _ x))
  have hV_sub : V ⊆ φ.target ∩ φ.symm ⁻¹' ψ.source := interior_subset
  have hVeq : ∀ y ∈ V, gφ y = gψ (τ y) := by
    intro y hy
    obtain ⟨hy2, hy1⟩ := hV_sub hy
    change f (φ.symm y) = f (ψ.symm (ψ (φ.symm y)))
    rw [OpenPartialHomeomorph.left_inv _ hy1]
  have hderiv1 : fderiv ℝ gφ =ᶠ[𝓝 (φ x)] fderiv ℝ (fun y => gψ (τ y)) := by
    refine Filter.eventually_of_mem hV_nhds fun y hy => ?_
    exact Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (isOpen_interior.mem_nhds hy)
      fun z hz => hVeq z hz)
  have hchain : fderiv ℝ (fun y => gψ (τ y)) =ᶠ[𝓝 (φ x)]
      fun y => (fderiv ℝ gψ (τ y)).comp (fderiv ℝ τ y) := by
    refine Filter.eventually_of_mem hV_nhds fun y hy => ?_
    obtain ⟨hy2, hy1⟩ := hV_sub hy
    have h1 : DifferentiableAt ℝ gψ (τ y) :=
      ((contDiffOn_chartRep_center f hf x).contDiffAt
        (ψ.open_target.mem_nhds (ψ.map_source hy1))).differentiableAt (by decide)
    have h2 : DifferentiableAt ℝ τ y :=
      ((contDiffOn_chartTransition p x).contDiffAt
        (Filter.mem_of_superset (isOpen_interior.mem_nhds hy) hV_sub)).differentiableAt (by decide)
    exact fderiv_comp y h1 h2
  -- the product rule
  have hA : HasFDerivAt (fun y => fderiv ℝ gψ (τ y)) (Hψ.comp (fderiv ℝ τ (φ x))) (φ x) := by
    have h1 : HasFDerivAt (fderiv ℝ gψ) (fderiv ℝ (fderiv ℝ gψ) (ψ x)) (ψ x) :=
      hgψ_sm1.hasFDerivAt
    have h1' : HasFDerivAt (fderiv ℝ gψ) (fderiv ℝ (fderiv ℝ gψ) (τ (φ x))) (τ (φ x)) := by
      simpa only [hτφx] using h1
    have h2 : HasFDerivAt τ (fderiv ℝ τ (φ x)) (φ x) := hτ_diff.hasFDerivAt
    simpa only [Function.comp_def, hHψ, hτφx] using h1'.comp (φ x) h2
  have hB : HasFDerivAt (fderiv ℝ τ) (fderiv ℝ (fderiv ℝ τ) (φ x)) (φ x) :=
    hτ_sm1.hasFDerivAt
  have hprod := hA.clm_comp hB
  have hgoal : fderiv ℝ (fderiv ℝ (chartRep f p))
        ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x) = fderiv ℝ (fderiv ℝ gφ) (φ x) := rfl
  have hCLM : fderiv ℝ (fderiv ℝ (chartRep f p)) ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x)
      = ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) ℝ).flip
          (chartDeriv p x)).comp ((chartHess f x).comp (chartDeriv p x)) := by
    rw [hgoal, Filter.EventuallyEq.fderiv_eq hderiv1, Filter.EventuallyEq.fderiv_eq hchain,
      hprod.fderiv, hτφx, hcrit']
    simp only [map_zero, ContinuousLinearMap.zero_comp, zero_add]
    rfl
  rw [hCLM]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  rfl

end HessianChange

section Transfer

/-- Linear algebra of the chart change: a bilinear form whose two chart expressions differ by
pre- and post-composition with an invertible `T` is nondegenerate (as a left bilinear form,
i.e. injective) in one chart exactly when it is in the other. -/
lemma injective_hessian_iff
    {Hx : EuclideanSpace ℝ (Fin 2) →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)}
    {T : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)} (hT : Function.Bijective T)
    {Hp : EuclideanSpace ℝ (Fin 2) →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)}
    (hH : ∀ v, Hp v = (Hx (T v)).comp T) :
    Function.Injective Hx ↔ Function.Injective Hp := by
  constructor
  · intro hinj a b hab
    have h1 : Hx (T a) = Hx (T b) := by
      ext u
      obtain ⟨z, rfl⟩ := hT.2 u
      have h := congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => L z) hab
      simpa [hH, ContinuousLinearMap.comp_apply] using h
    exact hT.1 (hinj h1)
  · intro hinj a b hab
    obtain ⟨a', rfl⟩ := hT.2 a
    obtain ⟨b', rfl⟩ := hT.2 b
    have h1 : Hp a' = Hp b' := by rw [hH a', hH b', hab]
    rw [hinj h1]

end Transfer

open scoped Manifold ContDiff in
/-- At a critical point, the nondegeneracy of the Hessian is independent of the chart: it holds for
the chart `extChartAt x` used in the definition of `NondegCrit` iff it holds for any chart `chartAt p`
containing `x`. -/
theorem nondegCrit_iff_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] (f : M → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (x p : M)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    (hc : Work.Drive.Morse.IsCritical f x) :
    Work.Drive.Morse.NondegCrit f x ↔ Function.Injective
      (fderiv ℝ (fderiv ℝ (fun y => f ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y)))
        ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x)) := by
  have hcrit : chartDf f x = 0 := (isCritical_iff_chartRep_chartAt f hf x).mp hc
  have hinner : fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 2) x).symm)) ((extChartAt (𝓡 2) x) x)
      = chartHess f x := by
    have hfun : (f ∘ (extChartAt (𝓡 2) x).symm) = chartRep f x := by
      funext y; simp [chartRep]
    have hpt : (extChartAt (𝓡 2) x) x = (chartAt (EuclideanSpace ℝ (Fin 2)) x) x := by simp
    unfold chartHess
    rw [hfun, hpt]
  have hL : Work.Drive.Morse.NondegCrit f x ↔ Function.Injective (chartHess f x) := by
    unfold Work.Drive.Morse.NondegCrit
    rw [hinner]
    exact and_iff_right hc
  rw [hL]
  change Function.Injective (chartHess f x) ↔
    Function.Injective (fderiv ℝ (fderiv ℝ (chartRep f p))
      ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x))
  exact injective_hessian_iff (bijective_fderiv_chartTransition x p hx)
    (fderiv_fderiv_chartRep_apply f hf x p hx hcrit)

end Work.Drive.N2
