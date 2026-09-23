import Submission.ChartCoordsTrans
import Submission.CurveCov
import Submission.RauchGlobal
import Submission.BonnetMyers
import Submission.IndexCorner

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.JacobiCoords
open Submission.ChartCoordsTrans
open Submission.ChartCurv
open Submission.RauchGlobal
open Submission.BonnetMyers
open Submission.IntrinsicVariation
open Submission.Jacobi

/-!
# The covariant derivative of a field along a curve, as a global field

For the shortening argument of the global `σ ≤ κ` (`ConjCut.CutConjInequality`) one needs the
covariant derivative `∇_{γ'}J` of a Jacobi field along a curve as a **global field along the curve**:
the cover lemmas `IndexIntrinsic2.integral_idxAlong_eq_zero_of_cover` and
`IndexIntrinsic2.integral_bilAlong_corner_of_cover` take the pair `(V,Z)` as global data, with the
per-piece identification `Z t = frameVector x₀ (γ t) (DtQ … t)`.

The field is *defined* by writing it in the chart at the base point `γ t` of the tangent space in
which the value lives (so the definition does not depend on a cover), and its two properties are

* **`covAlong_eq_cov`** — it is `∇_{γ'}𝒱` for any globally smooth section `𝒱` agreeing with `V` along
  `γ` near `t` (the intrinsic characterisation, from which the per-piece identifications follow);
* **`covAlong_eq_chart`** — it is the chart formula `DtQ` in any chart in which the curve and the
  field are described by the piece data of a cover (the identification clause of `IsJacobiPiece` and
  `IsBilPiece`).

The smoothness input is isolated in the predicate `SmoothAlongAt γ V t` (the chart-`γ t` coordinates
of `V` are `C^∞` near `t`), produced from `IsJacobiAt` by `smoothAlongAt_of_isJacobiAt` and from a
chart formula by `smoothAlongAt_frameVector`.
-/

namespace Submission.JacobiGlobal
noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- The germ of `γ` at `t` lies in the chart at `γ t`. -/
lemma eventually_mem_source_self {γ : ℝ → M} {t : ℝ} (hγ : ContinuousAt γ t) :
    ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (γ t)).source :=
  hγ.preimage_mem_nhds ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t)))

/-- **The chart coordinates of a Jacobi field are `C^∞`** (on any open set on which the curve stays
in the chart source and the field is Jacobi at every point). -/
theorem contDiffOn_chartCoords_of_isJacobiAt (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)} {x₀ : M} {U : Set ℝ}
    (hU : IsOpen U) (hγU : ContMDiffOn 𝓘(ℝ) I ∞ γ U)
    (hsrcU : ∀ s ∈ U, γ s ∈ (chartAt H x₀).source)
    (hJ : ∀ s ∈ U, IsJacobiAt cov γ J s) :
    ContDiffOn ℝ ∞ (chartCoords (I := I) x₀ γ J) U := by
  rw [hU.contDiffOn_iff]
  intro s hs
  -- a small interval around `s` inside `U`
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hs)
  have hεball : Ioo (s - ε) (s + ε) ⊆ U := by
    intro u hu
    exact hεsub (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  -- the local chart in which the coordinates are smooth
  obtain ⟨x₁, η, hη, hηε, hsrc₁, hcd₁, -⟩ :=
    Submission.JacobiCoords.exists_chartCoords_contDiffOn (cov := cov) htor (s := s) (ε := ε) hε
      (hγU.mono hεball) (hJ s hs)
  -- transfer to the chart at `x₀` on a smaller interval
  set U₁ : Set ℝ := Ioo (s - η / 2) (s + η / 2) with hU₁def
  have hU₁open : IsOpen U₁ := isOpen_Ioo
  have hsub₁ : U₁ ⊆ Icc (s - η) (s + η) := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hsubU : U₁ ⊆ U := fun u hu => hεball (by
    refine ⟨?_, ?_⟩ <;> linarith [hu.1, hu.2, hη, hηε])
  have hsU₁ : s ∈ U₁ := ⟨by linarith, by linarith⟩
  have hsrc : ∀ u ∈ U₁, γ u ∈ (chartAt H x₁).source := fun u hu => hsrc₁ u (hsub₁ hu)
  have hsrc' : ∀ u ∈ U₁, γ u ∈ (chartAt H x₀).source := fun u hu => hsrcU u (hsubU hu)
  have hγU₁ : ContMDiffOn 𝓘(ℝ) I ∞ γ U₁ := hγU.mono hsubU
  have hV : ContDiffOn ℝ ∞ (chartCoords (I := I) x₁ γ J) U₁ := hcd₁.mono hsub₁
  exact ((contDiffOn_chartCoords_of_chartCoords (I := I) hU₁open hγU₁ hsrc hsrc' hV).contDiffAt
    (hU₁open.mem_nhds hsU₁))



/-- A function `C^∞` on an open set is, near each of its points, equal to its derivative. -/
lemma eventually_hasDerivAt_of_contDiffOn {f : ℝ → F} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s) (hf : ContDiffOn ℝ ∞ f s) :
    ∀ᶠ u in 𝓝 t, HasDerivAt f (deriv f u) u := by
  filter_upwards [hs.mem_nhds ht] with u hu
  have hd : DifferentiableAt ℝ f u :=
    (hf.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hu)
  exact hd.hasDerivAt

/-- A field along a curve is **smooth along the curve at `t`** (in the sense of the chart at `γ t`,
which is the chart used by `covAlong`). -/
def SmoothAlongAt (γ : ℝ → M) (V : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) : Prop :=
  ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ (∀ s ∈ U, γ s ∈ (chartAt H (γ t)).source) ∧
    ContDiffOn ℝ ∞ (chartCoords (I := I) (γ t) γ V) U

/-- **The covariant derivative `∇_{γ'}V` of a field along a curve**, as a field along the curve.  It
is written in the chart at the base point `γ t` of the tangent space in which the value lives, which
makes it a global function of `t` (see `covAlong_eq_cov` for its intrinsic characterisation). -/
noncomputable def covAlong (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {γ : ℝ → M} (V : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) : TangentSpace I (γ t) :=
  frameVector (I := I) (γ t) (γ t)
    (DtQ cov (γ t) (chartCoord (I := I) (γ t) γ) (chartCoords (I := I) (γ t) γ V)
      (deriv (chartCoord (I := I) (γ t) γ)) (deriv (chartCoords (I := I) (γ t) γ V)) t)

/-- The smoothness of a Jacobi field along a curve, in the form used by `covAlong`. -/
theorem smoothAlongAt_of_isJacobiAt (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hJ : ∀ s, IsJacobiAt cov γ J s) (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1))) :
    SmoothAlongAt (I := I) γ J t := by
  have htI : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hγc : ContinuousAt γ t :=
    (hγ.continuousOn.continuousAt (isOpen_Ioo.mem_nhds htI))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (eventually_mem_source_self (H := H) (γ := γ) (t := t) hγc)
  set δ' : ℝ := min δ 1 / 2 with hδ'def
  have hδ'pos : 0 < δ' := by rw [hδ'def]; positivity
  have hδ'ltδ : δ' < δ := by
    rw [hδ'def]; have h : min δ 1 ≤ δ := min_le_left _ _; linarith
  have hδ'lt1 : δ' < 1 := by
    rw [hδ'def]; have h : min δ 1 ≤ 1 := min_le_right _ _; linarith
  have hsub : Ioo (t - δ') (t + δ') ⊆ Ioo (t - 1) (t + 1) := by
    intro s hs
    exact ⟨by linarith [hs.1, hδ'lt1], by linarith [hs.2, hδ'lt1]⟩
  have hsrcI : ∀ s ∈ Ioo (t - δ') (t + δ'), γ s ∈ (chartAt H (γ t)).source := by
    intro s hs
    have hb : s ∈ Metric.ball t δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1, hδ'ltδ], by linarith [hs.2, hδ'ltδ]⟩
    exact hδsub hb
  refine ⟨Ioo (t - δ') (t + δ'), isOpen_Ioo, ⟨by linarith, by linarith⟩, hsrcI, ?_⟩
  exact contDiffOn_chartCoords_of_isJacobiAt (cov := cov) htor isOpen_Ioo (hγ.mono hsub) hsrcI
    (fun s _ => hJ s)

/-- **A globally smooth section agreeing with a field that is smooth along the curve.** -/
theorem exists_section_of_smoothAlongAt
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : curveVelocity (I := I) γ t ≠ 0) (hV : SmoothAlongAt (I := I) γ V t) :
    ∃ 𝒱 : Π x : M, TangentSpace I x, CMDiff ∞ (T% 𝒱) ∧ ∀ᶠ s in 𝓝 t, 𝒱 (γ s) = V s := by
  obtain ⟨U, hUopen, htU, hUsrc, hVcd⟩ := hV
  have htI : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds htU)
  set ε' : ℝ := min (min ε 1) (min ε 1) / 2 with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; positivity
  have hε'ltε : ε' < ε := by
    rw [hε'def]; have h : min (min ε 1) (min ε 1) ≤ ε := by
      have h1 : min (min ε 1) (min ε 1) = min ε 1 := min_self _
      rw [h1]; exact min_le_left _ _
    linarith
  have hε'lt1 : ε' < 1 := by
    rw [hε'def]; have h : min (min ε 1) (min ε 1) ≤ 1 := by
      have h1 : min (min ε 1) (min ε 1) = min ε 1 := min_self _
      rw [h1]; exact min_le_right _ _
    linarith
  set V₁ : Set ℝ := Ioo (t - ε') (t + ε') with hV₁def
  have hV₁open : IsOpen V₁ := by rw [hV₁def]; exact isOpen_Ioo
  have htV₁ : t ∈ V₁ := by rw [hV₁def]; exact ⟨by linarith, by linarith⟩
  have hV₁U : V₁ ⊆ U := by
    intro s hs
    have hb : s ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      rw [hV₁def] at hs
      exact ⟨by linarith [hs.1, hε'ltε], by linarith [hs.2, hε'ltε]⟩
    exact hεsub hb
  have hV₁sub : V₁ ⊆ Ioo (t - 1) (t + 1) := by
    intro s hs
    rw [hV₁def] at hs
    exact ⟨by linarith [hs.1, hε'lt1], by linarith [hs.2, hε'lt1]⟩
  have hγV : ContMDiffOn 𝓘(ℝ) I ∞ γ V₁ := hγ.mono hV₁sub
  have hα : ContDiffOn ℝ ∞ (chartCoords (I := I) (γ t) γ V) (V₁ ∩ γ ⁻¹' (chartAt H (γ t)).source) :=
    hVcd.mono (fun s hs => hV₁U hs.1)
  obtain ⟨𝒱, h𝒱sm, h𝒱ev⟩ :=
    Submission.CurveField.exists_contMDiff_section_eventuallyEq_of_contDiffOn
      (I := I) (γ := γ) (V := V₁) hV₁open htV₁ hγV hne hα
  refine ⟨𝒱, h𝒱sm, ?_⟩
  have hsrcEv : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (γ t)).source := by
    filter_upwards [hV₁open.mem_nhds htV₁] with s hs
    exact hUsrc s (hV₁U hs)
  filter_upwards [h𝒱ev, hsrcEv] with s hs hsrc
  rw [hs, frameVector_chartCoords (I := I) hsrc]

/-- **The intrinsic characterisation of `covAlong`**: it is `∇_{γ'}𝒱` for any globally smooth
section `𝒱` agreeing with `V` along `γ` near `t`. -/
theorem covAlong_eq_cov (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : curveVelocity (I := I) γ t ≠ 0) (hV : SmoothAlongAt (I := I) γ V t)
    {𝒱 : Π x : M, TangentSpace I x} (h𝒱sm : CMDiff ∞ (T% 𝒱))
    (h𝒱ev : ∀ᶠ s in 𝓝 t, 𝒱 (γ s) = V s) :
    covAlong cov V t = cov 𝒱 (γ t) (curveVelocity (I := I) γ t) := by
  have htI : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (hγ.contMDiffAt (isOpen_Ioo.mem_nhds htI)).mdifferentiableAt (by simp)
  have hγc : ContinuousAt γ t := hγmd.continuousAt
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (eventually_mem_source_self (H := H) hγc)
  set δ' : ℝ := min δ 1 / 2 with hδ'def
  have hδ'pos : 0 < δ' := by rw [hδ'def]; positivity
  have hδ'ltδ : δ' < δ := by
    rw [hδ'def]; have h : min δ 1 ≤ δ := min_le_left _ _; linarith
  have hδ'lt1 : δ' < 1 := by
    rw [hδ'def]; have h : min δ 1 ≤ 1 := min_le_right _ _; linarith
  set I₀ : Set ℝ := Ioo (t - δ') (t + δ') with hI₀def
  have hI₀open : IsOpen I₀ := by rw [hI₀def]; exact isOpen_Ioo
  have htI₀ : t ∈ I₀ := by rw [hI₀def]; exact ⟨by linarith, by linarith⟩
  have hI₀src : ∀ u ∈ I₀, γ u ∈ (chartAt H (γ t)).source := by
    intro u hu
    refine hδsub ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    rw [hI₀def] at hu
    exact ⟨by linarith [hu.1, hδ'ltδ], by linarith [hu.2, hδ'ltδ]⟩
  have hI₀sub : I₀ ⊆ Ioo (t - 1) (t + 1) := by
    intro u hu
    rw [hI₀def] at hu
    exact ⟨by linarith [hu.1, hδ'lt1], by linarith [hu.2, hδ'lt1]⟩
  have hsrcEv : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (γ t)).source := by
    filter_upwards [hI₀open.mem_nhds htI₀] with s hs
    exact hI₀src s hs
  have huTgt : ∀ᶠ s in 𝓝 t, chartCoord (I := I) (γ t) γ s ∈ (extChartAt I (γ t)).target := by
    filter_upwards [hsrcEv] with s hs
    exact (extChartAt I (γ t)).map_source (by rwa [extChartAt_source])
  have hγeq : γ =ᶠ[𝓝 t] fun s => (extChartAt I (γ t)).symm (chartCoord (I := I) (γ t) γ s) := by
    filter_upwards [hsrcEv] with s hs
    show γ s = (extChartAt I (γ t)).symm ((extChartAt I (γ t)) (γ s))
    exact (PartialEquiv.left_inv (extChartAt I (γ t)) (by rwa [extChartAt_source])).symm
  have hcoord : ∀ᶠ s in 𝓝 t, HasDerivAt (chartCoord (I := I) (γ t) γ)
      (deriv (chartCoord (I := I) (γ t) γ) s) s :=
    eventually_hasDerivAt_of_contDiffOn hI₀open htI₀
      (Submission.SecondVarGlobal.contDiffOn_chartCoord (I := I) (z₀ := γ t)
        (hγ.mono hI₀sub) hI₀src)
  have hyloc : ∀ᶠ s in 𝓝 t, HasDerivAt (chartCoords (I := I) (γ t) γ V)
      (deriv (chartCoords (I := I) (γ t) γ V) s) s := by
    obtain ⟨U, hUopen, htU, -, hcd⟩ := hV
    exact eventually_hasDerivAt_of_contDiffOn hUopen htU hcd
  have hy : ∀ᶠ s in 𝓝 t, frameVector (I := I) (γ t) (γ s)
      (chartCoords (I := I) (γ t) γ V s) = 𝒱 (γ s) := by
    filter_upwards [hsrcEv, h𝒱ev] with s hs hev
    rw [frameVector_chartCoords (I := I) hs, hev]
  have h1 := Submission.ChartIndep.frameVector_chartCovDeriv_eq_cov (cov := cov)
    (γ := γ) (t₀ := t) (x₀ := γ t) (mem_chart_source H (γ t)) hsrcEv huTgt h𝒱sm hγeq hcoord hy hγmd
  have h2 : covAlong cov V t
      = frameVector (I := I) (γ t) (γ t)
        (chartCovDeriv cov (γ t) (chartCoord (I := I) (γ t) γ)
          (deriv (chartCoord (I := I) (γ t) γ)) (chartCoords (I := I) (γ t) γ V) t) := by
    rw [covAlong]
    congr 1
    refine (Submission.IndexCorner.chartCovDeriv_eq_DtQ (cov := cov) htor (γ t)
      (u := chartCoord (I := I) (γ t) γ) (w := deriv (chartCoord (I := I) (γ t) γ))
      (F := chartCoords (I := I) (γ t) γ V)
      (F' := deriv (chartCoords (I := I) (γ t) γ V)) ?_ hyloc.self_of_nhds).symm
    show (extChartAt I (γ t)).symm ((extChartAt I (γ t)) (γ t)) ∈ (chartAt H (γ t)).source
    rw [PartialEquiv.left_inv _ (by rw [extChartAt_source]; exact mem_chart_source H (γ t))]
    exact mem_chart_source H (γ t)
  rw [h2, h1]

/-- **The chart formula for `covAlong`.**  In the chart data of a piece of a cover (a chart `x₀`, the
coordinate curve `u` of `γ` with velocity `w`, the coordinates `y` of the field with derivative
`y'`), the covariant derivative is the chart formula `DtQ` — this is the identification clause of
`IsJacobiPiece` and `IsBilPiece`. -/
theorem covAlong_eq_chart (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : curveVelocity (I := I) γ t ≠ 0) (hV : SmoothAlongAt (I := I) γ V t)
    {x₀ : M} {u w y y' : ℝ → E}
    (hsrc : γ t ∈ (chartAt H x₀).source)
    (hsrcEv : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H x₀).source)
    (huTgt : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    (hγeq : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s))
    (hu : ∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s)
    (hy : ∀ᶠ s in 𝓝 t, frameVector (I := I) x₀ (γ s) (y s) = V s)
    (hy' : ∀ᶠ s in 𝓝 t, HasDerivAt y (y' s) s) :
    covAlong cov V t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u y w y' t) := by
  have htI : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (hγ.contMDiffAt (isOpen_Ioo.mem_nhds htI)).mdifferentiableAt (by simp)
  obtain ⟨𝒱, h𝒱sm, h𝒱ev⟩ := exists_section_of_smoothAlongAt hγ hne hV
  have h1 : covAlong cov V t = cov 𝒱 (γ t) (curveVelocity (I := I) γ t) :=
    covAlong_eq_cov (cov := cov) htor hγ hne hV h𝒱sm h𝒱ev
  have hyW : ∀ᶠ s in 𝓝 t, frameVector (I := I) x₀ (γ s) (y s) = 𝒱 (γ s) := by
    filter_upwards [hy, h𝒱ev] with s hs hev
    rw [hs, hev]
  have h2 := Submission.ChartIndep.frameVector_chartCovDeriv_eq_cov (cov := cov)
    (γ := γ) (t₀ := t) hsrc hsrcEv huTgt h𝒱sm hγeq hu hyW hγmd
  have h3 : frameVector (I := I) x₀ (γ t) (chartCovDeriv cov x₀ u w y t)
      = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u y w y' t) := by
    congr 1
    exact Submission.IndexCorner.chartCovDeriv_eq_DtQ (cov := cov) htor x₀
      (u := u) (w := w) (F := y) (F' := y')
      (mem_source_chartCurve (I := I) huTgt.self_of_nhds)
      hy'.self_of_nhds
  rw [h1, ← h2, h3]

/-- The smoothness of a field given by coordinates in a (possibly other) chart, in the form used by
`covAlong`. -/
theorem smoothAlongAt_frameVector {z : M} {a : ℝ → E} {γ : ℝ → M} {U : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (htU : t ∈ U) (ha : ContDiffOn ℝ ∞ a U)
    (hγU : ContMDiffOn 𝓘(ℝ) I ∞ γ U)
    (hsrc : ∀ s ∈ U, γ s ∈ (chartAt H z).source)
    (hsrc' : ∀ s ∈ U, γ s ∈ (chartAt H (γ t)).source) :
    SmoothAlongAt (I := I) γ (fun s => frameVector (I := I) z (γ s) (a s)) t :=
  ⟨U, hU, htU, hsrc', contDiffOn_chartCoords_frameVector (I := I) hU ha hγU hsrc hsrc'⟩

end

end Submission.JacobiGlobal
