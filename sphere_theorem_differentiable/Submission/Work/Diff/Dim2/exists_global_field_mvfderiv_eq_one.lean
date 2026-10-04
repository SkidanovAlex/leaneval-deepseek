import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.GE.exists_smooth_section_eq_nhds
import Submission.Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

/-- **Smoothness of a section prescribed in chart coordinates.**

If `f : M → E` is `C^∞` at `x` and `x` lies in the base set of the tangent-bundle trivialisation
at `x₀`, then the section whose chart coordinates (in the chart at `x₀`) are `f` is `C^∞` at `x`.

This is the "read the smoothness of a section in a trivialisation" direction of
`Trivialization.contMDiffAt_section_iff`: the coordinate expression of the section in the
trivialisation at `x₀` is `f` itself. -/
lemma contMDiffAt_symmL_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {x₀ x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    {f : M → E} (hf : ContMDiffAt I 𝓘(ℝ,E) ∞ f x) :
    ContMDiffAt I I.tangent ∞
      (fun z : M => (⟨z, (trivializationAt E (TangentSpace I) x₀).symmL ℝ z (f z)⟩ :
        TotalSpace E (TangentSpace I))) x := by
  rw [Trivialization.contMDiffAt_section_iff (trivializationAt E (TangentSpace I) x₀) hx]
  refine hf.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx] with y hy
  rw [Trivialization.symmL_apply _ hy (f y)]
  exact congrArg Prod.snd (Trivialization.apply_mk_symm _ hy (f y))

theorem exists_global_field_mvfderiv_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    {ϑ : M → ℝ} (hϑ : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ ϑ)
    {x₀ : M} {e : TangentSpace I x₀} (he : mvfderiv I ϑ x₀ e = 1) :
    ∃ W : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
        (fun y : M => (⟨y, W y⟩ : Bundle.TotalSpace E (TangentSpace I))) ∧
      W x₀ = e ∧
      (∀ᶠ y in 𝓝 x₀, mvfderiv I ϑ y (W y) = 1) := by
  classical
  -- ## Chart data at `x₀`
  let c : E := (extChartAt I x₀) x₀
  let G : E → ℝ := fun z => ϑ ((extChartAt I x₀).symm z)
  -- the chart coordinates of `e`
  let v : E := (mfderiv I 𝓘(ℝ,E) (extChartAt I x₀) x₀) e
  -- ## The chart-coordinate vector `v` corresponds to the tangent vector `e`
  have hframe : Submission.Geodesic.frameVector (I := I) x₀ x₀ v = e := by
    have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) (x := x₀) (y := x₀)
      (mem_extChartAt_source x₀)
    have hev := congrArg (fun (L : TangentSpace I x₀ →L[ℝ] TangentSpace I x₀) => L e) hcomp
    simp only [ContinuousLinearMap.id_apply] at hev
    show (trivializationAt E (TangentSpace I) x₀).symmL ℝ x₀ v = e
    rw [TangentBundle.symmL_trivializationAt (I := I) (mem_chart_source H x₀)]
    exact hev
  -- ## `G` is smooth on the chart target, and so are its derivative and the functional `z ↦ dG_z v`
  have hGmd : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ G (extChartAt I x₀).target :=
    (hϑ.contMDiffOn (s := Set.univ)).comp (contMDiffOn_extChartAt_symm (I := I) x₀)
      (fun z _ => trivial)
  have hGon : ContDiffOn ℝ ∞ G (extChartAt I x₀).target := contMDiffOn_iff_contDiffOn.mp hGmd
  have hG : ContDiffAt ℝ ∞ G c :=
    hGon.contDiffAt ((isOpen_extChartAt_target (I := I) x₀).mem_nhds (mem_extChartAt_target x₀))
  have hfderivOn : ContDiffOn ℝ ∞ (fderiv ℝ G) (extChartAt I x₀).target :=
    hGon.fderiv_of_isOpen (isOpen_extChartAt_target (I := I) x₀) (by simp)
  have hlamOn : ContDiffOn ℝ ∞ (fun z : E => fderiv ℝ G z v) (extChartAt I x₀).target :=
    hfderivOn.clm_apply (contDiffOn_const (c := v))
  have hlam : ContDiffAt ℝ ∞ (fun z : E => fderiv ℝ G z v) c :=
    hlamOn.contDiffAt ((isOpen_extChartAt_target (I := I) x₀).mem_nhds (mem_extChartAt_target x₀))
  -- ## `dG_c v = dϑ_{x₀} e = 1`
  have hv1 : fderiv ℝ G c v = 1 := by
    have h := Work.Diff.T.mvfderiv_frameVector_real (I := I) (x₀ := x₀) (p := x₀)
      (mem_chart_source H x₀) (g := ϑ) (hϑ.mdifferentiableAt (by simp)) v
    rw [hframe, he] at h
    simpa [G, c] using h.symm
  -- ## The inverse functional `g` is smooth wherever it is defined
  let g : E → E := fun z => (fderiv ℝ G z v)⁻¹ • v
  have hgAt : ∀ z : E, z ∈ (extChartAt I x₀).target → fderiv ℝ G z v ≠ 0 →
      ContDiffAt ℝ ∞ g z := by
    intro z hz hne
    have hmem : (extChartAt I x₀).target ∈ 𝓝 z :=
      (isOpen_extChartAt_target (I := I) x₀).mem_nhds hz
    have h1 : ContDiffAt ℝ ∞ (fderiv ℝ G) z := hfderivOn.contDiffAt hmem
    have h2 : ContDiffAt ℝ ∞ (fun w : E => fderiv ℝ G w v) z :=
      h1.clm_apply (contDiffAt_const (c := v))
    have h3 : ContDiffAt ℝ ∞ (fun w : E => (fderiv ℝ G w v)⁻¹) z := h2.inv hne
    show ContDiffAt ℝ ∞ (fun w : E => (fderiv ℝ G w v)⁻¹ • v) z
    exact h3.smul (contDiffAt_const (c := v))
  -- ## the coordinate function of the local field
  let f : M → E := fun y => g ((extChartAt I x₀) y)
  have hfAt : ∀ y : M, y ∈ (chartAt H x₀).source →
      fderiv ℝ G ((extChartAt I x₀) y) v ≠ 0 → ContMDiffAt I 𝓘(ℝ,E) ∞ f y := by
    intro y hy hne
    have hys : y ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
    have hzt : (extChartAt I x₀) y ∈ (extChartAt I x₀).target :=
      (extChartAt I x₀).map_source hys
    have hg : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ g ((extChartAt I x₀) y) :=
      (hgAt _ hzt hne).contMDiffAt
    exact ContMDiffAt.comp y hg (contMDiffAt_extChartAt' hy)
  -- ## the local field
  let X : (y : M) → TangentSpace I y :=
    fun y => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (f y)
  -- ## the good set is a neighbourhood of `x₀`
  have hcontχ : ContinuousAt (extChartAt I x₀) x₀ :=
    (contMDiffAt_extChartAt (I := I) (x := x₀) (n := ∞)).continuousAt
  have hU : {y : M | y ∈ (chartAt H x₀).source ∧
      fderiv ℝ G ((extChartAt I x₀) y) v ≠ 0} ∈ 𝓝 x₀ := by
    refine Filter.inter_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)) ?_
    have hne : fderiv ℝ G c v ≠ 0 := by
      rw [hv1]
      norm_num
    have hmem : {z : E | fderiv ℝ G z v ≠ 0} ∈ 𝓝 ((extChartAt I x₀) x₀) := by
      rw [show (extChartAt I x₀) x₀ = c from rfl]
      exact Filter.eventually_iff.mp (hlam.continuousAt.eventually_ne hne)
    exact hcontχ.preimage_mem_nhds hmem
  -- ## `X` is smooth on a neighbourhood of `x₀`
  have hXev : ∀ᶠ y in 𝓝 x₀, ContMDiffAt I I.tangent ∞
      (fun z : M => (⟨z, X z⟩ : TotalSpace E (TangentSpace I))) y := by
    refine Filter.eventually_of_mem hU (fun y hy => ?_)
    have hbase : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
      simpa [← extChartAt_source] using hy.1
    exact contMDiffAt_symmL_apply (x₀ := x₀) (x := y) hbase (hfAt y hy.1 hy.2)
  -- ## `dϑ(X) = 1` on a neighbourhood of `x₀`
  have hX1 : ∀ᶠ y in 𝓝 x₀, mvfderiv I ϑ y (X y) = 1 := by
    refine Filter.eventually_of_mem hU (fun y hy => ?_)
    have hkey := Work.Diff.T.mvfderiv_frameVector_real (I := I) (x₀ := x₀) (p := y) hy.1
      (g := ϑ) (hϑ.mdifferentiableAt (by simp)) (f y)
    have hfy : f y = (fderiv ℝ G ((extChartAt I x₀) y) v)⁻¹ • v := rfl
    show mvfderiv I ϑ y (X y) = 1
    rw [show X y = Submission.Geodesic.frameVector (I := I) x₀ y (f y) from rfl]
    rw [hkey]
    show fderiv ℝ G ((extChartAt I x₀) y) (f y) = 1
    rw [hfy, ContinuousLinearMap.map_smul, smul_eq_mul, inv_mul_cancel₀ hy.2]
  -- ## cut off to a global smooth section
  obtain ⟨W, hWsm, hWx, hWX⟩ :=
    Work.Diff.GE.exists_smooth_section_eq_nhds (I := I) (x := x₀) X hXev
  refine ⟨W, hWsm, ?_, ?_⟩
  · rw [hWx]
    show (trivializationAt E (TangentSpace I) x₀).symmL ℝ x₀ (f x₀) = e
    have hfc : f x₀ = v := by
      show (fderiv ℝ G c v)⁻¹ • v = v
      rw [hv1, inv_one, one_smul]
    rw [hfc]
    exact hframe
  · filter_upwards [hWX, hX1] with y hy1 hy2
    rw [hy1, hy2]

end Work.Diff.Dim2
