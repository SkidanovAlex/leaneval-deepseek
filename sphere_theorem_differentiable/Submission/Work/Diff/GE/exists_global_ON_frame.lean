import Mathlib
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.onFrameONfield
import Submission.Work.Diff.T.FrameExt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A globally smooth family of vector fields which is orthonormal near a point

For a smooth Riemannian metric `g` on a smooth manifold `M` and a point `x : M` there is a family
`W i` (`i : Fin (Module.finrank ℝ E)`) of *globally* `C^∞` vector fields which is a `g`-orthonormal
frame of `T_yM` for all `y` near `x`:

`Work.Diff.GE.exists_global_ON_frame`.

This is the global version of `Work.Diff.GE.smooth_onframe`, which produces fields that are only
smooth *at* `x` (see also `Work.Diff.GE.onFrameONfield`).  Since smoothness of a section is a local
condition, a globally defined family is obtained from a locally defined one by multiplying it with a
smooth bump function which equals `1` near `x` and whose closed support lies in the region where the
local family is smooth (`ContMDiffOn.smul_section_of_tsupport`); this is
`Work.Diff.GE.exists_global_smul_bump` below.

The local family is built by Gram–Schmidt (with respect to `g`) of a family of *globally* smooth
fields which near `x` coincides with the coordinate frame of the chart at `x`
(`Work.Diff.T.exists_global_eventuallyEq_symmL`), and it is orthonormal near `x` by
`Work.Diff.GE.isONFrame_gsNorm`:

* `Work.Diff.T.exists_global_eventuallyEq_symmL` makes the chart frame global,
* `Work.Diff.GE.coordFrame_chartSource_linearIndependent` says that the chart frame is a basis on
  the chart source, so the global fields are linearly independent near `x`,
* `Work.Diff.GE.gsNorm_contMDiffAt_of_linearIndependent` (in `onFrameONfield`) makes their
  Gram–Schmidt orthonormalisation smooth at `y` wherever the family is linearly independent at `y`.

Note the imports: this module deliberately uses `Work.Diff.GE.onFrameONfield` (which imports the
`curvbasic` family) but *not* `Work.Diff.GE.smooth_onframe` and not `bianchi_kato_defs`; the modules
`curvbasic` and `bianchi_kato_defs` both declare `Work.Diff.GE.exists_isONFrame`, so they can never
be imported together.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **The chart coordinate frame is linearly independent on the chart source.**  The section
`q ↦ (trivializationAt E (TangentSpace I) x).symmL ℝ q v` ("the tangent vector at `q` whose
coordinates in the chart at `x` are `v`") is a linear isomorphism over every point of the chart
source; hence the image of a basis of `E` is linearly independent there. -/
theorem coordFrame_chartSource_linearIndependent
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) {y : M}
    (hy : y ∈ (chartAt H x).source) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        (trivializationAt E (TangentSpace I) x).symmL ℝ y (b i)) := by
  have hb : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hy
  have hker : LinearMap.ker ((trivializationAt E (TangentSpace I) x).symmL ℝ y).toLinearMap = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro u v huv
    have h1 := Trivialization.continuousLinearMapAt_symmL (R := ℝ)
      (trivializationAt E (TangentSpace I) x) hb u
    have h2 := Trivialization.continuousLinearMapAt_symmL (R := ℝ)
      (trivializationAt E (TangentSpace I) x) hb v
    have h := congrArg (fun w => (trivializationAt E (TangentSpace I) x).continuousLinearMapAt
      ℝ y w) huv
    exact h1.symm.trans (h.trans h2)
  exact LinearIndependent.map' (R := ℝ) b.linearIndependent
    ((trivializationAt E (TangentSpace I) x).symmL ℝ y).toLinearMap hker

/-- **Cutting off a family of local sections by a bump function.**  If the sections `F i` are
smooth on an open set `U ∋ x`, there is a family `W i` of *globally* smooth sections which agrees
with `F i` near `x`.  Take a smooth bump function `ψ` with `ψ =ᶠ[𝓝 x] 1` and `tsupport ψ ⊆ U`
(`SmoothBumpFunction.nhds_basis_tsupport`) and set `W i := ψ • F i`; global smoothness is
`ContMDiffOn.smul_section_of_tsupport`. -/
theorem exists_global_smul_bump
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {n : ℕ} {U : Set M} (hU : IsOpen U) {x : M} (hxU : x ∈ U)
    {F : Fin n → Π y : M, TangentSpace I y}
    (hF : ∀ i, CMDiff[U] ∞ (T% (F i))) :
    ∃ W : Fin n → Π y : M, TangentSpace I y,
      (∀ i, CMDiff ∞ (T% (W i))) ∧ ∀ᶠ y in 𝓝 x, ∀ i, W i y = F i y := by
  obtain ⟨ψ, -, hψts⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp (hU.mem_nhds hxU)
  refine ⟨fun i => (ψ : M → ℝ) • F i, ?_, ?_⟩
  · intro i
    exact ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (F := E) (V := TangentSpace I)
      (I := I) ψ.contMDiff.contMDiffOn hU hψts (hF i)
  · filter_upwards [ψ.eventuallyEq_one] with y hy
    intro i
    show (ψ y) • (F i y) = F i y
    rw [hy, Pi.one_apply, one_smul]

/-- **A globally smooth field of orthonormal frames near a point.**  For a smooth Riemannian metric
`g` on a smooth manifold `M` and any point `x : M` there is a family of globally `C^∞` vector fields
`W i` which is a `g`-orthonormal frame of `T_yM` for all `y` near `x`. -/
theorem exists_global_ON_frame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) :
    ∃ W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, Work.Diff.GE.SmoothField (I := I) (M := M) (W i)) ∧
      Filter.Eventually (fun y : M => Submission.Diff.IsONFrame g y (fun i => W i y))
        (nhds x) := by
  classical
  -- an analytic manifold is in particular a smooth one
  haveI : IsManifold I ∞ M := inferInstance
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  -- the coordinate frame of the chart at `x`
  let cf : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i y => (trivializationAt E (TangentSpace I) x).symmL ℝ y (b i)
  -- global smooth fields agreeing with the coordinate frame near `x`
  have hZ : ∀ i : Fin (Module.finrank ℝ E),
      ∃ Z : Π y : M, TangentSpace I y,
        CMDiff ∞ (T% Z) ∧ Z =ᶠ[𝓝 x] cf i :=
    fun i => Work.Diff.T.exists_global_eventuallyEq_symmL (I := I) (M := M) x (b i)
      (mem_chart_source H x)
  choose Z hZsm hZeq using hZ
  -- they are linearly independent near `x`
  have hli : ∀ᶠ y in 𝓝 x, LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) => Z i y) := by
    filter_upwards [Filter.eventually_all.mpr hZeq,
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy hyU
    have hcf : LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) => cf i y) :=
      coordFrame_chartSource_linearIndependent (I := I) (M := M) x b hyU
    have hfun : (fun i : Fin (Module.finrank ℝ E) => Z i y) = fun i => cf i y := funext hy
    rw [hfun]
    exact hcf
  -- whose Gram–Schmidt orthonormalisation is smooth and orthonormal near `x`
  have hGssm : ∀ i : Fin (Module.finrank ℝ E),
      ∀ᶠ y in 𝓝 x, CMDiffAt ∞ (T% (gsNorm g Z i)) y :=
    fun i => hli.mono (fun y hy => gsNorm_contMDiffAt_of_linearIndependent g Z hZsm i y hy)
  have hONnear : ∀ᶠ y in 𝓝 x, Submission.Diff.IsONFrame g y (fun i => gsNorm g Z i y) :=
    hli.mono (fun y hy => isONFrame_gsNorm (g := g) (F := Z) hy)
  -- an open neighbourhood of `x` on which this holds
  have hEv : {y : M | (∀ i, CMDiffAt ∞ (T% (gsNorm g Z i)) y) ∧
      Submission.Diff.IsONFrame g y (fun i => gsNorm g Z i y)} ∈ 𝓝 x := by
    rw [← Filter.eventually_iff]
    exact (Filter.eventually_all.mpr hGssm).and hONnear
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hEv
  have hGon : ∀ i, CMDiff[V] ∞ (T% (gsNorm g Z i)) :=
    fun i y hy => ((hVsub hy).1 i).contMDiffWithinAt
  -- cut off by a bump function to make the family global
  obtain ⟨W, hWsm, hWeq⟩ := exists_global_smul_bump (I := I) (M := M) (U := V) (x := x)
    (F := fun i => gsNorm g Z i) hVopen hxV hGon
  refine ⟨W, fun i => hWsm i, ?_⟩
  filter_upwards [hWeq, hONnear] with y hy hyON
  have hfun : (fun i => W i y) = fun i => gsNorm g Z i y := funext hy
  rw [hfun]
  exact hyON

end Work.Diff.GE
