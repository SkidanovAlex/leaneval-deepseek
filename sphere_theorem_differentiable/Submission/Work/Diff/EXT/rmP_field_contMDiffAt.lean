import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.rmP_eq_sum_rmC4
import Submission.Work.Diff.GE.exists_smooth_section_eq_nhds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `y ↦ rmP g y (A y) (B y) (C y) (D y)` is `C^∞` at `x` for fields `C^∞` at `x`

The frozen pointwise curvature form `Submission.Diff.rmP g y a b c d = ⟪R(a,b)d, c⟫` is the
evaluation of the `(0,4)`-tensor field `Rm` of the metric `g` on four tangent vectors, hence it
depends on the four fields only through their *values*.  Consequently it is `C^∞` at `x` as soon as
the four fields are `C^∞` *at* `x` (Mathlib's weak `ContMDiffAt ∞`, which does **not** imply
smoothness on a neighbourhood of `x`).

The proof does not differentiate the fields `A B C D` at all:

* the frozen coordinate expansion `Work.Diff.GE.rmP_eq_sum_rmC4` writes `rmP` (on the chart at `x`)
  as `∑_{ijkl} α^i β^j γ^k δ^l · rmC4`, where `α^i = (cBasis).coord i ∘ coordFun x A` are the chart
  coordinates of `A` and `rmC4 … i j k l = rmP … (σ_i …) (σ_j …) (σ_k …) (σ_l …)` are the curvature
  components on the *coordinate frame* `σ_m = cFrame x m` of the chart at `x`;
* the coordinate functions of a field smooth at `x` are smooth at `x`
  (`coordFun_contMDiffAt` below, Mathlib's `Trivialization.contMDiffWithinAt_section`), so the
  coefficients are smooth at `x`;
* the coordinate frame is smooth on the whole chart source, i.e. on a neighbourhood of `x`, so each
  `σ_m` agrees near `x` with a globally smooth section (`Work.Diff.GE.exists_smooth_section_eq_nhds`,
  a bump-function cut-off), and `rmP` on four *globally* smooth fields is globally smooth
  (`rmP_fields_smooth` below, the boundary-free version of
  `Work.Diff.Evol.rmP_fields_smooth`/`Work.Diff.GE.contMDiff_rmP_fields`);
* the (pointwise) expansion and the two smoothness statements are combined with
  `ContMDiffAt.sum`/`ContMDiffAt.mul` and `Filter.EventuallyEq` congruence on the chart source.

No hypothesis `[I.Boundaryless]` is needed; in particular no product-manifold (time-dependent) chart
calculus is used.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Smoothness of `rmP` on globally smooth fields (boundary-free) -/

/-- **The curvature of a smooth connection along three globally smooth fields is a smooth
section.**  This is `Work.Diff.GE.contMDiff_curv_fields` / `Work.Diff.Evol.contMDiff_curv_fields`
*without* the hypothesis `[I.Boundaryless]` (which is not used by the proof). -/
theorem contMDiff_curv_fields_ext
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    CMDiff ∞ (T% (fun y : M => curv cov X Y Z y)) := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    have h : (∞ : ℕ∞ω) + 1 = ∞ := by simp
    rw [h]; infer_instance
  have hbr : CMDiff ∞ (T% (mlieBracket I X Y)) := by
    intro y
    exact (hX y).mlieBracket_vectorField (hY y) (by simp)
  have h1 : CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (Y y')) y (X y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
        hZ hY) hX
  have h2 : CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (X y')) y (Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
        hZ hX) hY
  have h3 : CMDiff ∞ (T% (fun y : M => cov Z y (mlieBracket I X Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov hZ hbr
  change CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (Y y')) y (X y)
      - cov (fun y' : M => cov Z y' (X y')) y (Y y) - cov Z y (mlieBracket I X Y y)))
  exact (h1.sub_section h2).sub_section h3

/-- **`rmP` on four globally smooth fields is globally smooth** (boundary-free form of
`Work.Diff.Evol.rmP_fields_smooth` and `Work.Diff.GE.contMDiff_rmP_fields`). -/
theorem rmP_fields_smooth_ext (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M => Submission.Diff.rmP g y (A y) (B y) (C y) (D y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hcov : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  have hfun : (fun y : M => Submission.Diff.rmP g y (A y) (B y) (C y) (D y))
      = fun y : M => inner ℝ (curv (lcOf g) A B D y) (C y) := by
    funext y
    show (g.inner y (rmVec (lcOf g) y (A y) (B y) (D y))) (C y) = _
    rw [Work.Diff.GE.rmVec_eq_curvVec (lcOf g) hcov y (A y) (B y) (D y),
      Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hA hB hD rfl rfl rfl]
    rfl
  rw [hfun]
  exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => curv (lcOf g) A B D y)
    (w := C) (contMDiff_curv_fields_ext (lcOf g) hcov hA hB hD) hC

/-! ## The coordinate function of a field smooth at a point -/

/-- The chart coordinates of a field which is `C^∞` *at* `p` are `C^∞` at `p`.  (Pointwise form of
`Submission.ChartCurv.contMDiffAt_coordFun`, whose hypothesis is global smoothness of the field.) -/
theorem coordFun_contMDiffAt (x₀ : M) {W : Π y : M, TangentSpace I y} {p : M}
    (hW : CMDiffAt ∞ (T% W) p) (hp : p ∈ (chartAt H x₀).source) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (Submission.ChartCurv.coordFun x₀ W) p := by
  have hbase : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hp
  have h1 : ContMDiffWithinAt I 𝓘(ℝ, E) ∞
      (fun q : M => ((trivializationAt E (TangentSpace I) x₀) ⟨q, W q⟩).2)
      (chartAt H x₀).source p :=
    ((Trivialization.contMDiffWithinAt_section (s := W) (chartAt H x₀).source hbase).1
      hW.contMDiffWithinAt)
  refine ((h1.congr ?_ ?_).contMDiffAt ((chartAt H x₀).open_source.mem_nhds hp))
  · intro y hy
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) x₀)
      (by rw [TangentBundle.trivializationAt_baseSet]; exact hy) (W y)
  · exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) x₀) hbase (W p)

/-! ## The main theorem -/

theorem rmP_field_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) {x : M}
    {A B C D : Work.Diff.EXT.TField (I := I) (M := M)}
    (hA : Work.Diff.EXT.SmoothTFieldAt (I := I) (M := M) A x)
    (hB : Work.Diff.EXT.SmoothTFieldAt (I := I) (M := M) B x)
    (hC : Work.Diff.EXT.SmoothTFieldAt (I := I) (M := M) C x)
    (hD : Work.Diff.EXT.SmoothTFieldAt (I := I) (M := M) D x) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y ↦ Submission.Diff.rmP g y (A y) (B y) (C y) (D y)) x := by
  classical
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun y : M ↦ TangentSpace I y) := inferInstance
  -- the chart at `x` is a neighbourhood of `x`
  have hsrc : (chartAt H x).source ∈ 𝓝 x := (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  -- the coordinate frame vectors are smooth on the chart source, hence near `x`
  have hframe : ∀ m : Fin (Module.finrank ℝ E),
      ∀ᶠ y in 𝓝 x, CMDiffAt ∞ (T% (Work.Diff.GE.cFrame (I := I) x m)) y := by
    intro m
    filter_upwards [hsrc] with y hy
    have h := contMDiffAt_frameVector (I := I) x (Work.Diff.GE.cBasis (E := E) m) hy
    simpa only [Work.Diff.GE.cFrame, Submission.Geodesic.frameSection_eq_frameVector] using h
  -- the curvature components on the coordinate frame are smooth at `x`
  have hrmC4 : ∀ i j k l : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y : M => Work.Diff.GE.rmC4 (I := I) (fun _ : ℝ => g) x 0 y i j k l) x := by
    intro i j k l
    obtain ⟨A', hA'sm, -, hA'eq⟩ :=
      Work.Diff.GE.exists_smooth_section_eq_nhds (I := I) (M := M) (x := x)
        (Work.Diff.GE.cFrame (I := I) x i) (hframe i)
    obtain ⟨B', hB'sm, -, hB'eq⟩ :=
      Work.Diff.GE.exists_smooth_section_eq_nhds (I := I) (M := M) (x := x)
        (Work.Diff.GE.cFrame (I := I) x j) (hframe j)
    obtain ⟨C', hC'sm, -, hC'eq⟩ :=
      Work.Diff.GE.exists_smooth_section_eq_nhds (I := I) (M := M) (x := x)
        (Work.Diff.GE.cFrame (I := I) x k) (hframe k)
    obtain ⟨D', hD'sm, -, hD'eq⟩ :=
      Work.Diff.GE.exists_smooth_section_eq_nhds (I := I) (M := M) (x := x)
        (Work.Diff.GE.cFrame (I := I) x l) (hframe l)
    have hmain : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y : M => Submission.Diff.rmP g y (A' y) (B' y) (C' y) (D' y)) x :=
      (rmP_fields_smooth_ext (I := I) (M := M) hLC g hA'sm hB'sm hC'sm hD'sm).contMDiffAt
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards [hA'eq, hB'eq, hC'eq, hD'eq] with y hyA hyB hyC hyD
    simp only [Work.Diff.GE.rmC4, hyA, hyB, hyC, hyD]
  -- the coefficient functions are smooth at `x`
  have hcoef : ∀ (V : Π y : M, TangentSpace I y), CMDiffAt ∞ (T% V) x →
      ∀ m : Fin (Module.finrank ℝ E),
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun y : M => (Work.Diff.GE.cBasis (E := E)).coord m
            (Submission.ChartCurv.coordFun (I := I) x V y)) x := by
    intro V hV m
    have hV' : ContMDiffAt I 𝓘(ℝ, E) ∞ (Submission.ChartCurv.coordFun (I := I) x V) x :=
      coordFun_contMDiffAt (I := I) (M := M) x hV (mem_chart_source H x)
    exact (LinearMap.toContinuousLinearMap
      ((Work.Diff.GE.cBasis (E := E)).coord m)).contMDiffAt.comp x hV'
  -- the whole sum is smooth at `x`
  have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => ∑ i, ∑ j, ∑ k, ∑ l,
        ((Work.Diff.GE.cBasis (E := E)).coord i
            (Submission.ChartCurv.coordFun (I := I) x A y))
          * ((Work.Diff.GE.cBasis (E := E)).coord j
              (Submission.ChartCurv.coordFun (I := I) x B y))
          * ((Work.Diff.GE.cBasis (E := E)).coord k
              (Submission.ChartCurv.coordFun (I := I) x C y))
          * ((Work.Diff.GE.cBasis (E := E)).coord l
              (Submission.ChartCurv.coordFun (I := I) x D y))
          * Work.Diff.GE.rmC4 (I := I) (fun _ : ℝ => g) x 0 y i j k l) x := by
    refine ContMDiffAt.sum (fun i _ ↦ ContMDiffAt.sum (fun j _ ↦ ContMDiffAt.sum (fun k _ ↦
      ContMDiffAt.sum (fun l _ ↦ ?_))))
    exact ((((hcoef A hA i).mul (hcoef B hB j)).mul (hcoef C hC k)).mul
      (hcoef D hD l)).mul (hrmC4 i j k l)
  -- identify with `rmP` on the chart source
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with y hy
  exact Work.Diff.GE.rmP_eq_sum_rmC4 (I := I) (M := M) hLC (fun _ : ℝ => g) x 0 hy

end Work.Diff.EXT
