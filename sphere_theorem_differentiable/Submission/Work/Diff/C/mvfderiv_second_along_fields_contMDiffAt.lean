import Mathlib
import Submission.Work.Diff.C.fcos_prelude
import Submission.Commons.Geometry.Manifold.VectorField.mvfderivWithin_apply_mlieBracketWithin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

noncomputable section

/-! ## `C²`-ingredients of the Lie-bracket identity for a function smooth only at a point

The four chart reductions below (`contDiffWithinAt_chart_written_c2`,
`mvfderivWithin_pullback_apply_c2`, `mvfderivWithin_second_chart_c2`,
`mvfderivWithin_mlieBracketWithin_chart_c2`) and their combination
`mvfderivWithin_apply_mlieBracketWithin_c2` are verbatim transcriptions of the corresponding
lemmas of `Submission.Work.Diff.GE.mvfderivWithin_apply_mlieBracketWithin_two` (where the
hypothesis `CMDiff[s] ∞ f` is relaxed to `CMDiff[s] (2 : ℕ∞ω) f`), renamed with a `_c2` suffix
and placed in the namespace `Work.Diff.C`.

They are copied rather than imported because that module transitively imports
`Submission.Work.Diff.GE.smp_defs`, whose `Work.Diff.GE.smoothExt_spec` clashes with the
identically named declaration of `Submission.Work.Diff.GE.bianchi_kato_defs` (needed here through
`Submission.Work.Diff.GE.smooth_onframe`).  Only the `∞`-counterparts from the *safe* module
`Submission.Commons.Geometry.Manifold.VectorField.mvfderivWithin_apply_mlieBracketWithin` are
reused (via `open Commons.Geometry.Manifold.VectorField`). -/

section C2Ingredients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## `C²`-versions of the `f`-dependent helpers of
`Commons.Geometry.Manifold.VectorField.mvfderivWithin_apply_mlieBracketWithin`

Each of these is the direct transcription of its `∞`-counterpart with the hypothesis
`CMDiff[s] ∞ f` relaxed to `CMDiff[s] (2 : ℕ∞ω) f`; the vector-field hypotheses stay `C^∞`. -/

/-- The chart-written form of a `C²` function on `M` is `C²` on the model space: for a point
`z ∈ s` in the source of the chart at `x`. -/
lemma contDiffWithinAt_chart_written_c2 {f : M → F} {s : Set M} {x : M}
    (hf : CMDiff[s] (2 : ℕ∞ω) f) {z : M} (hzs : z ∈ s) (hz : z ∈ (chartAt H x).source) :
    ContDiffWithinAt ℝ 2 (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) z) := by
  have h := (contMDiffWithinAt_iff_of_mem_source' (I := I) (I' := 𝓘(ℝ, F))
    (M := M) (M' := F) (x := x) (x' := z) (y := f z) (f := f) (s := s)
    hz (by simp)).1 (hf z hzs)
  simpa [chartAt_self_eq] using h.2

/-- Pointwise form of the chart reduction of the inner first derivative, with `C²`-regularity
of `f`. -/
lemma mvfderivWithin_pullback_apply_c2 {f : M → F} {Yin : Π y : M, TangentSpace I y}
    {s : Set M} {x : M} (hs : UniqueMDiff[s]) (hf : CMDiff[s] (2 : ℕ∞ω) f)
    {y : M} (hys : y ∈ s) (hyΩ : y ∈ (extChartAt I x).source) :
    mvfderivWithin I f s y (Yin y) =
      fderivWithin ℝ (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) y)
        (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yin (range I) ((extChartAt I x) y)) := by
  have hΩ : (extChartAt I x).source ∈ 𝓝 y := (isOpen_extChartAt_source x).mem_nhds hyΩ
  have hys' : y ∈ (chartAt H x).source := by rwa [extChartAt_source] at hyΩ
  -- reduce the set to `s ∩ φ.source`
  rw [← mvfderivWithin_inter (f := f) (s := s) (t := (extChartAt I x).source) (x := y) hΩ]
  -- replace `f` by `f ∘ φ⁻¹ ∘ φ` on this set
  have hfun : f =ᶠ[𝓝[s ∩ (extChartAt I x).source] y]
      ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x)) :=
    Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun z hz => by
      simp only [Function.comp_apply]
      rw [(extChartAt I x).left_inv hz.2])
  rw [mvfderivWithin_congr_eventually_of_mem (g := (f ∘ (extChartAt I x).symm) ∘ (extChartAt I x))
    hfun ⟨hys, hyΩ⟩]
  -- the model function is differentiable within `w`
  have hcont : ContDiffWithinAt ℝ 2 (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) y) :=
    contDiffWithinAt_chart_written_c2 (x := x) (z := y) hf hys hys'
  have hg_diff : MDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (f ∘ (extChartAt I x).symm) ((extChartAt I x) y) :=
    (hcont.contMDiffWithinAt).mdifferentiableWithinAt (by norm_num)
  have hφ_diff : MDiffAt[s ∩ (extChartAt I x).source] (extChartAt I x) y :=
    (mdifferentiableAt_extChartAt hys').mdifferentiableWithinAt
  have hsub : s ∩ (extChartAt I x).source ⊆ (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
    fun z hz => ⟨(extChartAt I x).map_source hz.2, by
      show (extChartAt I x).symm ((extChartAt I x) z) ∈ s
      rw [(extChartAt I x).left_inv hz.2]; exact hz.1⟩
  have hy_s₀ : UniqueMDiffAt[s ∩ (extChartAt I x).source] y :=
    UniqueMDiffWithinAt.inter (hs y hys) hΩ
  rw [mvfderivWithin_comp_apply_vec (f := extChartAt I x) (g := f ∘ (extChartAt I x).symm)
    (s := s ∩ (extChartAt I x).source) (u := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
    (x := y) hg_diff hφ_diff hsub hy_s₀ (Yin y)]
  rw [mvfderivWithin_model_eq_fderivWithin hg_diff]
  congr 1
  rw [mfderivWithin_extChartAt_eq_inverse hyΩ hy_s₀]
  simp only [mpullbackWithin_apply]
  rw [(extChartAt I x).left_inv hyΩ]

/-- Main chart reduction of the outer (second) derivative term, with `C²`-regularity of `f`. -/
lemma mvfderivWithin_second_chart_c2 {f : M → F} {Xv Yin : Π y : M, TangentSpace I y}
    {s : Set M} {x : M} (hs : UniqueMDiff[s]) (hxs : x ∈ s)
    (hxs' : x ∈ closure (interior s))
    (hf : CMDiff[s] (2 : ℕ∞ω) f) (hYin : CMDiff[s] ∞ (T% Yin)) :
    mvfderivWithin I (fun y => mvfderivWithin I f s y (Yin y)) s x (Xv x)
      = fderivWithin ℝ
          (fun z => fderivWithin ℝ (f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) z
            (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yin (range I) z))
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x)
          (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) ((extChartAt I x) x)) := by
  let H : E → F := fun z => fderivWithin ℝ (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) z
      (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yin (range I) z)
  have hInner : (fun y => mvfderivWithin I f s y (Yin y)) =ᶠ[𝓝[s] x]
      (fun y => H ((extChartAt I x) y)) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)] with y hys hyΩ
    exact mvfderivWithin_pullback_apply_c2 (x := x) hs hf hys hyΩ
  rw [mvfderivWithin_congr_eventually_of_mem (g := fun y => H ((extChartAt I x) y)) hInner hxs]
  have hΩ : (extChartAt I x).source ∈ 𝓝 x :=
    (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
  rw [← mvfderivWithin_inter (f := fun y => H ((extChartAt I x) y)) (s := s)
    (t := (extChartAt I x).source) (x := x) hΩ]
  have hw_unique : UniqueDiffOn ℝ ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
    hs.uniqueDiffOn_target_inter x
  have hxs_w : (extChartAt I x) x ∈ (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    show (extChartAt I x).symm ((extChartAt I x) x) ∈ s
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    exact hxs
  have hf'2 : ContDiffWithinAt ℝ 2 (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    contDiffWithinAt_chart_written_c2 (x := x) (z := x) hf hxs (ChartedSpace.mem_chart_source x)
  have hc : DifferentiableWithinAt ℝ
      (fun z => fderivWithin ℝ (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) z)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    (hf'2.fderivWithin_right hw_unique (by norm_num) hxs_w).differentiableWithinAt one_ne_zero
  have hY'diff : DifferentiableWithinAt ℝ
      (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yin (range I) z)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    (contDiffWithinAt_pullback_field hYin hs hxs).differentiableWithinAt one_ne_zero
  have hHdiff' : DifferentiableWithinAt ℝ H
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    hc.clm_apply hY'diff
  have hHdiff : MDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] H
      ((extChartAt I x) x) :=
    DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm (I := 𝓘(ℝ, E))
      (x := (extChartAt I x) x) (by simpa [chartAt_self_eq] using hHdiff')
  have hφdiff : MDiffAt[s ∩ (extChartAt I x).source] (extChartAt I x) x :=
    (mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source x)).mdifferentiableWithinAt
  have hsub : s ∩ (extChartAt I x).source
      ⊆ (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
    fun z hz => ⟨(extChartAt I x).map_source hz.2, by
      show (extChartAt I x).symm ((extChartAt I x) z) ∈ s
      rw [(extChartAt I x).left_inv hz.2]; exact hz.1⟩
  have hx_s₀ : UniqueMDiffAt[s ∩ (extChartAt I x).source] x :=
    UniqueMDiffWithinAt.inter (hs x hxs) hΩ
  change mvfderivWithin I (H ∘ (extChartAt I x)) (s ∩ (extChartAt I x).source) x (Xv x)
      = (fderivWithin ℝ H ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
          ((extChartAt I x) x))
        (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) ((extChartAt I x) x))
  rw [mvfderivWithin_comp_apply_vec (f := extChartAt I x) (g := H)
    (s := s ∩ (extChartAt I x).source) (u := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
    (x := x) hHdiff hφdiff hsub hx_s₀ (Xv x)]
  rw [mvfderivWithin_model_eq_fderivWithin hHdiff]
  suffices h : (mfderiv[s ∩ (extChartAt I x).source] (extChartAt I x) x) (Xv x)
      = mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) ((extChartAt I x) x) by
    rw [h]
    rfl
  rw [mfderivWithin_extChartAt_eq_inverse (mem_extChartAt_source x) hx_s₀,
    mpullbackWithin_apply, (extChartAt I x).left_inv (mem_extChartAt_source x),
    mfderivWithin_range_extChartAt_symm]

/-- Chart reduction of the bracket term, with `C²`-regularity of `f`. -/
lemma mvfderivWithin_mlieBracketWithin_chart_c2 {f : M → F} {Xv Yv : Π y : M, TangentSpace I y}
    {s : Set M} {x : M} (hf : CMDiff[s] (2 : ℕ∞ω) f) (hxs : x ∈ s) :
    mvfderivWithin I f s x (mlieBracketWithin I Xv Yv s x)
      = fderivWithin ℝ (f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x)
          (lieBracketWithin ℝ
            (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z)
            (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yv (range I) z)
            ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x)) := by
  have hf_diff : MDiffAt[s] f x := (hf x hxs).mdifferentiableWithinAt (by norm_num)
  rw [mvfderivWithin_eq_fderivWithin_chart hf_diff]
  have hbracket : mlieBracketWithin I Xv Yv s x
      = lieBracketWithin ℝ
          (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z)
          (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yv (range I) z)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) := by
    rw [VectorField.mlieBracketWithin_apply]
    have h1 : (mfderiv% (extChartAt I x) x).inverse
        = (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) ((extChartAt I x) x))) := by
      rw [mfderiv_extChartAt_self]
      exact ContinuousLinearMap.inverse_id
    rw [h1]
    rfl
  rw [hbracket]
  have hset : ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E)
      =ᶠ[𝓝 ((extChartAt I x) x)] ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s : Set E) := by
    filter_upwards [extChartAt_target_eventuallyEq (I := I) (x := x)] with z hz
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Eq.mp hz.symm h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, Eq.mp hz h1⟩
  have hL : lieBracketWithin ℝ
        (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z)
        (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yv (range I) z)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
      = lieBracketWithin ℝ
        (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z)
        (fun z : E => mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yv (range I) z)
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    lieBracketWithin_congr_set
      (V := fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Xv (range I) z : E))
      (W := fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Yv (range I) z : E)) hset
  rw [fderivWithin_congr_set hset, hL]
  rfl

/-- **`X(Yf) − Y(Xf) = [X,Y]f` needs only `C²` regularity of `f`.**  Same statement as
`Commons.Geometry.Manifold.VectorField.mvfderivWithin_apply_mlieBracketWithin`, but with the
hypothesis `hf : CMDiff[s] (2 : ℕ∞ω) f` instead of `CMDiff[s] ∞ f`; the existing proof only ever uses
`C²`-regularity of `f` (it reduces to the model-space identity `fderivWithin_apply_lieBracketWithin_add`,
whose hypothesis is `ContDiffWithinAt ℝ 2`).  The fields `X`, `Y` keep their `C^∞` hypothesis, so all
field-dependent helpers of that file are reused as is.  Motivation:
`ContMDiffAt I 𝓘(ℝ,ℝ) ∞ u x` does *not* yield `CMDiff[U] ∞ u` for a neighbourhood `U` of `x` (the
index `∞` is pointwise, cf. the note after `contMDiffAt_iff_contMDiffOn_nhds`), only
`CMDiff[U] (2 : ℕ∞ω) u`, which is exactly what this supplies. -/
theorem mvfderivWithin_apply_mlieBracketWithin_c2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : M → F} {X Y : Π x : M, TangentSpace I x} {s : Set M} {x : M}
    (hs : UniqueMDiff[s]) (hxs : x ∈ s) (hxs' : x ∈ closure (interior s))
    (hf : CMDiff[s] (2 : ℕ∞ω) f) (hX : CMDiff[s] ∞ (T% X)) (hY : CMDiff[s] ∞ (T% Y)) :
    mvfderivWithin I (fun y : M => mvfderivWithin I f s y (Y y)) s x (X x) =
      mvfderivWithin I (fun y : M => mvfderivWithin I f s y (X y)) s x (Y x)
        + mvfderivWithin I f s x (VectorField.mlieBracketWithin I X Y s x) := by
  -- hypotheses for the model-space identity
  have hw_unique : UniqueDiffOn ℝ ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
    hs.uniqueDiffOn_target_inter x
  have hp0w : (extChartAt I x) x ∈ (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    show (extChartAt I x).symm ((extChartAt I x) x) ∈ s
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    exact hxs
  have hp0w' : (extChartAt I x) x ∈
      closure (interior ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)) := by
    simpa only [Set.inter_comm] using
      extChartAt_mem_closure_interior hxs' (mem_extChartAt_source x)
  have hf'2 : ContDiffWithinAt ℝ 2 (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    contDiffWithinAt_chart_written_c2 (x := x) (z := x) hf hxs (ChartedSpace.mem_chart_source x)
  have hX'' : DifferentiableWithinAt ℝ
      (fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (range I) z : E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    (contDiffWithinAt_pullback_field hX hs hxs).differentiableWithinAt one_ne_zero
  have hY'' : DifferentiableWithinAt ℝ
      (fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Y (range I) z : E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
    (contDiffWithinAt_pullback_field hY hs hxs).differentiableWithinAt one_ne_zero
  have hmodel := fderivWithin_apply_lieBracketWithin_add
    (f := f ∘ (extChartAt I x).symm)
    (X := fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (range I) z : E))
    (Y := fun z : E => (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Y (range I) z : E))
    (s := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (x := (extChartAt I x) x)
    hX'' hY'' hf'2 hw_unique hp0w' hp0w
  have hLHS := mvfderivWithin_second_chart_c2 (Xv := X) (Yin := Y) hs hxs hxs' hf hY
  have hRHS1 := mvfderivWithin_second_chart_c2 (Xv := Y) (Yin := X) hs hxs hxs' hf hX
  have hRHS2 := mvfderivWithin_mlieBracketWithin_chart_c2 (Xv := X) (Yv := Y) hf hxs
  rw [hLHS, hRHS1, hRHS2]
  exact hmodel
end C2Ingredients

/-! ## Converting the within-set statement into the pointwise one -/

/-- On a set that is a neighbourhood of the basepoint, `mvfderivWithin` agrees with the plain
`mvfderiv`. -/
lemma mvfderivWithin_of_mem_nhds_c
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {g : M → F} {s : Set M} {x : M} (h : s ∈ 𝓝 x) :
    mvfderivWithin I g s x = mvfderiv I g x := by
  simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_mem_nhds h]

/-- `X(Yf) − Y(Xf) = [X,Y]f` at `x`, for `f` only `C^∞` **at the point** `x` (`CMDiffAt ∞ f x`,
Mathlib's weak pointwise notion: no single neighbourhood of `x` on which `f` is `C^∞` need exist)
and *globally* `C^∞` fields `X`, `Y`.  True because only the 2-jet of `f` at `x` is involved.

`hf` is `C^∞` at `x`, hence `C²` on an open neighbourhood `v` of `x`
(`contMDiffAt_iff_contMDiffOn_nhds`, which is available for finite orders).  On `v` the
`C²`-ingredient `mvfderivWithin_apply_mlieBracketWithin_c2` gives the identity for the
within-set derivatives, and on the open set `v` the within-set quantities coincide with the plain
ones at `x`. -/
theorem mvfderiv_second_along_fields_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : M → F} {X Y : Π y : M, TangentSpace I y} {x : M}
    (hf : CMDiffAt ∞ f x) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) :
    mvfderiv I (fun y : M => mvfderiv I f y (Y y)) x (X x) =
      mvfderiv I (fun y : M => mvfderiv I f y (X y)) x (Y x)
        + mvfderiv I f x (VectorField.mlieBracket I X Y x) := by
  -- `f` is `C²` on an open neighbourhood of `x`: pointwise `C^∞` gives `C^2` at `x`, and for a
  -- *finite* order the pointwise notion is a neighbourhood notion.
  haveI : IsManifold I (2 : ℕ∞ω) M :=
    IsManifold.of_le (I := I) (M := M) (m := (2 : ℕ∞ω)) (n := ∞) (by simp)
  obtain ⟨u, hu, hfu⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (I := I) (I' := 𝓘(ℝ, F)) (n := (2 : ℕ∞ω))
      (f := f) (x := x) (by simp)).mp (hf.of_le (by simp))
  obtain ⟨v, hvsub, hvopen, hxv⟩ := _root_.mem_nhds_iff.mp hu
  have hmem : v ∈ 𝓝 x := hvopen.mem_nhds hxv
  have hfv : CMDiff[v] (2 : ℕ∞ω) f := hfu.mono hvsub
  have hXs : CMDiff[v] ∞ (T% X) := (contMDiffOn_univ.mpr hX).mono (subset_univ v)
  have hYs : CMDiff[v] ∞ (T% Y) := (contMDiffOn_univ.mpr hY).mono (subset_univ v)
  have hxs' : x ∈ closure (interior v) := by
    rw [hvopen.interior_eq]
    exact subset_closure hxv
  -- the `C²`-identity on `v`
  have hmain := mvfderivWithin_apply_mlieBracketWithin_c2 (s := v) (f := f) (X := X) (Y := Y)
    (x := x) hvopen.uniqueMDiffOn hxv hxs' hfv hXs hYs
  -- on the open set `v` the within-set derivative of `f` is the plain one
  have hconv : ∀ (B' : Π z : M, TangentSpace I z),
      mvfderivWithin I (fun z => mvfderivWithin I f v z (B' z)) v x
        = mvfderiv I (fun z => mvfderiv I f z (B' z)) x := by
    intro B'
    have hev : (fun z => mvfderiv I f z (B' z)) =ᶠ[𝓝[v] x]
        (fun z => mvfderivWithin I f v z (B' z)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact congrArg (fun L : TangentSpace I z →L[ℝ] F => L (B' z))
        (mvfderivWithin_of_mem_nhds_c (I := I) (M := M) (g := f) (s := v)
          (hvopen.mem_nhds hz)).symm
    have hx' : (fun z => mvfderiv I f z (B' z)) x
        = (fun z => mvfderivWithin I f v z (B' z)) x := by
      simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_mem_nhds hmem]
    have hcongr := Commons.Geometry.Manifold.VectorField.mvfderivWithin_congr_eventually
      (I := I) (s := v) (x := x) hev hx'
    rw [← hcongr,
      mvfderivWithin_of_mem_nhds_c (I := I) (M := M)
        (g := fun z => mvfderiv I f z (B' z)) (s := v) hmem]
  have hbr : mvfderivWithin I f v x (mlieBracketWithin I X Y v x)
      = mvfderiv I f x (mlieBracket I X Y x) := by
    rw [mvfderivWithin_of_mem_nhds_c (I := I) (M := M) (g := f) (s := v) hmem,
      VectorField.mlieBracketWithin_of_mem_nhds (I := I) hmem]
  rw [hconv Y, hconv X, hbr] at hmain
  exact hmain

end

end Work.Diff.C
