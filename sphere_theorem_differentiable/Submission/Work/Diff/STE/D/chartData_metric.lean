import Mathlib
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.Diff.STE.D.ChartData_Rstar
import Submission.Work.Diff.EXT.inCoordinates_tangent_bilin
import Submission.Work.Diff.EXT.bilinMat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart matrix of a global smooth metric is smooth

`Work.Diff.STE.D.ChartData h` is the smoothness of the chart matrix of a section `h` of the bundle
of bilinear forms on the chart target of every chart of `M`.  The construction
`Work.Diff.STE.D.smetOf` goes the other way: it turns a section with `ChartData` into a global
smooth metric.  This file proves the *converse*, which is needed to feed a *given* smooth metric
`g : Submission.Diff.SMet I M` into the Galerkin scheme of layer D:

`Work.Diff.STE.D.chartData_metric : ChartData (g.inner)`.

The proof is a three-line principle made explicit:

* if `e` is the trivialization of the bundle of bilinear forms at a fixed chart centre `x₀`, whose
  base set is the chart source `(chartAt H x₀).source`, then the trivialized form of the section
  `x ↦ ⟨x, g.inner x⟩` is `x ↦ (e ⟨x, g.inner x⟩).2`, and it is `C^∞` on the source by
  `contMDiffAt_totalSpace` (the section is smooth) together with
  `ContMDiffWithinAt.change_section_trivialization` (the trivialization at the *moving* point `x`
  supplied by `contMDiffAt_totalSpace` is replaced by the fixed one at `x₀`; this is exactly where
  the base-set membership of the chart source is used);
* by `inCoordinates_tangent_bilin`, the trivialized form is `matToBilin` applied to the chart matrix
  of `g.inner` in the frame of the chart at `x₀`;
* composing with the chart inverse `(extChartAt I x₀).symm` and reading off the matrix entries
  (which are `matToBilin M (bB i) (bB j) = M i j`) gives the smoothness of the chart matrix on the
  chart target.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

theorem chartData_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (g : Submission.Diff.SMet I M) :
    Work.Diff.STE.D.ChartData (I := I) (M := M) (g.inner) := by
  intro x₀
  -- the trivialization of the bundle of bilinear forms at the chart centre `x₀`
  set e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x₀ with he_def
  -- its base set is the chart source
  have hbase : e.baseSet = (chartAt H x₀).source := by
    rw [he_def, hom_trivializationAt_baseSet, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    simp
  -- hence the section lies in its source over the chart source
  have hmem : ∀ x ∈ (chartAt H x₀).source,
      (⟨x, g.inner x⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) ∈ e.source := by
    intro x hx
    rw [Trivialization.mem_source, hbase]
    exact hx
  -- the trivialized section `x ↦ (e ⟨x, g.inner x⟩).2` is `C^∞` on the chart source
  have hΨ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) (⊤ : ℕ∞)
      (fun x : M => (e ⟨x, g.inner x⟩).2) (chartAt H x₀).source := by
    intro x hx
    have hf : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
        (fun y : M => (⟨y, g.inner y⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)))
        (chartAt H x₀).source x :=
      (g.contMDiff x).contMDiffWithinAt.mono (subset_univ _)
    obtain ⟨hp, hfx⟩ := contMDiffWithinAt_totalSpace.mp hf
    have he1 : (⟨x, g.inner x⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))
        ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x).source := by
      rw [Trivialization.mem_source]
      exact mem_baseSet_trivializationAt _ _ x
    exact ContMDiffWithinAt.change_section_trivialization hp hfx he1 (hmem x hx)
  -- read off the matrix entries of the chart matrix
  rw [contDiffOn_pi]
  intro i
  rw [contDiffOn_pi]
  intro j y hy
  have hχ : ContMDiffWithinAt 𝓘(ℝ, E) I (⊤ : ℕ∞) (extChartAt I x₀).symm
      (extChartAt I x₀).target y := contMDiffWithinAt_extChartAt_symm_target x₀ hy
  have hcomp : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) (⊤ : ℕ∞)
      ((fun x : M => (e ⟨x, g.inner x⟩).2) ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀).target y :=
    ContMDiffWithinAt.comp y (hΨ _ (by
        have h1 := (extChartAt I x₀).map_target' hy
        rwa [extChartAt_source] at h1)) hχ (fun z hz => by
      have h1 := (extChartAt I x₀).map_target' hz
      rwa [extChartAt_source] at h1)
  have hcd : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      ((fun x : M => (e ⟨x, g.inner x⟩).2) ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀).target y := hcomp.contDiffWithinAt
  have h1 : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun z => ((fun x : M => (e ⟨x, g.inner x⟩).2) ∘ (extChartAt I x₀).symm) z
        (Work.Diff.EXT.bB (E := E) i))
      (extChartAt I x₀).target y :=
    hcd.clm_apply contDiffWithinAt_const
  have h5 : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun z => ((fun x : M => (e ⟨x, g.inner x⟩).2) ∘ (extChartAt I x₀).symm) z
        (Work.Diff.EXT.bB (E := E) i) (Work.Diff.EXT.bB (E := E) j))
      (extChartAt I x₀).target y :=
    h1.clm_apply contDiffWithinAt_const
  refine h5.congr_of_mem ?_ hy
  intro z hz
  have hzsrc : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
    have h1 := (extChartAt I x₀).map_target' hz
    rwa [extChartAt_source] at h1
  have hkey := Work.Diff.EXT.inCoordinates_tangent_bilin (I := I) (x₀ := x₀)
    (x := (extChartAt I x₀).symm z) hzsrc (φ := g.inner ((extChartAt I x₀).symm z))
  have hval : (e ⟨(extChartAt I x₀).symm z, g.inner ((extChartAt I x₀).symm z)⟩).2
      = Work.Diff.EXT.matToBilin
        (fun i j => g.inner ((extChartAt I x₀).symm z)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm z)
            (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm z)
            (Work.Diff.EXT.bB (E := E) j))) := by
    rw [he_def]
    exact hkey
  rw [Function.comp_apply, hval, Work.Diff.EXT.matToBilin_apply_basis]

end Work.Diff.STE.D
