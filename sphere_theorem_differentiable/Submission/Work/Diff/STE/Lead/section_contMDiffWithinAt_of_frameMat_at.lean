/-
# From the smoothness of the frame matrix to the smoothness of the section

If the *frame matrix* of a time-dependent family of bilinear forms on `M`,
`(t, x) ↦ frameMat y x (γ t x)` (the matrix of `γ t x` in the coordinate frame of the chart at
`y`, `Work.Diff.EXT.frameMat`), is jointly `C^∞` on `s ⊆ ℝ × M` at `(t₀, x₀)`, where
`x₀ ∈ (chartAt H y).source`, then the section `p ↦ ⟨p.2, γ p.1 p.2⟩` of the bundle of bilinear forms
over `M`, pulled back to `ℝ × M`, is jointly `C^∞` on `s` at `(t₀, x₀)`.

This is the within-set version of `Work.Diff.EXT.formFamSection_contMDiffAt_of_frameMat`, with the
frame centre `y` allowed to differ from the point `x₀` at which smoothness is claimed; the only
extra input is that `x₀` lies in the chart at `y` (so that the trivialisation at `y` covers `x₀`).
It is the local smoothness input of the DeTurck bootstrap: one reads a chart matrix of the metric
family and must produce the section itself.

## Route

`Bundle.Trivialization.contMDiffWithinAt_iff`, applied to the trivialisation `e` of the bundle of
bilinear forms *at `y`* (whose base set is the chart at `y`, hence contains `x₀` by `hy`), reduces
the smoothness of the section to the smoothness of `p ↦ p.2` (trivial, `contMDiffWithinAt_snd`) and
of the trivialised component

`p ↦ (e ⟨p.2, γ p.1 p.2⟩).2 = inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ) (fun x ↦ TangentSpace I x →L[ℝ] ℝ) y p.2 y p.2 (γ p.1 p.2)`,

the last identity being `hom_trivializationAt_apply` (it holds definitionally).  On the chart at `y`
that trivialised form is the reconstruction `matToBilin` of its matrix in the coordinate frame of
the chart at `y` (`inCoordinates_tangent_bilin`), i.e. exactly `matToBilin (frameMat y p.2 (γ p.1 p.2))`,
which is smooth by the hypothesis since `matToBilin` is linear and continuous, hence `C^∞`
(`ContinuousLinearMap.contDiff`).  The passage between the two descriptions of the trivialised
component is `ContMDiffWithinAt.congr_of_eventuallyEq`, using that `p.2` stays in the chart at `y`
near `(t₀, x₀)` (continuity of `Prod.snd` and `hy`).
-/
import Mathlib
import Submission.Work.Diff.STE.Lead.JointSmoothKit
import Submission.Work.Diff.STE.C2.formFamJoint_pullMetBilin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Filter Set Bundle

namespace Work.Diff.STE.Lead

theorem section_contMDiffWithinAt_of_frameMat_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (γ : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {s : Set (ℝ × M)} {t₀ : ℝ} {x₀ y : M} (hp₀ : (t₀, x₀) ∈ s)
    (hy : x₀ ∈ (chartAt H y).source)
    (hframe : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun p : ℝ × M => Work.Diff.EXT.frameMat (I := I) y p.2 (γ p.1 p.2)) s (t₀, x₀)) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2 (γ p.1 p.2))
      s (t₀, x₀) := by
  -- the trivialisation of the bundle of bilinear forms at `y`
  let e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) y
  haveI : MemTrivializationAtlas e := by dsimp only [e]; infer_instance
  -- its base set is the chart at `y`, which contains `x₀` by `hy`
  have hmem : x₀ ∈ e.baseSet := by
    dsimp only [e]
    rw [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet]
    exact ⟨hy, hy, by simp⟩
  have hsrc : (⟨x₀, γ t₀ x₀⟩ : Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) ∈ e.source := by
    rw [Bundle.Trivialization.mem_source]; exact hmem
  -- `p.2` stays in the chart at `y` for `p` near `(t₀, x₀)` (hence also along `s`)
  have hb' : ∀ᶠ p : ℝ × M in 𝓝 (t₀, x₀), p.2 ∈ (chartAt H y).source :=
    continuous_snd.continuousAt.preimage_mem_nhds
      (IsOpen.mem_nhds (s := (chartAt H y).source) (x := x₀) (chartAt H y).open_source hy)
  have hb : ∀ᶠ p : ℝ × M in 𝓝[s] (t₀, x₀), p.2 ∈ (chartAt H y).source :=
    hb'.filter_mono nhdsWithin_le_nhds
  -- the reconstruction of the (smooth) frame matrix as a bilinear form is smooth on `s`
  have hmat : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun p : ℝ × M => Work.Diff.EXT.matToBilin (E := E)
        (Work.Diff.EXT.frameMat (I := I) y p.2 (γ p.1 p.2))) s (t₀, x₀) := by
    have hlift : ContMDiff (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E)))
        (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
        (fun A : Work.Diff.EXT.MatE (E := E) => Work.Diff.EXT.matToBilin (E := E) A) :=
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Work.Diff.EXT.MatE (E := E))
        (F := (E →L[ℝ] E →L[ℝ] ℝ)) (n := (⊤ : ℕ∞))
        (Work.Diff.EXT.matToBilin (E := E))).contMDiff
    exact (hlift.contMDiffAt.contMDiffWithinAt).comp (t₀, x₀) hframe (fun p _ => Set.mem_univ _)
  -- read the section in the trivialisation at `y`
  refine (Bundle.Trivialization.contMDiffWithinAt_iff (e := e) (f := fun p : ℝ × M =>
    Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
      (γ p.1 p.2)) hsrc).mpr ?_
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  -- the trivialised component agrees with the reconstruction of the frame matrix
  refine hmat.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hb] with p hp'
    dsimp only [e]
    rw [hom_trivializationAt_apply]
    exact Work.Diff.EXT.inCoordinates_tangent_bilin (I := I) (x₀ := y) (x := p.2) hp'
      (φ := γ p.1 p.2)
  · dsimp only [e]
    rw [hom_trivializationAt_apply]
    exact Work.Diff.EXT.inCoordinates_tangent_bilin (I := I) (x₀ := y) (x := x₀) hy
      (φ := γ t₀ x₀)

end Work.Diff.STE.Lead
