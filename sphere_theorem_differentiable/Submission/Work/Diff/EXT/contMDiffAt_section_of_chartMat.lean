/-
# From the smoothness of the chart matrix of a metric family to the smoothness of the metric
section

Let `G : ℝ → SMet I M` be a family of smooth Riemannian metrics on a manifold `M`, `x₀ : M` a
chart centre, and suppose that the **chart matrix** of `G` at `x₀`,
`(t, y) ↦ chartMat G x₀ t y` (the matrix of `G t` in the coordinate frame of the chart at `x₀`),
is `C^∞` at `(t₀, (extChartAt I x₀) x₀)` as a function `ℝ × E → MatE`.

The lemma below turns this *matrix valued* smoothness into the smoothness, at `(t₀, x₀)`, of the
section

`p ↦ ⟨p.2, (G p.1).inner p.2⟩`

of the bundle of bilinear forms `fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ`
over `M`, pulled back to `ℝ × M` along `Prod.snd`.  This is the "manifold level" step of the
restart/splice construction of area `EXT` (`Submission/Work/Diff/EXT/twoSided_of_within.lean`).

## Route

Writing the section as a map into a total space over the base `M`, Mathlib's
`contMDiffAt_hom_bundle` reduces its smoothness at `(t₀, x₀)` to the smoothness of

* `p ↦ p.2` (trivial, `contMDiffAt_snd`), and
* `p ↦ inCoordinates E (TangentSpace I) (E →L ℝ) (fun x ↦ TangentSpace I x →L ℝ) x₀ p.2 x₀ p.2
  ((G p.1).inner p.2)`,

the second component being the form read in the hom-bundle trivialisation at `x₀`.  Two delegated
lemmas give what is needed:

* `inCoordinates_tangent_bilin` (`Submission/Work/Diff/EXT/inCoordinates_tangent_bilin.lean`):
  on the chart at `x₀`, the trivialised form has matrix `φ (frameVector x₀ x ·) (frameVector x₀ x ·)`
  in the canonical basis — i.e. exactly the chart matrix;
* `contMDiffAt_matToBilin_chartMat` (`Submission/Work/Diff/EXT/contMDiffAt_matToBilin_chartMat.lean`):
  the reconstruction `matToBilin` of the chart matrix (from `Submission/Work/Diff/EXT/bilinMat.lean`)
  is `C^∞` at `(t₀, x₀)`.

The two functions agree near `(t₀, x₀)` because `p.2` lies in the chart at `x₀` there and
`(extChartAt I x₀).symm ((extChartAt I x₀) p.2) = p.2` on that chart; `congr_of_eventuallyEq`
then transfers the smoothness.
-/

import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.bilinMat
import Submission.Work.Diff.EXT.inCoordinates_tangent_bilin
import Submission.Work.Diff.EXT.contMDiffAt_matToBilin_chartMat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set

namespace Work.Diff.EXT

theorem contMDiffAt_section_of_chartMat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (h : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      (t₀, (extChartAt I x₀) x₀)) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((G p.1).inner p.2))
      (t₀, x₀) := by
  -- `p.2` stays in the chart at `x₀` for `p` near `(t₀, x₀)`
  have hb : ∀ᶠ p : ℝ × M in 𝓝 (t₀, x₀), p.2 ∈ (chartAt H' x₀).source :=
    continuous_snd.continuousAt.preimage_mem_nhds
      (IsOpen.mem_nhds (chartAt H' x₀).open_source (mem_chart_source H' x₀))
  -- read the section in the hom-bundle trivialisation at `x₀`
  refine (contMDiffAt_hom_bundle (𝕜 := ℝ) (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (B := M) (M := ℝ × M) (IB := I) (IM := (𝓘(ℝ, ℝ)).prod I)
    (f := fun p : ℝ × M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
      ((G p.1).inner p.2)) (x₀ := (t₀, x₀))).mpr ?_
  refine ⟨?_, ?_⟩
  · -- the base component is `Prod.snd`
    exact contMDiffAt_snd
  · -- the trivialised component is `C^∞` because it agrees with the reconstruction of the
    -- (smooth) chart matrix
    refine (contMDiffAt_matToBilin_chartMat (I := I) (G := G) h).congr_of_eventuallyEq ?_
    filter_upwards [hb] with p hp
    have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) p.2) = p.2 :=
      (extChartAt I x₀).left_inv (by rwa [extChartAt_source])
    -- the trivialised form is the reconstruction of its matrix in the canonical basis
    rw [inCoordinates_tangent_bilin (x := p.2) hp]
    -- ... and that matrix is the chart matrix
    have hmat : (fun i j => chartMat G x₀ p.1 ((extChartAt I x₀) p.2) i j)
        = (fun i j => (G p.1).inner p.2
            (Submission.Geodesic.frameVector (I := I) x₀ p.2 (bB (E := E) i))
            (Submission.Geodesic.frameVector (I := I) x₀ p.2 (bB (E := E) j))) := by
      funext i j
      simp only [chartMat, chartMatFun]
      rw [hleft]
    rw [hmat]

end Work.Diff.EXT
