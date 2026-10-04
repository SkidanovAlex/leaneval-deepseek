/-
# From the smoothness of the frame matrix of a family of forms to the smoothness of the section

Let `γ : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ` be a time dependent
family of bilinear forms on the tangent bundle of `M`, `x₀ : M` a chart centre, and suppose that
the **frame matrix** of `γ` in the coordinate frame of the chart at `x₀`,
`(t, x) ↦ frameMat x₀ x (γ t x)`, is `C^∞` at `(τ, x₀)` as a function `ℝ × M → MatE`.

The lemma below turns this *matrix valued* smoothness into the smoothness at `(τ, x₀)` of the
section

`p ↦ ⟨p.2, γ p.1 p.2⟩`

of the bundle of bilinear forms `fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ`
over `M`, pulled back to `ℝ × M` along `Prod.snd` (`formFamSection`, the total space
representation used by `FormFamJoint` in `Submission/Work/Diff/EXT/glueDefs.lean`).

## Route

Mathlib's `contMDiffAt_hom_bundle` reduces the smoothness of the section at `(τ, x₀)` to the
smoothness of

* `p ↦ p.2` (trivial, `contMDiffAt_snd`), and
* `p ↦ inCoordinates E (TangentSpace I) (E →L ℝ) (fun x ↦ TangentSpace I x →L ℝ) x₀ p.2 x₀ p.2
  (γ p.1 p.2)`,

the second component being the form read in the hom-bundle trivialisation at `x₀`.  On the chart
at `x₀` the trivialised form *is* the reconstruction `matToBilin` of its matrix
(`inCoordinates_tangent_bilin`, `Submission/Work/Diff/EXT/inCoordinates_tangent_bilin.lean`), and
that matrix is by definition the frame matrix `frameMat x₀ p.2 (γ p.1 p.2)`.  Since `matToBilin`
is linear and continuous, hence `C^∞`, the composition with the (smooth, by hypothesis) frame
matrix is smooth, and `congr_of_eventuallyEq` transfers this to the trivialised component, valid
on the chart at `x₀`.

The only technicality is that synthesising the algebraic structure of the continuous-linear-map
space `E →L[ℝ] E →L[ℝ] ℝ` is expensive, so `synthInstance.maxHeartbeats` is raised here (as in
`bilinMat.lean`).
-/

import Mathlib
import Submission.Work.Diff.EXT.glueDefs
import Submission.Work.Diff.EXT.bilinMat
import Submission.Work.Diff.EXT.inCoordinates_tangent_bilin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set

namespace Work.Diff.EXT

theorem formFamSection_contMDiffAt_of_frameMat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    {γ : Work.Diff.EXT.FormFam (I := I) (M := M)} {τ : ℝ} {x₀ : M}
    (h : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
        (fun p : ℝ × M => Work.Diff.EXT.frameMat (I := I) x₀ p.2 (γ p.1 p.2)) (τ, x₀)) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (Work.Diff.EXT.formFamSection (I := I) γ) (τ, x₀) := by
  -- `p.2` stays in the chart at `x₀` for `p` near `(τ, x₀)`
  have hb : ∀ᶠ p : ℝ × M in 𝓝 (τ, x₀), p.2 ∈ (chartAt H' x₀).source :=
    continuous_snd.continuousAt.preimage_mem_nhds
      (IsOpen.mem_nhds (chartAt H' x₀).open_source (mem_chart_source H' x₀))
  -- the reconstruction of the (smooth) frame matrix is smooth
  have hmat : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun p : ℝ × M =>
        Work.Diff.EXT.matToBilin (Work.Diff.EXT.frameMat (I := I) x₀ p.2 (γ p.1 p.2)))
      (τ, x₀) := by
    have hclm : ContMDiffAt (𝓘(ℝ, Work.Diff.EXT.MatE (E := E)))
        (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
        (⇑(Work.Diff.EXT.matToBilin (E := E)))
        (Work.Diff.EXT.frameMat (I := I) x₀ x₀ (γ τ x₀)) :=
      ((ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Work.Diff.EXT.MatE (E := E))
        (F := (E →L[ℝ] E →L[ℝ] ℝ)) (n := (⊤ : ℕ∞))
        Work.Diff.EXT.matToBilin).contMDiff).contMDiffAt
    exact ContMDiffAt.comp _ hclm h
  -- read the section in the hom-bundle trivialisation at `x₀`
  refine (contMDiffAt_hom_bundle (𝕜 := ℝ) (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (B := M) (M := ℝ × M) (IB := I) (IM := (𝓘(ℝ, ℝ)).prod I)
    (f := fun p : ℝ × M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
      (γ p.1 p.2)) (x₀ := (τ, x₀))).mpr ?_
  refine ⟨?_, ?_⟩
  · -- the base component is `Prod.snd`
    exact contMDiffAt_snd
  · -- the trivialised component agrees with the reconstruction of the frame matrix
    refine hmat.congr_of_eventuallyEq ?_
    filter_upwards [hb] with p hp
    rw [Work.Diff.EXT.inCoordinates_tangent_bilin (x := p.2) hp]
    rfl

end Work.Diff.EXT
