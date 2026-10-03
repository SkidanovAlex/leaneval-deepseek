import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.Deps
import Submission.Lib.Unif2.Work.Parabolic.harmonicOnX_comp_biholomorph

/-!
# Holomorphy is a biholomorphic invariant

The main result of this file is `Work.Parabolic.holomorphicOnX_comp_biholomorph`: if
`Φ : X ≃ₘ⟮mℂ, mℂ⟯ Y` is a biholomorphism of one-dimensional complex manifolds (the plain
notation is Mathlib's smoothness level `∞`) and `f : Y → ℂ` is holomorphic on `s ⊆ Y`, then
`x ↦ f (Φ x)` is holomorphic on `Φ ⁻¹' s`.

The point of the statement is the smoothness level: `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` is *not* the
analytic level `ω`, but for the model with corners `mℂ = modelWithCornersSelf ℂ ℂ` the scalar field
is `ℂ`, so a `C^∞` map in this model has `ℂ`-Fréchet smooth chart representations, which are
holomorphic, hence analytic.  This is the content of
`Work.Parabolic.analyticAt_chart_representation_infty` (proved in the sibling file
`harmonicOnX_comp_biholomorph.lean`).

Concretely, for `x : X` the chart representation of `Φ` at `x`,

`z ↦ (chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z))`,

is analytic at `(chartAt ℂ x) x`; composing it with the chart representation
`w ↦ f ((chartAt ℂ (Φ x)).symm w)` of `f` at `Φ x` (analytic there by hypothesis, since
`x ∈ Φ ⁻¹' s` means `Φ x ∈ s`) gives analyticity of a map which agrees with the chart
representation of `x ↦ f (Φ x)` near `(chartAt ℂ x) x` — the chart `chartAt ℂ (Φ x)` inverts on its
source, which contains `Φ ((chartAt ℂ x).symm z)` for `z` near `(chartAt ℂ x) x` by continuity of
`Φ ∘ (chartAt ℂ x).symm`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.Parabolic

/-- **Holomorphy transports along a biholomorphism, in the smoothness level used by the
library.**  `((⊤ : ℕ∞) : WithTop ℕ∞)` is Mathlib's `∞`, the level of the plain notation
`X ≃ₘ⟮mℂ, mℂ⟯ Y`; since the model `modelWithCornersSelf ℂ ℂ` has scalar field `ℂ`, such a
`Φ` has complex-analytic chart representations (the sibling file
`Submission.Work.Parabolic.harmonicOnX_comp_biholomorph` proves this as
`Work.Parabolic.analyticAt_chart_representation_infty`).  The general-set form is stated, since
callers need `Φ ⁻¹' s`. -/
theorem holomorphicOnX_comp_biholomorph {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y]
    (Φ : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X Y
      ((⊤ : ℕ∞) : WithTop ℕ∞)) {f : Y → ℂ} {s : Set Y} (hf : Submission.HolomorphicOnX f s) :
    Submission.HolomorphicOnX (fun x => f (Φ x)) (Φ ⁻¹' s) := by
  intro x hx
  rw [Submission.HolomorphicOnXAt]
  -- the chart representation of `Φ` at `x` is analytic at `(chartAt ℂ x) x`
  have hF : AnalyticAt ℂ (fun z : ℂ => (chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z)))
      ((chartAt ℂ x) x) :=
    analyticAt_chart_representation_infty (Φ := ⇑Φ) Φ.contMDiff x
  -- the chart representation of `f` at `Φ x` is analytic at `(chartAt ℂ (Φ x)) (Φ x)`
  have hg : AnalyticAt ℂ (fun w : ℂ => f ((chartAt ℂ (Φ x)).symm w))
      ((chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm ((chartAt ℂ x) x)))) := by
    rw [show (chartAt ℂ x).symm ((chartAt ℂ x) x) = x from
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    exact hf (Φ x) hx
  -- composition of the two chart representations
  have hcomp : AnalyticAt ℂ
      (fun z : ℂ => f ((chartAt ℂ (Φ x)).symm ((chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z)))))
      ((chartAt ℂ x) x) :=
    AnalyticAt.comp (E := ℂ) (F := ℂ) (G := ℂ)
      (g := fun w : ℂ => f ((chartAt ℂ (Φ x)).symm w))
      (f := fun z : ℂ => (chartAt ℂ (Φ x)) (Φ ((chartAt ℂ x).symm z)))
      (x := (chartAt ℂ x) x) hg hF
  -- it agrees with the chart representation of `x ↦ f (Φ x)` near `(chartAt ℂ x) x`
  refine hcomp.congr ?_
  have hcont : ContinuousAt (fun z : ℂ => Φ ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) :=
    Φ.continuous.continuousAt.comp
      ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  have hvs : ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      Φ ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (Φ x)).source := by
    have hmem : (chartAt ℂ (Φ x)).source ∈ 𝓝 (Φ ((chartAt ℂ x).symm ((chartAt ℂ x) x))) := by
      rw [show (chartAt ℂ x).symm ((chartAt ℂ x) x) = x from
        (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact (chartAt ℂ (Φ x)).open_source.mem_nhds (mem_chart_source ℂ (Φ x))
    exact hcont.preimage_mem_nhds hmem
  filter_upwards [hvs] with z hz
  rw [(chartAt ℂ (Φ x)).left_inv hz]
  rfl

end Work.Parabolic
