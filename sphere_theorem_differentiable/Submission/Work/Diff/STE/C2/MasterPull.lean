/-
# Layer C2 (DeTurck pull-back): the first variation of the pull-back of a metric family

`Work.Diff.STE.C2.hasDerivWithinAt_pullMetBilin_flow` is the identity

`d/ds [ (A s).inner (φ s x) (dφ_s u) (dφ_s v) ]`
  `= dA t (φ t x) (dφ_t u) (dφ_t v) + ⟨∇_{dφ_t u} (Y t), dφ_t v⟩_{A t}`
    `+ ⟨dφ_t u, ∇_{dφ_t v}(Y t)⟩_{A t}`

(the metric version of the DeTurck/pull-back computation: `∂_s(φ_s^* A_s) = φ_s^*(∂_s A_s + L_{Y_s}A_s)`).

It is the sum of the two halves that were established separately:

* `Work.Diff.STE.C2.hasDerivWithinAt_metDiff_flow` — the variation of the *difference* family
  `A s - A t` (whose only effect is the derivative `dA` in the metric index);
* `Work.Diff.STE.C2.fixedMet_flow_Ico` — the first variation of the pull-back of the *frozen*
  metric `A t` along the flow (the Lie-derivative term, written with `lcOf (A t)`).

The time set is an interval `Ico a b` throughout: the frozen-metric half is *false* for a general
time set `J` (a set with isolated accumulation points, e.g. `{0} ∪ {1/n}`, admits families whose
within-derivative is `Y` at every time but whose Jacobian evolution is not the flow of `Y`).

No hypothesis (`hvar`) about the raw identification `TangentSpace I z ≃ E` is needed — that was the
false formulation of the earlier attempt.
-/
import Mathlib
import Submission.Work.Diff.STE.C2.Defs
import Submission.Work.Diff.STE.C2.fixedMet_flow_Ico
import Submission.Work.Diff.STE.C2.hasDerivWithinAt_metDiff_flow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.C2

theorem hasDerivWithinAt_pullMetBilin_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)) (Y : ℝ → Π x : M, TangentSpace I x)
    (A : ℝ → Submission.Diff.SMet I M) {a b : ℝ} (hab : a < b)
    (dA : ℝ → (x : M) → TangentSpace I x → TangentSpace I x → ℝ)
    (hφ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (Ico a b ×ˢ Set.univ))
    (hY : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I M)) (Ico a b ×ˢ Set.univ))
    (hA : Submission.Diff.JointSmooth A (Ico a b))
    (hvel : ∀ t ∈ Ico a b, ∀ x : M,
      HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I (fun s ↦ φ s x) (Ico a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (φ t x))))
    (hAderiv : ∀ t ∈ Ico a b, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun s ↦ (A s).inner x u v) (dA t x u v) (Ico a b) t) :
    ∀ t ∈ Ico a b, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ ↦ Work.Diff.STE.C2.pullMetBilin (φ s) (A s) x u v)
        (dA t (φ t x) (mfderiv I I (φ t) x u) (mfderiv I I (φ t) x v)
          + ((A t).inner (φ t x)
              ((Submission.Diff.lcOf (A t)) (Y t) (φ t x) (mfderiv I I (φ t) x u))
              (mfderiv I I (φ t) x v)
            + (A t).inner (φ t x) (mfderiv I I (φ t) x u)
              ((Submission.Diff.lcOf (A t)) (Y t) (φ t x) (mfderiv I I (φ t) x v))))
        (Ico a b) t := by
  intro t ht x u v
  have h2 := Work.Diff.STE.C2.hasDerivWithinAt_metDiff_flow (I := I) (M := M)
    A (Ico a b) hA φ Y dA hφ hvel hAderiv t ht x u v
  have h1 := Work.Diff.STE.C2.fixedMet_flow_Ico (I := I) (M := M)
    hLC (A t) φ Y hab hφ hY hvel t ht x u v
  have hsum := h2.add h1
  refine hsum.congr_of_eventuallyEq ?_ ?_
  · filter_upwards with s
    simp only [Work.Diff.STE.C2.pullMetBilin_apply, Pi.add_apply, Pi.sub_apply]
    ring
  · simp only [Work.Diff.STE.C2.pullMetBilin_apply, Pi.add_apply, Pi.sub_apply]
    ring

end Work.Diff.STE.C2
