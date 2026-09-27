import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Projection.Defs
import Submission.Work.Projection.mfderiv_chartAt_decomp

/-!
# Height functions on an embedded surface, and their critical points

We fix a smooth map `e : M → ℝ⁵` (in practice an embedding with injective derivative) and study the
family of *height functions* `h_v = x ↦ ⟪v, e x⟫`.  This file contains the elementary calculus:
smoothness of `h_v`, its manifold derivative, and the description of its critical points.

The point of the height family is that its members are the "generic" functions used to produce a
Morse function on a compact surface.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff RealInnerProductSpace
open Work.Drive.Morse

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

/-- The continuous linear functional `y ↦ ⟪v, y⟫` on `ℝ⁵`, written as an explicit finite sum so
that it is a plain `→L[ℝ]` (rather than the `→L⋆` produced by `innerSL`). -/
noncomputable def innerCLM (v : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 5) →L[ℝ] ℝ :=
  ∑ i, (v i) • (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) i)

lemma innerCLM_apply (v y : EuclideanSpace ℝ (Fin 5)) : innerCLM v y = ⟪v, y⟫ := by
  rw [show innerCLM v y = ∑ i, v i * y i from rfl, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The height function of `e` in direction `v`. -/
noncomputable def heightFun (e : M → EuclideanSpace ℝ (Fin 5)) (v : EuclideanSpace ℝ (Fin 5)) :
    M → ℝ :=
  fun x => innerCLM v (e x)

lemma heightFun_apply (e : M → EuclideanSpace ℝ (Fin 5)) (v : EuclideanSpace ℝ (Fin 5)) (x : M) :
    heightFun e v x = ⟪v, e x⟫ := innerCLM_apply v (e x)

/-- Height functions of a smooth map are smooth. -/
theorem contMDiff_heightFun (e : M → EuclideanSpace ℝ (Fin 5)) (v : EuclideanSpace ℝ (Fin 5))
    (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (heightFun e v) := by
  show ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ ((innerCLM v) ∘ e)
  exact ContinuousLinearMap.contMDiff (innerCLM v) |>.comp he

/-- The manifold derivative of a height function. -/
theorem mfderiv_heightFun (e : M → EuclideanSpace ℝ (Fin 5)) (v : EuclideanSpace ℝ (Fin 5))
    (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e) (x : M) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (heightFun e v) x
      = (innerCLM v).comp (mfderiv (𝓡 2) (𝓡 5) e x) := by
  show mfderiv (𝓡 2) 𝓘(ℝ, ℝ) ((innerCLM v) ∘ e) x = _
  rw [mfderiv_comp x (f := e) (g := innerCLM v) (ContinuousLinearMap.mdifferentiableAt _)
    ((he x).mdifferentiableAt (by simp))]
  have hm : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 5))) 𝓘(ℝ, ℝ) (innerCLM v) (e x) = innerCLM v :=
    ContinuousLinearMap.mfderiv_eq _
  rw [hm]
  rfl

/-- `x` is a critical point of the height function `h_v` iff the composite
`u ↦ ⟪v, De_x u⟫` is the zero functional. -/
theorem isCritical_heightFun_iff (e : M → EuclideanSpace ℝ (Fin 5)) (v : EuclideanSpace ℝ (Fin 5))
    (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e) (x : M) :
    IsCritical (heightFun e v) x ↔
      (innerCLM v).comp (mfderiv (𝓡 2) (𝓡 5) e x) = 0 := by
  rw [IsCritical, mfderiv_heightFun e v he x]
  exact Iff.rfl

/-- The chart representation of a height function: `y ↦ ⟪v, F y⟫` where `F` is the chart
representation of `e`. -/
noncomputable def chartHeight (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (v : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun y => innerCLM v (F y)

lemma chartHeight_apply (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (v : EuclideanSpace ℝ (Fin 5)) (y : EuclideanSpace ℝ (Fin 2)) :
    chartHeight F v y = ⟪v, F y⟫ := innerCLM_apply v (F y)

/-- The derivative of a chart representation of a height function. -/
theorem fderiv_chartHeight (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (v : EuclideanSpace ℝ (Fin 5)) (y : EuclideanSpace ℝ (Fin 2)) (hF : DifferentiableAt ℝ F y) :
    fderiv ℝ (chartHeight F v) y = (innerCLM v).comp (fderiv ℝ F y) := by
  show fderiv ℝ ((innerCLM v) ∘ F) y = _
  rw [fderiv_comp y (ContinuousLinearMap.differentiableAt _) hF]
  rw [ContinuousLinearMap.fderiv]

end Work.Drive.N2
