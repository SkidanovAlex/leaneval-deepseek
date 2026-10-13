/-
# The Laplacian commutes with a convolution

`Work.FTS.PressureOn.Auxiliary.convolution_laplaceTraceVec_comm`:

  `Δ(ρ ⋆ W) = ρ ⋆ (ΔW)`

for a smooth compactly supported `ρ : ℝ³ → ℝ` and a smooth vector field `W : ℝ³ → ℝ³`, where `Δ`
is `laplaceTraceVec` (the trace of the Hessian in the standard basis) and `⋆` is
`MeasureTheory.convolution ρ · (ContinuousLinearMap.lsmul ℝ ℝ) volume`, i.e.
`(ρ ⋆ G) x = ∫ t, ρ t • G (x - t)`.

## Proof

The auxiliary lemma `hasFDerivAt_convolution_smul` computes the derivative of the convolution with
the derivative falling on `W` (via the parametric integral lemma
`hasFDerivAt_integral_of_dominated_of_fderiv_le`), and is applied once to `W` and once to the
directional derivative field `z ↦ fderiv ℝ W z (e i)`, whose smoothness comes from
`ContDiff.fderiv_right` composed with the evaluation `ContinuousLinearMap.apply ℝ ℝ³ (e i)`.
A finite sum/integral exchange (`MeasureTheory.integral_finsetSum`) finishes the identity.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter
open scoped Topology Pointwise Convolution
open FiniteTimeSingularity

namespace Work.FTS.PressureOn.Auxiliary

/-- **Differentiation under the convolution integral.**  For a smooth compactly supported
`ρ : ℝ³ → ℝ` and a `C¹` map `V : ℝ³ → H` into a normed space `H` over `ℝ`,

  `(d/dx) ∫ t, ρ t • V (x - t) = ∫ t, ρ t • fderiv ℝ V (x - t)`.

The derivative of the convolution therefore falls on the convolved factor; `ρ` only has to be
continuous and compactly supported for the domination of the integrand. -/
private theorem hasFDerivAt_convolution_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : EuclideanSpace ℝ (Fin 3) → H)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (hV : ContDiff ℝ 1 V)
    (x₀ : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (fun y => ∫ t, ρ t • V (y - t))
      (∫ t, ρ t • fderiv ℝ V (x₀ - t)) x₀ := by
  have h3 : ∀ a x, HasFDerivAt (fun y => V (y - a)) (fderiv ℝ V (x - a)) x := fun a x => by
    simpa [Function.comp_def, Pi.sub_apply] using
      (hV.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub (hasFDerivAt_const a x))
  obtain ⟨C₀, hC₀⟩ : ∃ C, ∀ z ∈ ((-tsupport ρ) + closedBall x₀ 1), ‖fderiv ℝ V z‖ ≤ C :=
    ((hρc.isCompact.neg.add (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      (hV.continuous_fderiv one_ne_zero).continuousOn)
  set C := max C₀ 0 with hCdef
  have hC : ∀ z ∈ ((-tsupport ρ) + closedBall x₀ 1), ‖fderiv ℝ V z‖ ≤ C :=
    fun z hz => le_trans (hC₀ z hz) (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_right _ _
  have hbound : ∀ a : EuclideanSpace ℝ (Fin 3), ∀ x ∈ ball x₀ 1,
      ‖ρ a • fderiv ℝ V (x - a)‖ ≤ C * ‖ρ a‖ := by
    intro a x hx
    rw [norm_smul]
    by_cases ha : a ∈ tsupport ρ
    · have hz : x - a ∈ ((-tsupport ρ) + closedBall x₀ 1) := by
        refine Set.mem_add.mpr ⟨-a, ?_, x, ball_subset_closedBall hx, by abel⟩
        exact Set.mem_neg.mpr (by simpa using ha)
      calc ‖ρ a‖ * ‖fderiv ℝ V (x - a)‖ ≤ ‖ρ a‖ * C :=
            mul_le_mul_of_nonneg_left (hC _ hz) (norm_nonneg _)
        _ = C * ‖ρ a‖ := by ring
    · have h0 : ρ a = 0 := by
        by_contra h
        exact ha (subset_tsupport ρ (Function.mem_support.mpr h))
      simp [h0]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
    (bound := fun a => C * ‖ρ a‖)
    (F := fun y t => ρ t • V (y - t)) (F' := fun y t => ρ t • fderiv ℝ V (y - t))
    (ball_mem_nhds x₀ zero_lt_one) ?_ ?_ ?_ (Filter.Eventually.of_forall hbound) ?_ ?_
  · exact Filter.Eventually.of_forall fun y =>
      (hρ.continuous.smul (hV.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact Continuous.integrable_of_hasCompactSupport
      (hρ.continuous.smul (hV.continuous.comp (continuous_const.sub continuous_id)))
      (hρc.smul_right (f' := fun t => V (x₀ - t)))
  · exact ((hρ.continuous.smul
      ((hV.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)))).aestronglyMeasurable
  · exact ((continuous_norm.comp hρ.continuous).integrable_of_hasCompactSupport hρc.norm).const_mul C
  · exact Filter.Eventually.of_forall fun a x _ => (h3 a x).const_smul (ρ a)

theorem convolution_laplaceTraceVec_comm (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hρc : HasCompactSupport ρ) (hW : ∀ n : ℕ, ContDiff ℝ n W) :
    (fun x => MeasureTheory.convolution ρ (Work.FTS.PressureOn.laplaceTraceVec W)
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = Work.FTS.PressureOn.laplaceTraceVec
          (fun x => MeasureTheory.convolution ρ W
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x) := by
  -- the directional derivative fields `z ↦ ∂W(z) e i` are `C¹`
  have hVi : ∀ i : Fin 3,
      ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 3) => fderiv ℝ W z (e i)) := fun i => by
    have h4 : ContDiff ℝ 1 (fderiv ℝ W) := (hW 2).fderiv_right (m := 1) (by norm_num)
    simpa [Function.comp_def] using
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) (e i)).contDiff.comp h4
  -- integrability of the `(ℝ³ →L[ℝ] ℝ³)`-valued integrand, for `integral_apply`
  have hConC : ∀ (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Integrable (fun t => ρ t • fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => fderiv ℝ W z (e i))
        (x - t)) MeasureTheory.volume := fun i x =>
    Continuous.integrable_of_hasCompactSupport
      ((hρ 1).continuous.smul ((hVi i).continuous_fderiv one_ne_zero |>.comp (continuous_const.sub continuous_id)))
      (hρc.smul_right (f' := fun t => fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ W z (e i)) (x - t)))
  -- integrability of the vector-valued integrand, for the sum/integral exchange
  have hCon : ∀ (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Integrable (fun t => ρ t • (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ W z (e i)) (x - t) (e i))) MeasureTheory.volume := fun i x =>
    Continuous.integrable_of_hasCompactSupport
      ((hρ 1).continuous.smul (((hVi i).continuous_fderiv one_ne_zero |>.comp
        (continuous_const.sub continuous_id)).clm_apply continuous_const))
      (hρc.smul_right (f' := fun t => fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ W z (e i)) (x - t) (e i)))
  funext x
  rw [MeasureTheory.convolution_lsmul]
  have hWa : (fun y => MeasureTheory.convolution ρ W
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume y)
      = fun y => ∫ t, ρ t • W (y - t) := by
    funext y
    rw [MeasureTheory.convolution_lsmul]
  rw [hWa]
  -- the `i`-th diagonal second derivative of the convolution
  have key2 : ∀ i : Fin 3,
      fderiv ℝ (fun w => fderiv ℝ (fun y => ∫ t, ρ t • W (y - t)) w (e i)) x (e i)
        = ∫ t, ρ t • (fderiv ℝ (fun z => fderiv ℝ W z (e i)) (x - t) (e i)) := by
    intro i
    have h1 : ∀ w, fderiv ℝ (fun y => ∫ t, ρ t • W (y - t)) w
        = ∫ t, ρ t • fderiv ℝ W (w - t) :=
      fun w => (hasFDerivAt_convolution_smul ρ W hρc (hρ 1) (hW 1) w).fderiv
    have hint1 : ∀ w, Integrable (fun t => ρ t • fderiv ℝ W (w - t)) MeasureTheory.volume := by
      intro w
      exact Continuous.integrable_of_hasCompactSupport
        ((hρ 1).continuous.smul (((hW 1).continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)))
        (hρc.smul_right (f' := fun t => fderiv ℝ W (w - t)))
    have h2 : (fun w => fderiv ℝ (fun y => ∫ t, ρ t • W (y - t)) w (e i))
        = fun w => ∫ t, ρ t • (fderiv ℝ W (w - t) (e i)) := by
      funext w
      rw [h1 w, ContinuousLinearMap.integral_apply (hint1 w)]
      simp only [smul_apply]
    have hf := (hasFDerivAt_convolution_smul ρ (fun z : EuclideanSpace ℝ (Fin 3) => fderiv ℝ W z (e i))
        hρc (hρ 1) (hVi i) x).fderiv
    rw [h2, hf, ContinuousLinearMap.integral_apply (hConC i x)]
    simp only [smul_apply]
  have hR2 : Work.FTS.PressureOn.laplaceTraceVec (fun y => ∫ t, ρ t • W (y - t)) x
      = ∑ i : Fin 3, ∫ t, ρ t • (fderiv ℝ (fun z => fderiv ℝ W z (e i)) (x - t) (e i)) := by
    simp only [Work.FTS.PressureOn.laplaceTraceVec]
    exact Finset.sum_congr rfl fun i _ => key2 i
  have hL2 : ∫ t, ρ t • Work.FTS.PressureOn.laplaceTraceVec W (x - t)
      = ∑ i : Fin 3, ∫ t, ρ t • (fderiv ℝ (fun z => fderiv ℝ W z (e i)) (x - t) (e i)) := by
    have hsplit : (fun t => ρ t • Work.FTS.PressureOn.laplaceTraceVec W (x - t))
        = fun t => ∑ i : Fin 3, ρ t • (fderiv ℝ (fun z => fderiv ℝ W z (e i)) (x - t) (e i)) := by
      funext t
      simp only [Work.FTS.PressureOn.laplaceTraceVec, Finset.smul_sum]
    rw [hsplit, MeasureTheory.integral_finsetSum]
    exact fun i _ => hCon i x
  rw [hR2, hL2]

end Work.FTS.PressureOn.Auxiliary
