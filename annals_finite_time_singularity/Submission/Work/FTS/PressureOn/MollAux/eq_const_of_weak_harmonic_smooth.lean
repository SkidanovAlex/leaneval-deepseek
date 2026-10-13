import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Auxiliary.integral_inner_laplaceTraceVec_comm
import Submission.Work.FTS.PressureOn.Auxiliary.bounded_harmonic_const
import Submission.Work.FTS.PressureOn.Green.integral_gauss_smul_laplaceTraceVec
import Submission.Work.FTS.BSSwirl.eq_zero_of_forall_inner_test

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

theorem eq_const_of_weak_harmonic_smooth
    (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ∀ n : ℕ, ContDiff ℝ n V)
    (hbdd : ∃ C : ℝ, ∀ x, ‖V x‖ ≤ C)
    (h : ∀ W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ n : ℕ, ContDiff ℝ n W) → HasCompactSupport W →
      ∫ x, inner ℝ (V x) (Work.FTS.PressureOn.laplaceTraceVec W x) = 0) :
    ∃ c : EuclideanSpace ℝ (Fin 3), ∀ x, V x = c := by
  -- `ΔV` (trace of the Hessian, componentwise) is continuous.
  have hcΔV : Continuous (Work.FTS.PressureOn.laplaceTraceVec V) := by
    unfold Work.FTS.PressureOn.laplaceTraceVec
    refine continuous_finsetSum _ (fun i _ => ?_)
    have hψ : ContDiff ℝ 1
        (fun w : Work.FTS.PressureOn.R3 => fderiv ℝ V w (FiniteTimeSingularity.e i)) := by
      fun_prop
    have hcont := hψ.continuous_fderiv (by norm_num)
    exact (ContinuousLinearMap.apply ℝ Work.FTS.PressureOn.R3
      (FiniteTimeSingularity.e i)).continuous.comp hcont
  -- Green's second identity turns the weak harmonicity of `V` into weak harmonicity of `ΔV`.
  have hweak : ∀ W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ n : ℕ, ContDiff ℝ n W) → HasCompactSupport W →
      ∫ x, inner ℝ (Work.FTS.PressureOn.laplaceTraceVec V x) (W x) = 0 := by
    intro W hW hWc
    rw [← Work.FTS.PressureOn.Auxiliary.integral_inner_laplaceTraceVec_comm V W hV hW hWc]
    exact h W hW hWc
  -- Testing against every smooth compactly supported field, `ΔV` must vanish identically.
  have hzero : ∀ x, Work.FTS.PressureOn.laplaceTraceVec V x = 0 :=
    Work.FTS.BSSwirl.eq_zero_of_forall_inner_test hcΔV hweak
  -- Hence each coordinate of `V` is a classical harmonic function.
  have hcoord : ∀ j : Fin 3, ∀ x,
      Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => V y j) x = 0 := by
    intro j x
    have h1 := Work.FTS.PressureOn.Green.IgslvAux.laplaceTraceVec_coord V (hV 2) x j
    rw [hzero x] at h1
    simpa using h1.symm
  obtain ⟨C, hC⟩ := hbdd
  have hbdd_coord : ∀ j : Fin 3, ∃ C' : ℝ,
      ∀ y : EuclideanSpace ℝ (Fin 3), |V y j| ≤ C' := by
    intro j
    refine ⟨C, fun y => ?_⟩
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (V y) j).trans (hC y)
  have hconst_coord : ∀ j : Fin 3, ∃ c : ℝ, ∀ y : EuclideanSpace ℝ (Fin 3), V y j = c := by
    intro j
    refine Work.FTS.PressureOn.Auxiliary.bounded_harmonic_const
      (fun y : EuclideanSpace ℝ (Fin 3) => V y j) (fun n => ?_) (hcoord j) (hbdd_coord j)
    have h := (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp (hV n)
    simpa [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using h
  choose c hc using hconst_coord
  exact ⟨WithLp.toLp 2 (fun j => c j), fun x => by
    apply WithLp.ofLp_injective
    exact funext (fun j => hc j x)⟩

end Work.FTS.PressureOn.MollAux
