import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Submission.Work.SmallBoxBridge.Fourier.T0Form_slot_eq_dirichlet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kinetic energy identity `(2π)⁻³∫_p ‖p‖²‖kinFT u p‖² = Σ_k∫_x (∂_k u)²`

This is the `p`-space form of the one-body kinetic energy in the `kinFT` convention
(`kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy`): the weighted Plancherel identity that identifies the
`(2π)⁻³∫_p ‖p‖²‖·‖²` word with the full-space Dirichlet word
`Σ_k∫_x (∂_k u)²`.  It is the `χ = 1` (no window) member of the bridge's windowed identity
`Work.SmallBoxBridge.Resolve.winModeForm_sq_eq_dirichlet`; the only extra content is the
exchange of the finite coordinate sum `Σ_k` with the `x`-integral, which needs the
integrability of the individual Dirichlet densities.

The identity is stated for `u : ℝ³ → ℝ` smooth of compact support; `u` is complexified to a
Schwartz function `f`, for which the directional derivative `x ↦ ∂_k f(x)` is again Schwartz
(`LineDeriv.lineDerivOp`), hence `L²`, giving the integrability of `x ↦ (∂_k u(x))²`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

theorem kinFT_energy_sum (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiff ℝ (⊤ : ENat) u) (hcs : HasCompactSupport u) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => (u x : ℂ)) p‖ ^ 2
      = ∑ k : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  -- Step 1: the left side is the windowed mode form at the trivial window `χ ≡ 1`.
  have hL : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun x : ℝ³ => (u x : ℂ)) p‖ ^ 2
      = Submission.BoseGases.winModeForm (fun _ : ℝ³ => (1 : ℝ)) (fun r => r ^ 2) u := by
    rw [Submission.BoseGases.winModeForm]
    have hfun : (fun y : ℝ³ => (((1 : ℝ) : ℂ) * ((u y : ℝ) : ℂ)))
        = (fun y : ℝ³ => ((u y : ℝ) : ℂ)) := by
      funext y; simp
    rw [hfun]
  -- Step 2: the bridge's windowed Plancherel identity at `χ ≡ 1`.
  have hB := Work.SmallBoxBridge.Resolve.winModeForm_sq_eq_dirichlet
      (fun _ : ℝ³ => (1 : ℝ)) u contDiff_const hu hcs
  have hone : (fun y : ℝ³ => (1 : ℝ) * u y) = u := by funext y; rw [one_mul]
  rw [hone] at hB
  -- Step 3: exchange the finite coordinate sum with the position integral.
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  -- The complexification of `u`, as a Schwartz function.
  set v : ℝ³ → ℂ := fun y => (u y : ℂ) with hv
  have hv_smooth : ContDiff ℝ (⊤ : ENat) v := by
    simpa only [hv, Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp hu
  have hv_cs : HasCompactSupport v := by
    simpa only [hv, Function.comp_def, Complex.ofRealCLM_apply] using
      hcs.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp)
  let f : SchwartzMap ℝ³ ℂ := hv_cs.toSchwartzMap hv_smooth
  have hf_coe : (f : ℝ³ → ℂ) = v := rfl
  -- The directional derivative `∂_k f` is Schwartz, hence `L²`; so `x ↦ ‖∂_k f x‖²` is
  -- integrable.
  have hInt_complex : ∀ k : Fin 3,
      Integrable (fun x : ℝ³ =>
        ‖fderiv ℝ (f : ℝ³ → ℂ) x (Submission.BoseGases.kcStdBasis k)‖ ^ 2) := by
    intro k
    have hm : MeasureTheory.MemLp
        (LineDeriv.lineDerivOp (Submission.BoseGases.kcStdBasis k) f : ℝ³ → ℂ) 2
        (MeasureTheory.volume : MeasureTheory.Measure ℝ³) :=
      SchwartzMap.memLp _ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ³)
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable] at hm
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hm
  -- The derivative of the complexification is the complexification of the derivative.
  have hfder : ∀ x : ℝ³, fderiv ℝ (f : ℝ³ → ℂ) x
      = Complex.ofRealCLM.comp (fderiv ℝ u x) := by
    intro x
    rw [hf_coe, hv]
    have h := (Complex.ofRealCLM.hasFDerivAt (x := u x)).comp x
      ((hu1.differentiable_one x).hasFDerivAt)
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h.fderiv
  have hInt_real : ∀ k : Fin 3,
      Integrable (fun x : ℝ³ => (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
    intro k
    refine (hInt_complex k).congr ?_
    filter_upwards with x
    rw [hfder x]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    rw [Complex.sq_norm, Complex.normSq_ofReal, pow_two]
  have hC : (∫ x : ℝ³, ∑ k : Fin 3,
        (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = ∑ k : Fin 3, ∫ x : ℝ³,
          (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
    simpa using MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun k (x : ℝ³) => (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)
      (fun k _ => hInt_real k)
  rw [hL, hB]
  exact hC

end Work.BSKinetic
