/-
# `Work.StabilityFar.Decay.fderiv_timeHolder` — the far-field time-Hölder bound for `Dₓu`

`St4`'s joint `C^{1,α}` estimate has two blocks: the spatial Lipschitz (`FarDerivLipschitz`, proved
separately) and the **time-Hölder** regularity of the spatial derivative `Dₓu(·,t)`, which is this
file.

In the far field `‖x‖ > 2R`, `u(·,t) = BS(ω(·,t))` is differentiable with derivative the Bochner
integral of the kernel derivative (`biotSavart_hasFDerivAt_far`):

  `fderiv ℝ (u · t) x = bsDeriv (ω · t) x = (4π)⁻¹ • ∫ a, (ω a × ·) ∘ kDerivCLM (x - a)`.

The integrand is *linear* in the vorticity, so the difference of the two time slices is the
integral of the difference of the vorticities.  Both slices are supported in `B(0,R)` and their
difference obeys `‖ω a t - ω a τ‖ ≤ H |t - τ|^α` there (`TimeHolderOnBall`), while for `a` off the
ball both slices vanish.  Since `‖x - a‖ ≥ R` on the support ball, the kernel derivative is bounded
by `4/R³` (`norm_kDerivCLM_le`), and the whole integral is at most
`H |t - τ|^α · (4/R³) · vol(B(0,R))`; the prefactor `(4π)⁻¹` and the volume `R³·4π/3` leave the
constant `4H/3`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.StabilityFar.Defs
import Submission.Work.StabilityFar.Decay.biotSavart_fderiv
import Submission.Work.StabilityFar.Decay.biotSavart_sub
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv_const
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

open MeasureTheory

theorem fderiv_timeHolder {α : NNReal} {ω u : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {R M H T : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hH : 0 ≤ H) (hα : 0 < (α : ℝ))
    (hbs : Work.StabilityFar.IsBiotSavartSlice u ω T)
    (hbdd : Work.StabilityFar.SlicesBounded ω M T)
    (hsupp : Work.StabilityFar.SlicesSupported ω R T)
    (hmeas : Work.StabilityFar.SlicesMeasurable ω T)
    (hth : Work.StabilityFar.TimeHolderOnBall (α : ℝ) ω R T H) :
    ∃ At : ℝ, 0 ≤ At ∧ ∀ x : Work.StabilityFar.R3, 2 * R < ‖x‖ →
      ∀ t ∈ Work.StabilityFar.window T, ∀ τ ∈ Work.StabilityFar.window T,
      ‖fderiv ℝ (u · t) x - fderiv ℝ (u · τ) x‖ ≤ At * |t - τ| ^ (α : ℝ) := by
  refine ⟨(4 * Real.pi)⁻¹ * (4 / R ^ 3) * (R ^ 3 * (Real.pi * 4 / 3)) * H, by positivity, ?_⟩
  intro x hx t ht τ hτ
  have hx2 : 2 * R ≤ ‖x‖ := le_of_lt hx
  -- identify the two Fréchet derivatives with the Biot–Savart kernel integrals
  have hfun_t : (u · t) = Work.LWP.biotSavart (ω · t) := funext (fun z => hbs t ht z)
  have hfun_τ : (u · τ) = Work.LWP.biotSavart (ω · τ) := funext (fun z => hbs τ hτ z)
  have hdt := biotSavart_hasFDerivAt_far (ω := (ω · t)) hR hM
    (fun a => hbdd t ht a) (fun a => hsupp t ht a) (hmeas t ht) hx2
  have hdτ := biotSavart_hasFDerivAt_far (ω := (ω · τ)) hR hM
    (fun a => hbdd τ hτ a) (fun a => hsupp τ hτ a) (hmeas τ hτ) hx2
  have e1 : fderiv ℝ (u · t) x = bsDeriv (ω · t) x := by rw [hfun_t]; exact hdt.2.fderiv
  have e2 : fderiv ℝ (u · τ) x = bsDeriv (ω · τ) x := by rw [hfun_τ]; exact hdτ.2.fderiv
  rw [e1, e2]
  -- pointwise identity of the integrands
  have hpt : ∀ a : R3, (crossL ((ω · t) a)).comp (kDerivCLM (x - a))
        - (crossL ((ω · τ) a)).comp (kDerivCLM (x - a))
      = (crossL ((ω · t) a - (ω · τ) a)).comp (kDerivCLM (x - a)) := by
    intro a
    rw [crossL_sub, ContinuousLinearMap.sub_comp]
  -- the difference of the two kernel integrals is the integral of the difference
  have hsub : bsDeriv (ω · t) x - bsDeriv (ω · τ) x
      = (4 * Real.pi)⁻¹ •
        ∫ a, (crossL ((ω · t) a - (ω · τ) a)).comp (kDerivCLM (x - a)) := by
    have e1' : bsDeriv (ω · t) x = (4 * Real.pi)⁻¹ •
        ∫ a, (crossL ((ω · t) a)).comp (kDerivCLM (x - a)) := rfl
    have e2' : bsDeriv (ω · τ) x = (4 * Real.pi)⁻¹ •
        ∫ a, (crossL ((ω · τ) a)).comp (kDerivCLM (x - a)) := rfl
    rw [e1', e2']
    refine ((smul_sub (4 * Real.pi)⁻¹ _ _).symm).trans ?_
    congr 1
    rw [← MeasureTheory.integral_sub hdt.1 hdτ.1]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hsub, norm_smul, Real.norm_of_nonneg (by positivity)]
  -- pointwise bound of the difference integrand
  set C : ℝ := H * |t - τ| ^ (α : ℝ) * (4 / R ^ 3) with hC
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hptb : ∀ a : R3, ‖(crossL ((ω · t) a - (ω · τ) a)).comp (kDerivCLM (x - a))‖
      ≤ C * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) a := by
    intro a
    by_cases ha : a ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem ha, mul_one]
      have haR : ‖a‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using ha
      have hxa : R ≤ ‖x - a‖ := by have := norm_sub_norm_le x a; linarith
      calc ‖(crossL ((ω · t) a - (ω · τ) a)).comp (kDerivCLM (x - a))‖
          ≤ ‖crossL ((ω · t) a - (ω · τ) a)‖ * ‖kDerivCLM (x - a)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖(ω · t) a - (ω · τ) a‖ * (4 / R ^ 3) :=
            mul_le_mul (norm_crossL_le _) (norm_kDerivCLM_le (x - a) R hR hxa)
              (norm_nonneg _) (norm_nonneg _)
        _ ≤ (H * |t - τ| ^ (α : ℝ)) * (4 / R ^ 3) :=
            mul_le_mul_of_nonneg_right (hth a ha t ht τ hτ) (by positivity)
        _ = C := by rw [hC]
    · rw [Set.indicator_of_notMem ha, mul_zero, norm_le_zero_iff]
      have ht0 : (ω · t) a = 0 := by by_contra h; exact ha (hsupp t ht a h)
      have hτ0 : (ω · τ) a = 0 := by by_contra h; exact ha (hsupp τ hτ a h)
      rw [ht0, hτ0, sub_zero, crossL_zero, ContinuousLinearMap.zero_comp]
  have hintdiff : Integrable (fun a : R3 =>
      (crossL ((ω · t) a - (ω · τ) a)).comp (kDerivCLM (x - a))) volume :=
    (hdt.1.sub hdτ.1).congr (Filter.Eventually.of_forall hpt)
  have hbndint : Integrable (fun a : R3 =>
      C * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) a) volume := by
    have hfin : volume (Metric.closedBall (0 : R3) R) ≠ ⊤ :=
      (isCompact_closedBall 0 R).measure_lt_top.ne
    have hind : Integrable ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)))
        (volume : Measure R3) := by
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const hfin (by simp)
    exact hind.const_mul _
  have hvol : ∫ a : R3, (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) a
      = R ^ 3 * (Real.pi * 4 / 3) := by
    rw [MeasureTheory.integral_indicator measurableSet_closedBall,
      MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    exact Work.LWP.BiotSavart.volume_closedBall_real R hR.le
  have h5 : ‖∫ a, (crossL ((ω · t) a - (ω · τ) a)).comp (kDerivCLM (x - a))‖
      ≤ C * (R ^ 3 * (Real.pi * 4 / 3)) := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    have hmono := MeasureTheory.integral_mono_ae hintdiff.norm hbndint
      (Filter.Eventually.of_forall hptb)
    rw [MeasureTheory.integral_const_mul, hvol] at hmono
    exact hmono
  refine (mul_le_mul_of_nonneg_left h5 (by positivity)).trans (le_of_eq ?_)
  rw [hC]; ring

end Work.StabilityFar.Decay
