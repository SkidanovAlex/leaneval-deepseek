import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.BoseB1Cube.sq_intervalIntegral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.shiftDiff_sq_pointwise`

The **pointwise** (in `x`) finite-difference bound for a `C²` function
`χ : ℝ³ → ℝ` and a direction `z`:

    (χ (x + z/2) − χ (x − z/2))² ≤ ‖z‖² ∫_{−1/2}^{1/2} ‖fderiv ℝ χ (x + s • z)‖² ds .

It is the exact pointwise companion of the integrated Poincaré inequality
`Work.BoseB1Cube.ShiftBound` (`∫ y, (f y − f (y + w))² ≤ ‖w‖² ∫ y, ‖fderiv ℝ f y‖²`),
and it is proved the same way, without any integration in `x`:

* the fundamental theorem of calculus along the segment `s ↦ x + s • z`
  (`intervalIntegral.integral_eq_sub_of_hasDerivAt`, the derivative of `χ` along the segment
  being `s ↦ (fderiv ℝ χ (x + s • z)) z` by the chain rule for `HasFDerivAt`/`HasDerivAt`);
* Cauchy–Schwarz in `s` on the interval `(−1/2, 1/2)` of length `1`
  (`Work.BoseB1Cube.sq_intervalIntegral_le`, Jensen for `x ↦ x²`) — note that the length factor
  is exactly `1/2 − (−1/2) = 1`;
* the operator-norm bound `‖(fderiv ℝ χ y) z‖ ≤ ‖fderiv ℝ χ y‖ ‖z‖`
  (`ContinuousLinearMap.le_opNorm`), squared and integrated.

Since `χ` is `C²`, all integrands occurring are continuous on the compact interval, hence
interval integrable, and no a.e./integrability side conditions arise.
-/

namespace Work.BoseB1Cube

open MeasureTheory intervalIntegral

theorem shiftDiff_sq_pointwise {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (h2 : ContDiff ℝ 2 χ)
    (x z : EuclideanSpace ℝ (Fin 3)) :
    (χ (x + (1 / 2 : ℝ) • z) - χ (x - (1 / 2 : ℝ) • z)) ^ 2
      ≤ ‖z‖ ^ 2 * ∫ s in (-(1 / 2) : ℝ)..(1 / 2), (‖fderiv ℝ χ (x + s • z)‖) ^ 2 := by
  -- `χ` is differentiable everywhere, so the chain rule applies at every `s`.
  have hχd : ∀ y : EuclideanSpace ℝ (Fin 3), DifferentiableAt ℝ χ y :=
    fun y => (h2.contDiffAt (x := y)).differentiableAt (by norm_num)
  -- the derivative of `s ↦ χ (x + s • z)` is `s ↦ (fderiv ℝ χ (x + s • z)) z`
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => χ (x + s • z)) ((fderiv ℝ χ (x + s • z)) z) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x + s • z) z s := by
      simpa using ((hasDerivAt_id s).smul_const z).const_add x
    exact ((hχd (x + s • z)).hasFDerivAt).comp_hasDerivAt s h1
  -- continuity of the integrands, from `χ` being `C²`
  have hfderiv_cont : Continuous (fun y : EuclideanSpace ℝ (Fin 3) => fderiv ℝ χ y) :=
    h2.continuous_fderiv (by norm_num)
  have hint1 : Continuous (fun s : ℝ => (fderiv ℝ χ (x + s • z)) z) :=
    (hfderiv_cont.comp (by continuity)).clm_apply continuous_const
  have hint2 : Continuous (fun s : ℝ => ((fderiv ℝ χ (x + s • z)) z) ^ 2) := hint1.pow 2
  have hint3 : Continuous (fun s : ℝ => ‖fderiv ℝ χ (x + s • z)‖ ^ 2) :=
    ((hfderiv_cont.comp (by continuity)).norm).pow 2
  -- step 1: the fundamental theorem of calculus along the segment
  have hFTC : (∫ s in (-(1 / 2) : ℝ)..(1 / 2), (fderiv ℝ χ (x + s • z)) z)
      = χ (x + (1 / 2 : ℝ) • z) - χ (x - (1 / 2 : ℝ) • z) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (-(1/2) : ℝ)) (b := (1/2 : ℝ))
      (f := fun s : ℝ => χ (x + s • z))
      (f' := fun s : ℝ => (fderiv ℝ χ (x + s • z)) z)
      (fun s _ => hderiv s) (hint1.intervalIntegrable (-(1/2)) (1/2))
    have harg : x + (-(1/2) : ℝ) • z = x - (1/2 : ℝ) • z := by
      rw [neg_smul, sub_eq_add_neg]
    rw [h]
    exact congrArg (fun t => χ (x + (1/2 : ℝ) • z) - χ t) harg
  -- step 2: Cauchy–Schwarz in `s` (the interval has length exactly `1`)
  have hCS : (∫ s in (-(1 / 2) : ℝ)..(1 / 2), (fderiv ℝ χ (x + s • z)) z) ^ 2
      ≤ ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ((fderiv ℝ χ (x + s • z)) z) ^ 2 := by
    have h := sq_intervalIntegral_le (fun s : ℝ => (fderiv ℝ χ (x + s • z)) z)
      (by norm_num : (-(1/2) : ℝ) ≤ 1/2) (hint2.intervalIntegrable (-(1/2)) (1/2))
    rwa [show (1/2 : ℝ) - (-(1/2)) = 1 by norm_num, one_mul] at h
  -- step 3: the square of the derivative is bounded by `‖z‖² ‖fderiv‖²`, integrated
  have hstep : (∫ s in (-(1 / 2) : ℝ)..(1 / 2), ((fderiv ℝ χ (x + s • z)) z) ^ 2)
      ≤ ‖z‖ ^ 2 * ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ‖fderiv ℝ χ (x + s • z)‖ ^ 2 := by
    have hmono : (∫ s in (-(1/2) : ℝ)..(1/2), ((fderiv ℝ χ (x + s • z)) z) ^ 2)
        ≤ ∫ s in (-(1/2) : ℝ)..(1/2), ‖z‖ ^ 2 * ‖fderiv ℝ χ (x + s • z)‖ ^ 2 :=
      intervalIntegral.integral_mono_on (by norm_num) (hint2.intervalIntegrable (-(1/2)) (1/2))
        ((hint3.const_mul (‖z‖ ^ 2)).intervalIntegrable (-(1/2)) (1/2)) (fun s _ => by
          have hb : |(fderiv ℝ χ (x + s • z)) z| ≤ ‖fderiv ℝ χ (x + s • z)‖ * ‖z‖ := by
            have := ContinuousLinearMap.le_opNorm (fderiv ℝ χ (x + s • z)) z
            simpa [Real.norm_eq_abs] using this
          obtain ⟨hlo, hhi⟩ := abs_le.mp hb
          calc ((fderiv ℝ χ (x + s • z)) z) ^ 2
              ≤ (‖fderiv ℝ χ (x + s • z)‖ * ‖z‖) ^ 2 := sq_le_sq' hlo hhi
            _ = ‖z‖ ^ 2 * ‖fderiv ℝ χ (x + s • z)‖ ^ 2 := by ring)
    rwa [intervalIntegral.integral_const_mul] at hmono
  calc (χ (x + (1/2 : ℝ) • z) - χ (x - (1/2 : ℝ) • z)) ^ 2
      = (∫ s in (-(1/2) : ℝ)..(1/2), (fderiv ℝ χ (x + s • z)) z) ^ 2 := by rw [hFTC]
    _ ≤ ∫ s in (-(1/2) : ℝ)..(1/2), ((fderiv ℝ χ (x + s • z)) z) ^ 2 := hCS
    _ ≤ ‖z‖ ^ 2 * ∫ s in (-(1/2) : ℝ)..(1/2), ‖fderiv ℝ χ (x + s • z)‖ ^ 2 := hstep

end Work.BoseB1Cube
