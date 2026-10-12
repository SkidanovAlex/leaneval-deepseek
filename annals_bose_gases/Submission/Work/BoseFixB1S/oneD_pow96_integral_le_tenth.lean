import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Submission.Work.BoseFixB1S.conv3Small_48_polydisc_lower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.oneD_pow96_integral_le_tenth`

`∫_ℝ (ζ s)^96 ds ≤ 1/10`, where `ζ = Submission.BoseGases.zeta1d` is the 1D cosine
profile `cos (π ·)` on `|·| ≤ 1/2`, zero outside.

The true value is `C(96,48)/2^96 = ∫_{Icc (-1/2) (1/2)} cos^96 (π s) ds ≈ 0.0812`, so
`1/10` has comfortable margin (the sibling `oneD_pow96_integral_le_conv48` proves the
weaker `≤ 1/7` with the crude Gaussian `exp (-192 s²)`; that route cannot reach `1/10`
because `√(π/192) ≈ 0.1279 > 1/10`).

Proof (this file).  The sharp pointwise Gaussian majorant at the *optimal* exponent
`48 π² = 96 · π²/2` costs only the classical second-order inequality
`log (cos x) ≤ -x²/2` (`|x| ≤ π/2`), which is proved here by calculus (the auxiliary
function `log (cos ·) + ·²/2` is antitone on `[0, π/2]`, its derivative being
`t - tan t ≤ 0`).  Hence

* `cos_pow96_le_exp_neg`: `cos x ^ 96 ≤ exp (-(48) · x²)` for `|x| ≤ π/2`, and
* `cos_pi_pow96_le_exp`: `cos (π s) ^ 96 ≤ exp (-(48 π²) s²)` for `|s| ≤ 1/2`;

integrating against `integral_gaussian` gives `∫_ℝ exp (-(48 π²) s²) = √(1/(48 π))`,
which is `≤ 1/10` because `π ≥ 25/12` (only `π > 3` is used).

Note on the endpoint: at `|x| = π/2` Lean's convention `Real.log 0 = 0` makes the log
inequality *false*, so the log estimate is stated for `|x| < π/2` and the endpoint is
handled separately (`cos (π s) = 0` there, and `0 ^ 96 = 0 ≤ exp`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false

/-- The classical inequality `log (cos y) ≤ -y²/2` for `0 ≤ y < π/2`.

The auxiliary function `f t = log (cos t) + t²/2` has `f 0 = 0` and derivative
`-tan t + t ≤ 0` on `(0, π/2)` (since `t ≤ tan t`), so it is antitone on `[0, y]`. -/
lemma log_cos_le_neg_sq_div_two_of_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hylt : y < Real.pi / 2) :
    Real.log (Real.cos y) ≤ -(y ^ 2) / 2 := by
  have hcont : ContinuousOn (fun t : ℝ => Real.log (Real.cos t) + t ^ 2 / 2) (Set.Icc 0 y) :=
    (Real.continuous_cos.continuousOn.log (fun t ht => ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [ht.1], by linarith [ht.2, hylt]⟩))).add
      (((continuous_id.pow 2).div_const 2).continuousOn)
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => Real.log (Real.cos t) + t ^ 2 / 2)
      (interior (Set.Icc 0 y)) := by
    rw [interior_Icc]
    intro t ht
    have hcos : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2, hylt]⟩)
    have h1 : HasDerivAt (fun z : ℝ => Real.log (Real.cos z)) ((-Real.sin t) / Real.cos t) t :=
      (Real.hasDerivAt_cos t).log hcos
    have h2 : HasDerivAt (fun z : ℝ => z ^ 2 / 2) t t := by
      have h : HasDerivAt (fun z : ℝ => z ^ 2 / 2) (2 * t ^ (2 - 1) / 2) t :=
        (hasDerivAt_pow 2 t).div_const 2
      have hv : 2 * t ^ (2 - 1) / 2 = t := by norm_num
      rw [hv] at h
      exact h
    exact (h1.add h2).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ interior (Set.Icc 0 y),
      deriv (fun z : ℝ => Real.log (Real.cos z) + z ^ 2 / 2) t ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have hcospos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2, hylt]⟩
    have htan : t * Real.cos t < Real.sin t := by
      have h := Real.lt_tan ht.1 (by linarith [ht.2, hylt])
      rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcospos] at h
      linarith
    have h1 : HasDerivAt (fun z : ℝ => Real.log (Real.cos z)) ((-Real.sin t) / Real.cos t) t :=
      (Real.hasDerivAt_cos t).log (ne_of_gt hcospos)
    have h2 : HasDerivAt (fun z : ℝ => z ^ 2 / 2) t t := by
      have h : HasDerivAt (fun z : ℝ => z ^ 2 / 2) (2 * t ^ (2 - 1) / 2) t :=
        (hasDerivAt_pow 2 t).div_const 2
      have hv : 2 * t ^ (2 - 1) / 2 = t := by norm_num
      rw [hv] at h
      exact h
    have hfull : HasDerivAt (fun z : ℝ => Real.log (Real.cos z) + z ^ 2 / 2)
        (-Real.sin t / Real.cos t + t) t := h1.add h2
    have key : t ≤ Real.sin t / Real.cos t := by
      rw [le_div_iff₀ hcospos]
      linarith
    rw [hfull.deriv, neg_div]
    linarith [key]
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc 0 y) hcont hdiff hderiv
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 y := ⟨le_rfl, hy0⟩
  have hymem : y ∈ Set.Icc 0 y := ⟨hy0, le_rfl⟩
  have hle := hanti h0mem hymem hy0
  have hf0 : Real.log (Real.cos 0) + (0 : ℝ) ^ 2 / 2 = 0 := by simp
  linarith

/-- `log (cos x) ≤ -x²/2` for `|x| < π/2` (the even extension of the previous lemma).

The strict hypothesis is needed: at `|x| = π/2` one has `cos x = 0` and Lean's
convention `Real.log 0 = 0` makes the inequality false. -/
lemma log_cos_le_neg_sq_div_two {x : ℝ} (hx : |x| < Real.pi / 2) :
    Real.log (Real.cos x) ≤ -(x ^ 2) / 2 := by
  rcases le_or_gt 0 x with hx0 | hx0
  · exact log_cos_le_neg_sq_div_two_of_nonneg hx0 (abs_lt.mp hx).2
  · have h : Real.log (Real.cos (-x)) ≤ -((-x) ^ 2) / 2 :=
      log_cos_le_neg_sq_div_two_of_nonneg (by linarith) (by linarith [(abs_lt.mp hx).1])
    rw [Real.cos_neg] at h
    convert h using 1
    ring

/-- `cos x ^ 96 ≤ exp (-(48) · x²)` for `|x| ≤ π/2` (optimal Gaussian majorant).

At `|x| = π/2` the left side vanishes, which handles the endpoint where the log estimate
of `log_cos_le_neg_sq_div_two` does not apply. -/
lemma cos_pow96_le_exp_neg (x : ℝ) (hx : |x| ≤ Real.pi / 2) :
    Real.cos x ^ 96 ≤ Real.exp (-(48 : ℝ) * x ^ 2) := by
  have hcosnn : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp hx).1], (abs_le.mp hx).2⟩
  rcases eq_or_lt_of_le hcosnn with hzero | hpos
  · rw [← hzero, zero_pow (by norm_num)]
    exact Real.exp_nonneg _
  · have hxlt : |x| < Real.pi / 2 := by
      rcases lt_or_eq_of_le hx with h | h
      · exact h
      · exfalso
        have hc : Real.cos |x| = 0 := by rw [h, Real.cos_pi_div_two]
        rw [Real.cos_abs] at hc
        exact (ne_of_gt hpos) hc
    have hlog := log_cos_le_neg_sq_div_two hxlt
    calc Real.cos x ^ 96 = Real.exp ((96 : ℕ) * Real.log (Real.cos x)) := by
          rw [Real.exp_nat_mul, Real.exp_log hpos]
      _ ≤ Real.exp (-(48 : ℝ) * x ^ 2) := by
          apply Real.exp_le_exp.mpr
          have hcast : ((96 : ℕ) : ℝ) = 96 := by norm_num
          rw [hcast]
          linarith

/-- `cos (π s) ^ 96 ≤ exp (-(48 π²) s²)` for `|s| ≤ 1/2`. -/
lemma cos_pi_pow96_le_exp (s : ℝ) (hs : |s| ≤ 1 / 2) :
    Real.cos (Real.pi * s) ^ 96 ≤ Real.exp (-(48 * Real.pi ^ 2) * s ^ 2) := by
  have hx : |Real.pi * s| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, hs]
  calc Real.cos (Real.pi * s) ^ 96 ≤ Real.exp (-(48 : ℝ) * (Real.pi * s) ^ 2) :=
        cos_pow96_le_exp_neg _ hx
    _ = Real.exp (-(48 * Real.pi ^ 2) * s ^ 2) := by
        congr 1
        ring

/-- `∫_ℝ exp (-(48 π²) s²) ds = √(1/(48 π)) ≤ 1/10`. -/
lemma exp_neg_48pi2_sq_integral_le_tenth :
    (∫ s : ℝ, Real.exp (-(48 * Real.pi ^ 2) * s ^ 2)) ≤ 1 / 10 := by
  have hb : (0 : ℝ) < 48 * Real.pi ^ 2 := by positivity
  rw [integral_gaussian (48 * Real.pi ^ 2)]
  rw [Real.sqrt_le_left (by norm_num)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_gt_three]

theorem oneD_pow96_integral_le_tenth :
    (∫ s : ℝ, Submission.BoseGases.zeta1d s ^ 96) ≤ 1 / 10 := by
  rw [oneD_pow96_integral_eq_Icc]
  have hb : (0 : ℝ) < 48 * Real.pi ^ 2 := by positivity
  have hint : Integrable (fun s : ℝ => Real.exp (-(48 * Real.pi ^ 2) * s ^ 2)) volume :=
    integrable_exp_neg_mul_sq hb
  calc ∫ s in Set.Icc (-(1 / 2) : ℝ) (1 / 2), Real.cos (Real.pi * s) ^ 96
      ≤ ∫ s in Set.Icc (-(1 / 2) : ℝ) (1 / 2), Real.exp (-(48 * Real.pi ^ 2) * s ^ 2) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact (by fun_prop : Continuous fun s : ℝ => Real.cos (Real.pi * s) ^ 96).integrableOn_Icc
        · exact hint.integrableOn
        · exact measurableSet_Icc
        · intro s hs
          exact cos_pi_pow96_le_exp s (abs_le.mpr ⟨hs.1, hs.2⟩)
    _ ≤ ∫ s : ℝ, Real.exp (-(48 * Real.pi ^ 2) * s ^ 2) :=
        MeasureTheory.setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun s => Real.exp_nonneg _)
    _ ≤ 1 / 10 := exp_neg_48pi2_sq_integral_le_tenth

end Work.BoseFixB1S
