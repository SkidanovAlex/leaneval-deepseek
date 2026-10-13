/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted Hardy inequality for `HarOp`, proved from scratch

`HarOp β f z = z^{-β} ∫_0^z s^{β-1} f s ds` (`GbarSetup.lean`), `w z = (1+z)²/z²`.  This module
proves the weighted Hardy inequality

  `∫_0^∞ w(z)² (HarOp β f z)² dz ≤ (100/β²) ∫_0^∞ w(z)² (f z)² dz`   (`β ≥ 5`)

together with the integrability of the left-hand side.  It is the analytic input of the
`Ḡ`-estimate of §'Elliptic Regularity Estimates' of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)

(the `α`-independence of the constant of the estimate is exactly the factor `1/β²` here, which
cancels the explicit `1/α²` in front of `Ḡ`).

## Proof

The classical weighted Cauchy–Schwarz / Tonelli pair, with the *sharp* exponent on the source:
`s^{β-1} f s = s^{(β-1)/2} · s^{(β-1)/2} f s` and Cauchy–Schwarz on `(0,z]` give the pointwise
bound `(HarOp β f z)² ≤ (1/β) z^{-β} ∫_0^z s^{β-1} (f s)² ds` (`gbar_HarOp_pointwise_sq`),
whose constant `1/β` is the sharp Hardy rate.  Multiplying by `w(z)²` and integrating, Tonelli
(`HarOp_lintegral_swap`) turns the double integral into
`(1/β) ∫_0^∞ s^{β-1} (f s)² (∫_s^∞ w(z)² z^{-β} dz) ds`, and since `w` is decreasing the inner
integral is at most `w(s)² s^{1-β}/(β-1)` (`w_tail_lintegral_bound`).  The factors cancel, leaving
`1/(β(β-1)) ≤ 100/β²`, and the real-integral form follows
(`Work.FTS.EllipticEst.Blocks.integral_le_of_lintegral_le`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.HarOp_lintegral_swap
import Submission.Work.FTS.EllipticEst.w_tail_lintegral_bound
import Submission.Work.FTS.EllipticEst.Blocks.integral_le_of_lintegral_le
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## Cauchy–Schwarz for Lebesgue integrals -/

/-- Cauchy–Schwarz for the Lebesgue integral, in the form needed below. -/
theorem gbar_cs_integral {s : Set ℝ} {a b : ℝ → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict s))
    (hb : AEStronglyMeasurable b (volume.restrict s))
    (ha2 : IntegrableOn (fun x => a x ^ 2) s) (hb2 : IntegrableOn (fun x => b x ^ 2) s) :
    (∫ x in s, a x * b x) ^ 2 ≤ (∫ x in s, a x ^ 2) * (∫ x in s, b x ^ 2) :=
  Work.Spaces.cs_integral ((memLp_two_iff_integrable_sq ha).mpr ha2)
    ((memLp_two_iff_integrable_sq hb).mpr hb2)

/-! ## The pointwise weighted Cauchy–Schwarz bound -/

/-- **Pointwise (weighted Cauchy–Schwarz) step of the Hardy inequality.**  For `β > 1`, `z > 0`
and `f` with `f²` integrable on `(0,∞)`,
`(HarOp β f z)² ≤ (1/β) z^{-β} ∫_{(0,z]} s^{β-1} (f s)²`, in `ℝ≥0∞`. -/
theorem gbar_HarOp_pointwise_sq (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    ENNReal.ofReal ((HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
        ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
  have hβ0 : 0 < β := one_pos.trans hβ
  have hb1 : 0 ≤ β - 1 := by linarith
  have hb1' : 0 < β - 1 := by linarith
  have hb2 : 0 ≤ (β - 1) / 2 := by linarith
  have hb2' : 0 < (β - 1) / 2 := by linarith
  have hz0 : 0 ≤ z := hz.le
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  set I : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s with hI
  set J2 : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s ^ 2 with hJ2
  have hf2 : Integrable (fun s : ℝ => f s ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    hf.mono_set Set.Ioc_subset_Ioi_self
  have hM : Integrable (fun s : ℝ => z ^ (β - 1) + z ^ (β - 1) * f s ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (integrable_const _).add (hf2.const_mul _)
  have hφ : AEStronglyMeasurable (absF f) (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    change AEStronglyMeasurable (fun x : ℝ => Real.sqrt (f x ^ 2)) _
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hf2.aestronglyMeasurable
  have hcont : AEStronglyMeasurable (fun s : ℝ => s ^ ((β - 1) / 2))
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (Real.continuous_rpow_const hb2).aestronglyMeasurable
  have ha : Integrable (fun s : ℝ => (s ^ ((β - 1) / 2)) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine Integrable.mono' hM ((Real.continuous_rpow_const hb2).pow 2).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (x ^ ((β - 1) / 2))), sq_rpow hx0,
      show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    calc x ^ (β - 1) ≤ z ^ (β - 1) := Real.rpow_le_rpow hx0.le hx.2 hb1
      _ ≤ z ^ (β - 1) + z ^ (β - 1) * f x ^ 2 :=
          le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hz0 _) (sq_nonneg _))
  have hb : Integrable (fun s : ℝ => (s ^ ((β - 1) / 2) * absF f s) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine Integrable.mono' hM ((hcont.mul hφ).pow 2) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (x ^ ((β - 1) / 2) * absF f x)),
      mul_pow, sq_rpow hx0, absF_sq,
      show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    calc x ^ (β - 1) * f x ^ 2 ≤ z ^ (β - 1) * f x ^ 2 :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx0.le hx.2 hb1) (sq_nonneg _)
      _ ≤ z ^ (β - 1) + z ^ (β - 1) * f x ^ 2 :=
          le_add_of_nonneg_left (Real.rpow_nonneg hz0 _)
  -- ## Cauchy–Schwarz
  have hcs := gbar_cs_integral (s := Set.Ioc (0 : ℝ) z)
    (a := fun s : ℝ => s ^ ((β - 1) / 2)) (b := fun s : ℝ => s ^ ((β - 1) / 2) * absF f s)
    hcont (hcont.mul hφ) ha hb
  have hA : (∫ s in Set.Ioc (0 : ℝ) z, s ^ ((β - 1) / 2) * (s ^ ((β - 1) / 2) * absF f s))
      = ∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z,
          s ^ ((β - 1) / 2) * (s ^ ((β - 1) / 2) * absF f s))
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) * absF f s :=
      setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
        have h2 : x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2) = x ^ (β - 1) := by
          rw [← Real.rpow_add hx.1]; congr 1; ring
        rw [show x ^ ((β - 1) / 2) * (x ^ ((β - 1) / 2) * absF f x)
            = (x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2)) * absF f x from by ring, h2])
    rw [h1, ← intervalIntegral.integral_of_le hz0]
  have hB : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2)) ^ 2) = z ^ β / β := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2)) ^ 2)
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      rcases eq_or_lt_of_le hx.1.le with h | h
      · rw [← h, Real.zero_rpow (ne_of_gt hb2'), Real.zero_rpow (ne_of_gt hb1')]
        norm_num
      · rw [sq_rpow h, show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    rw [h1, ← intervalIntegral.integral_of_le hz0]
    exact intervalIntegral_rpow_sub_one hβ0
  have hC : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2) * absF f s) ^ 2) = J2 := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2) * absF f s) ^ 2)
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) * f s ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      rw [mul_pow, sq_rpow hx.1, absF_sq,
        show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    rw [h1, ← intervalIntegral.integral_of_le hz0]
  have hCS : (∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s) ^ 2 ≤ (z ^ β / β) * J2 := by
    have h := hcs
    rw [hA, hB, hC] at h
    exact h
  -- ## The integral itself
  have hJle : |I| ≤ ∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s := by
    have h1 := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := fun s : ℝ => s ^ (β - 1) * f s) hz0
    rw [← hI, Real.norm_eq_abs, intervalIntegral.integral_of_le hz0] at h1
    refine h1.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_of_le hz0]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le (β - 1)),
      absF_eq_abs]
  have hI2 : I ^ 2 ≤ (z ^ β / β) * J2 := by
    have h2 : |I| ^ 2 ≤ (∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg I) hJle 2
    rw [sq_abs] at h2
    linarith [hCS, h2]
  -- ## The a.e. bridge to the Lebesgue integral
  have hgI : IntegrableOn (fun s : ℝ => s ^ (β - 1) * f s ^ 2) (Set.Ioc 0 z) :=
    hb.congr ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun x hx => by
        show (x ^ ((β - 1) / 2) * absF f x) ^ 2 = x ^ (β - 1) * f x ^ 2
        rw [mul_pow, sq_rpow hx.1, absF_sq,
          show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]))
  have hbridge : ENNReal.ofReal J2
      = ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
    rw [hJ2, intervalIntegral.integral_of_le hz0]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgI
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun x hx =>
          mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg (f x))))
  -- ## Final assembly
  have huz : z ^ (-β) * z ^ β = 1 := by
    rw [← Real.rpow_add hz, show -β + β = 0 from by ring, Real.rpow_zero]
  have hmain : (HarOp β f z) ^ 2 = (z ^ (-β)) ^ 2 * I ^ 2 := by
    rw [HarOp, ← hI]
    ring
  have hkey : (z ^ (-β)) ^ 2 * ((z ^ β / β) * J2) = (1 / β) * (z ^ (-β) * J2) := by
    have h1 : (z ^ (-β)) ^ 2 * z ^ β = z ^ (-β) := by
      have h2 : (z ^ (-β)) ^ 2 * z ^ β = z ^ (-β) * (z ^ (-β) * z ^ β) := by ring
      rw [h2, huz, mul_one]
    have h3 : (z ^ (-β)) ^ 2 * ((z ^ β / β) * J2)
        = ((z ^ (-β)) ^ 2 * z ^ β) * (J2 / β) := by ring
    rw [h3, h1]
    ring
  calc ENNReal.ofReal ((HarOp β f z) ^ 2)
      = ENNReal.ofReal ((z ^ (-β)) ^ 2 * I ^ 2) := by rw [hmain]
    _ ≤ ENNReal.ofReal ((z ^ (-β)) ^ 2 * ((z ^ β / β) * J2)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hI2 (sq_nonneg _)
    _ = ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) * ENNReal.ofReal J2 := by
        rw [hkey, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (Real.rpow_nonneg hz0 (-β))]
        ring
    _ = ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
          ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
        rw [hbridge]

/-! ## The `lintegral` form of the weighted Hardy inequality -/

/-- The weighted Hardy inequality in `ℝ≥0∞` form, with the sharp constant `1/(β(β-1))`. -/
theorem gbar_HarOp_weighted_lintegral (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 0)) :
    ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (100 / β ^ 2) *
          ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2) := by
  have hβ1 : (1 : ℝ) < β := by linarith
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ ENNReal.ofReal (1 / β) *
          (ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
            ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
    intro z hz
    have hz0 : 0 < z := hz
    have hy := gbar_HarOp_pointwise_sq β hβ1 f hf hz0
    calc ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * ENNReal.ofReal ((HarOp β f z) ^ 2) :=
          ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))
      _ ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
            (ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
              ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) :=
          mul_le_mul_of_nonneg_left hy bot_le
      _ = ENNReal.ofReal (1 / β) *
            (ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
              ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
          rw [mul_assoc (ENNReal.ofReal (1 / β)) (ENNReal.ofReal (z ^ (-β)))
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [mul_left_comm (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
                (ENNReal.ofReal (1 / β))
                (ENNReal.ofReal (z ^ (-β)) *
                  ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [← mul_assoc (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
                (ENNReal.ofReal (z ^ (-β)))
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [← ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
  have hA : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
    have h := setLIntegral_mono' (μ := volume) measurableSet_Ioi hpt
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
    exact h
  rw [HarOp_lintegral_swap β hβ1 f hf] at hA
  have hC : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)))
      ≤ ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1)) :=
    setLIntegral_mono' (μ := volume) measurableSet_Ioi
      (fun s hs => mul_le_mul_of_nonneg_left (w_tail_lintegral_bound β hβ1 hs) bot_le)
  have hD : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
      = ENNReal.ofReal (1 / (β - 1)) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
    have hpt2 : ∀ s ∈ Set.Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
        = ENNReal.ofReal (1 / (β - 1)) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
      intro s hs
      have hs0 : 0 < s := hs
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs0.le _) (sq_nonneg _))]
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (β - 1))]
      congr 1
      have h1 : s ^ (β - 1) * s ^ (1 - β) = 1 := by
        rw [← Real.rpow_add hs0, show β - 1 + (1 - β) = 0 by ring, Real.rpow_zero]
      calc s ^ (β - 1) * f s ^ 2 * ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
          = (s ^ (β - 1) * s ^ (1 - β)) * ((Work.Spaces.w s) ^ 2 * f s ^ 2) / (β - 1) := by
            ring
        _ = (Work.Spaces.w s) ^ 2 * f s ^ 2 / (β - 1) := by rw [h1, one_mul]
        _ = 1 / (β - 1) * ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt2,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hconst : (1 : ℝ) / β * (1 / (β - 1)) ≤ 100 / β ^ 2 := by
    rw [div_mul_div_comm, one_mul]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hβ]
  calc ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β))) := hA
    _ ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1)) :=
        mul_le_mul_of_nonneg_left hC bot_le
    _ = ENNReal.ofReal (1 / β) *
        (ENNReal.ofReal (1 / (β - 1)) *
          ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2)) := by
        rw [hD]
    _ = (ENNReal.ofReal (1 / β) * ENNReal.ofReal (1 / (β - 1))) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (100 / β ^ 2) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ bot_le
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / β)]
        exact ENNReal.ofReal_le_ofReal hconst

/-! ## The real-integral form -/

/-- **The weighted Hardy inequality**, real-integral form, with the a.e. strong measurability of
`HarOp β f` supplied as a hypothesis. -/
theorem gbar_HarOp_weighted_integral_le (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 0))
    (hfw : IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (f z) ^ 2) (Set.Ioi 0))
    (hmeas : AEStronglyMeasurable (HarOp β f) (volume.restrict (Set.Ioi 0))) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ (100 / β ^ 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2 := by
  have hC : (0 : ℝ) ≤ 100 / β ^ 2 := by positivity
  let G : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2
  let H : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (f z) ^ 2
  have hGnn : ∀ z, 0 ≤ G z := fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hHnn : ∀ z, 0 ≤ H z := fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hlin : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (G z)
      ≤ ENNReal.ofReal (100 / β ^ 2) * ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (H z) :=
    gbar_HarOp_weighted_lintegral β hβ f hf
  have hHfin : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (H z) < ⊤ := by
    have hEq : ENNReal.ofReal (∫ z, H z ∂volume.restrict (Set.Ioi 0))
        = ∫⁻ z, ENNReal.ofReal (H z) ∂volume.restrict (Set.Ioi 0) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfw
        (Filter.Eventually.of_forall hHnn)
    rw [← hEq]
    exact ENNReal.ofReal_lt_top
  have hGfin : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (G z) < ⊤ :=
    lt_of_le_of_lt hlin (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hHfin)
  have hHasFin : MeasureTheory.HasFiniteIntegral G (volume.restrict (Set.Ioi 0)) :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hGnn)).mpr hGfin
  have hw2 : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 0)) := by
    have hw0 : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
      unfold Work.Spaces.w
      exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
        (continuous_id.pow 2).continuousOn (fun z hz => by
          simp only [Set.mem_Ioi] at hz
          positivity)
    exact (hw0.pow 2).aestronglyMeasurable measurableSet_Ioi
  have hAESM : AEStronglyMeasurable G (volume.restrict (Set.Ioi 0)) :=
    hw2.mul (hmeas.pow 2)
  refine ⟨⟨hAESM, hHasFin⟩, ?_⟩
  exact Work.FTS.EllipticEst.Blocks.integral_le_of_lintegral_le hC hGnn hHnn hfw hlin

end Work.FTS.EllipticEst
