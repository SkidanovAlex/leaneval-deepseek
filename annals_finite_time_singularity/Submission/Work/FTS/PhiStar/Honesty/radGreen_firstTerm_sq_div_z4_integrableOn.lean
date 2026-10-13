import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Have
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Honesty.lintegral_Ioo_triangle
import Submission.Work.FTS.PhiStar.Honesty.lintegral_ofReal_rpow_Ioo_left
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_mul_rpow
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_mul_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

/-- Cauchy-Schwarz with the constant function `1` on the interval `[0,z]`, `z ≥ 0`:
`(∫_0^z f)² ≤ z ∫_0^z f²`.  Proved by completing the square. -/
private theorem cs_zero_interval {f : ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (hf : IntervalIntegrable f volume 0 z)
    (hf2 : IntervalIntegrable (fun t : ℝ => f t ^ 2) volume 0 z) :
    (∫ t in (0 : ℝ)..z, f t) ^ 2 ≤ z * ∫ t in (0 : ℝ)..z, f t ^ 2 := by
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    simp
  · set A : ℝ := ∫ t in (0 : ℝ)..z, f t with hA
    set B : ℝ := ∫ t in (0 : ℝ)..z, f t ^ 2 with hB
    have key : ∀ c : ℝ, 0 ≤ c ^ 2 * z - 2 * c * A + B := by
      intro c
      have hA1 : IntervalIntegrable (fun t : ℝ => f t ^ 2 - 2 * c * f t) volume 0 z :=
        hf2.sub (hf.const_mul (2 * c))
      have hA2 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 z := intervalIntegrable_const
      have hiden : (∫ t in (0 : ℝ)..z, (f t - c) ^ 2) = c ^ 2 * z - 2 * c * A + B := by
        have h1 : (∫ t in (0 : ℝ)..z, (f t - c) ^ 2)
            = ∫ t in (0 : ℝ)..z, (f t ^ 2 - 2 * c * f t + c ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
        rw [h1]
        have hadd : (∫ t in (0 : ℝ)..z, (f t ^ 2 - 2 * c * f t + c ^ 2))
            = (∫ t in (0 : ℝ)..z, (f t ^ 2 - 2 * c * f t))
              + (∫ t in (0 : ℝ)..z, c ^ 2) := by
          simpa using intervalIntegral.integral_add hA1 hA2
        rw [hadd]
        have hsub : (∫ t in (0 : ℝ)..z, (f t ^ 2 - 2 * c * f t))
            = (∫ t in (0 : ℝ)..z, f t ^ 2) - (∫ t in (0 : ℝ)..z, 2 * c * f t) := by
          simpa using intervalIntegral.integral_sub hf2 (hf.const_mul (2 * c))
        rw [hsub, ← hB]
        have hmul : (∫ t in (0 : ℝ)..z, 2 * c * f t) = 2 * c * (∫ t in (0 : ℝ)..z, f t) := by
          simpa using intervalIntegral.integral_const_mul (2 * c) f
        rw [hmul, ← hA]
        have hconst : (∫ t in (0 : ℝ)..z, c ^ 2) = c ^ 2 * z := by
          rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul, sub_zero]
          ring
        rw [hconst]
        ring
      have hnn : 0 ≤ ∫ t in (0 : ℝ)..z, (f t - c) ^ 2 :=
        intervalIntegral.integral_nonneg hz (fun u _ => sq_nonneg (f u - c))
      linarith [hiden ▸ hnn]
    have hzA := key (A / z)
    have hexp : z * ((A / z) ^ 2 * z - 2 * (A / z) * A + B) = B * z - A ^ 2 := by
      field_simp
      ring
    have hle : A ^ 2 ≤ B * z := by
      have h : 0 ≤ B * z - A ^ 2 := by rw [← hexp]; exact mul_nonneg hzpos.le hzA
      linarith
    rw [mul_comm z B]
    exact hle

/-- The abstract version of the target statement: for a single exponent `r > -1` the
power-primitive `∫_0^z c t t^r`, weighted by `z^{-(r+1)}`, is square-integrable against
`z^{-4}` on `(0,1)`, whenever `c` is continuous there and `c(t)²/t⁴` is integrable.

This is the sharp form of the near-`0` estimate for the first term of the radial Green
function of `Work.FTS.PhiStar.Radial.radGreen`: the proof combines the Cauchy-Schwarz
inequality `(∫_0^z f)² ≤ z ∫_0^z f²` with the weighted Hardy/Tonelli computation
`∫_0^1 z^{-(2r+5)} ∫_0^z c² t^{2r}`. -/
private theorem key (r : ℝ) (hr : -1 < r) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioo 0 1))
    (hint : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    IntegrableOn
      (fun z : ℝ => (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)
      (Set.Ioo 0 1) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- integrability of the two integrands on `Icc 0 1`
  have hfIcc : IntegrableOn (fun t : ℝ => c t * t ^ r) (Set.Icc 0 1) :=
    integrableOn_mul_rpow (by linarith) hc hint
  have hf2Icc : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) (Set.Icc 0 1) :=
    integrableOn_sq_mul_rpow (by linarith) hc hint
  have hf2Ioo : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) (Set.Ioo 0 1) :=
    hf2Icc.mono_set fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- the pointwise rewriting of the square
  have hpow : ∀ t : ℝ, 0 ≤ t → (c t * t ^ r) ^ 2 = (c t) ^ 2 * t ^ (2 * r) := by
    intro t ht
    have htr : (t ^ r) ^ 2 = t ^ (2 * r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
      congr 1
      ring
    rw [mul_pow, htr]
  -- Cauchy-Schwarz with the constant function `1`
  have hcs : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2
        ≤ z * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r) := by
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := le_of_lt hz.1
    have hz1 : z ≤ 1 := le_of_lt hz.2
    have hsub : Set.Icc 0 z ⊆ Set.Icc 0 1 :=
      fun x hx => ⟨hx.1, le_trans hx.2 hz1⟩
    have h1 : IntervalIntegrable (fun t : ℝ => c t * t ^ r) volume 0 z :=
      IntegrableOn.intervalIntegrable (by rw [uIcc_of_le hz0]; exact hfIcc.mono_set hsub)
    have h2' : IntervalIntegrable (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) volume 0 z :=
      IntegrableOn.intervalIntegrable (by rw [uIcc_of_le hz0]; exact hf2Icc.mono_set hsub)
    have h2 : IntervalIntegrable (fun t : ℝ => (c t * t ^ r) ^ 2) volume 0 z :=
      h2'.congr fun t ht => by
        rw [uIoc_of_le hz0] at ht
        exact (hpow t (le_of_lt ht.1)).symm
    have h3 := cs_zero_interval hz0 h1 h2
    have h4 : (∫ t in (0 : ℝ)..z, (c t * t ^ r) ^ 2)
        = ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r) :=
      intervalIntegral.integral_congr fun t ht => by
        rw [uIcc_of_le hz0] at ht
        exact hpow t ht.1
    rw [h4] at h3
    exact h3
  -- the bound `G z ≤ z^{-(2r+5)} * ∫_0^z (c t)^2 t^{2r}`
  have hGbound : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4
        ≤ z ^ (-(2 * r + 5)) * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r) := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hz0' : (0 : ℝ) ≤ z := le_of_lt hz0
    have hA : (z ^ (-(r + 1))) ^ 2 = z ^ (-(2 * r + 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz0']
      congr 1
      ring
    have hB : z ^ (-(2 * r + 2)) * z ^ (-((4 : ℕ) : ℝ)) = z ^ (-(2 * r + 6)) := by
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    have hC : (z ^ 4)⁻¹ = z ^ (-((4 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast z 4]
      exact (Real.rpow_neg hz0' ((4 : ℕ) : ℝ)).symm
    have he : (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4
        = z ^ (-(2 * r + 6)) * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2 := by
      calc (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4
          = ((z ^ (-(r + 1))) ^ 2 * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2) * (z ^ 4)⁻¹ := by
            rw [div_eq_mul_inv, mul_pow]
        _ = (z ^ (-(2 * r + 2)) * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2)
              * z ^ (-((4 : ℕ) : ℝ)) := by
            rw [hA, hC]
        _ = (z ^ (-(2 * r + 2)) * z ^ (-((4 : ℕ) : ℝ)))
              * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2 := by ring
        _ = z ^ (-(2 * r + 6)) * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2 := by rw [hB]
    rw [he]
    calc z ^ (-(2 * r + 6)) * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2
        ≤ z ^ (-(2 * r + 6)) * (z * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r)) :=
          mul_le_mul_of_nonneg_left (hcs z hz) (Real.rpow_nonneg hz0' _)
      _ = z ^ (-(2 * r + 5)) * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r) := by
          have hstep2 : z ^ (-(2 * r + 6)) * z = z ^ (-(2 * r + 5)) := by
            have h1 : z ^ (-(2 * r + 6)) * z = z ^ (-(2 * r + 6)) * z ^ (1 : ℝ) := by
              rw [Real.rpow_one]
            rw [h1, ← Real.rpow_add hz0]
            congr 1
            ring
          rw [← mul_assoc, hstep2]
  -- measurability of the three weight functions
  have hWcont : ContinuousOn (fun z : ℝ => ENNReal.ofReal (z ^ (-(2 * r + 5))))
      (Set.Ioo (0 : ℝ) 1) :=
    ENNReal.continuous_ofReal.continuousOn.comp
      (fun z hz => (Real.continuousAt_rpow_const z (-(2 * r + 5))
        (Or.inl (ne_of_gt hz.1))).continuousWithinAt)
      (fun z _ => mem_univ _)
  have hHcont : ContinuousOn (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)))
      (Set.Ioo (0 : ℝ) 1) :=
    ENNReal.continuous_ofReal.continuousOn.comp
      ((hc.pow 2).mul (fun z hz => (Real.continuousAt_rpow_const z (2 * r)
        (Or.inl (ne_of_gt hz.1))).continuousWithinAt))
      (fun z _ => mem_univ _)
  have hWmeas : AEMeasurable (fun z : ℝ => ENNReal.ofReal (z ^ (-(2 * r + 5))))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hWcont.aemeasurable measurableSet_Ioo
  have hHmeas : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hHcont.aemeasurable measurableSet_Ioo
  have hQmeas : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    (ENNReal.continuous_ofReal.continuousOn.comp
      ((hc.pow 2).div (continuousOn_id.pow 4) (fun z hz => pow_ne_zero 4 (ne_of_gt hz.1)))
      (fun z _ => mem_univ _)).aemeasurable measurableSet_Ioo
  -- the a.e. pointwise bound in `ofReal` form
  have hstep : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)
        ≤ ENNReal.ofReal (z ^ (-(2 * r + 5)))
            * ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hzle : z ≤ 1 := le_of_lt hz.2
    have hint2 : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) (Set.Ioo (0 : ℝ) z) :=
      hf2Ioo.mono_set fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hzle⟩
    have hnn2 : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) z)]
        (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht.1) _)
    have hconv : ENNReal.ofReal (∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r))
        = ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := by
      rw [intervalIntegral.integral_of_le hz0.le, integral_Ioc_eq_integral_Ioo]
      exact ofReal_integral_eq_lintegral_ofReal hint2 hnn2
    calc ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)
        ≤ ENNReal.ofReal (z ^ (-(2 * r + 5)) * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r)) :=
          ENNReal.ofReal_le_ofReal (hGbound z hz)
      _ = ENNReal.ofReal (z ^ (-(2 * r + 5)))
            * ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hz0) _), hconv]
  -- the lintegral bound
  have hlin1 : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4))
      ≤ ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (z ^ (-(2 * r + 5)))
          * ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hstep z hz
  have hlin2 : (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) * ∫⁻ z in Set.Ioo t 1,
          ENNReal.ofReal (z ^ (-(2 * r + 5))))
      ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
          * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4)) := by
    have hr' : -(2 * r + 5) < (-1 : ℝ) := by linarith
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [lintegral_ofReal_rpow_Ioo_left (r := -(2 * r + 5)) (t := t) ht.1 (le_of_lt ht.2) hr']
    refine ENNReal.ofReal_le_ofReal ?_
    have hut : 1 ≤ t ^ (-(2 * r + 4)) := by
      have h := Real.rpow_le_rpow_of_nonpos ht.1 (le_of_lt ht.2) (show -(2 * r + 4) ≤ 0 by linarith)
      rwa [Real.one_rpow] at h
    have hv : (0 : ℝ) < 2 * r + 4 := by linarith
    rw [show -(2 * r + 5) + 1 = -(2 * r + 4) by ring]
    have hkey : (1 - t ^ (-(2 * r + 4))) / (-(2 * r + 4))
        = (t ^ (-(2 * r + 4)) - 1) / (2 * r + 4) := by
      rw [div_neg, ← neg_div, neg_sub]
    rw [hkey, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (le_of_lt hv))
  have hlin3 : (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
        * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4)))
      = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
          * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
    have hv : (0 : ℝ) < 2 * r + 4 := by linarith
    have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
            * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4))
          = ENNReal.ofReal ((c t) ^ 2 / t ^ 4) * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have hA : ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) * ENNReal.ofReal (t ^ (-(2 * r + 4)))
          = ENNReal.ofReal ((c t) ^ 2 / t ^ 4) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht0) _))]
        congr 1
        rw [div_eq_mul_inv, ← Real.rpow_natCast t 4, ← Real.rpow_neg (le_of_lt ht0) ((4 : ℕ) : ℝ)]
        rw [mul_assoc, ← Real.rpow_add ht0]
        congr 1
        ring
      have hB : ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4))
          = ENNReal.ofReal (t ^ (-(2 * r + 4))) * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos hv, div_eq_mul_inv]
      rw [hB, ← mul_assoc, hA]
    rw [lintegral_congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hpt t ht)]
    rw [lintegral_mul_const'' _ hQmeas]
  have hfin : (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4)) < ∞ := by
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun t : ℝ => (c t) ^ 2 / t ^ 4) :=
      Eventually.of_forall fun t => div_nonneg (sq_nonneg _) (by positivity)
    exact (hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral
  have hmain : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4))
      ≤ (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
          * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
    calc (∫⁻ z in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4))
        ≤ ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (z ^ (-(2 * r + 5)))
            * ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := hlin1
      _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
            * ∫⁻ z in Set.Ioo t 1, ENNReal.ofReal (z ^ (-(2 * r + 5))) :=
          lintegral_Ioo_triangle (a := 0) (b := 1) h01 hWmeas hHmeas
      _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
            * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4)) := hlin2
      _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
            * (ENNReal.ofReal (2 * r + 4))⁻¹ := hlin3
  have hlt : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)) < ∞ :=
    lt_of_le_of_lt hmain (ENNReal.mul_lt_top hfin
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < 2 * r + 4))))
  -- continuity of the target function and conclusion
  have hPcont : ContinuousOn (fun z : ℝ => ∫ t in (0 : ℝ)..z, c t * t ^ r) (Set.Ioo (0 : ℝ) 1) :=
    (intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1)
      (by rw [uIcc_of_le h01]; exact hfIcc)).mono fun x hx => by
        rw [uIcc_of_le h01]
        exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hpowcont : ContinuousOn (fun z : ℝ => z ^ (-(r + 1))) (Set.Ioo (0 : ℝ) 1) :=
    fun z hz => (Real.continuousAt_rpow_const z (-(r + 1))
      (Or.inl (ne_of_gt hz.1))).continuousWithinAt
  have hcont : ContinuousOn
      (fun z : ℝ => (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)
      (Set.Ioo (0 : ℝ) 1) :=
    ((hpowcont.mul hPcont).pow 2).div (continuousOn_id.pow 4)
      fun z hz => pow_ne_zero 4 (ne_of_gt hz.1)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
      (fun z : ℝ => (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hz.1) 4)
  exact ⟨hcont.aestronglyMeasurable measurableSet_Ioo,
    (hasFiniteIntegral_iff_ofReal hnn).mpr (by simpa only using hlt)⟩

theorem radGreen_firstTerm_sq_div_z4_integrableOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioo 0 1))
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (z ^ (-(2 * (m : ℝ) + 5) / α)
          * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))) ^ 2 / z ^ 4)
      (Set.Ioo 0 1) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hr : (-1 : ℝ) < (2 * (m : ℝ) + 5) / α - 1 := by
    have hpos : (0 : ℝ) < (2 * (m : ℝ) + 5) / α := div_pos (by linarith) hα
    linarith
  have hk := key ((2 * (m : ℝ) + 5) / α - 1) hr hc hint
  refine hk.congr_fun ?_ measurableSet_Ioo
  intro z hz
  have hexp : -((2 * (m : ℝ) + 5) / α - 1 + 1) = -(2 * (m : ℝ) + 5) / α := by
    rw [sub_add_cancel]
    exact (neg_div α (2 * (m : ℝ) + 5)).symm
  rw [hexp]

end Work.FTS.PhiStar.Honesty
