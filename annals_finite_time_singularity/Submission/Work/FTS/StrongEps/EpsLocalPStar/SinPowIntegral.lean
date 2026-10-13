import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.FTS.GalBasis.cc.sin_pow_int_general

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

theorem SinPowIntegral {γ : ℝ} (h1 : 1 < γ) (h2 : γ ≤ 2) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ Real.pi / 4) :
    ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2) ≤ (100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1) := by
  have hγ1 : 0 < γ - 1 := by linarith
  have hr : -1 < γ - 2 := by linarith
  have hb0 : 0 ≤ b := le_trans ha hab
  have hbpi : 2 * b ≤ Real.pi / 2 := by linarith [hb, Real.pi_pos]
  -- Integrability of the integrand on `0..b` (comparison with `x ↦ x ^ (γ-2)`).
  have hfint : IntervalIntegrable (fun x : ℝ => (Real.sin (2 * x)) ^ (γ - 2)) volume 0 b := by
    have hgint : IntervalIntegrable (fun x : ℝ => max 1 (2 ^ (γ - 2)) * x ^ (γ - 2)) volume 0 b :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) hr).const_mul _
    refine hgint.mono_fun' ?_ ?_
    · exact ((Real.measurable_sin.comp
        (measurable_const.mul measurable_id)).pow_const _).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
      have hx' : x ∈ Set.Ioc (0 : ℝ) b := by rwa [Set.uIoc_of_le hb0] at hx
      have hxpos : 0 < x := hx'.1
      have h2xpos : 0 < 2 * x := by linarith
      have h2xle : 2 * x ≤ Real.pi / 2 := by linarith [hx'.2, hb, Real.pi_pos]
      have hsinpos : 0 < Real.sin (2 * x) :=
        Real.sin_pos_of_pos_of_lt_pi h2xpos (by linarith [Real.pi_pos, h2xle])
      have hxr : 0 ≤ x ^ (γ - 2) := Real.rpow_nonneg (le_of_lt hxpos) _
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hsinpos) _)]
      rcases le_or_gt 0 (γ - 2) with hr0 | hr0
      · -- nonnegative exponent: `sin(2x) ≤ 2x`
        have hsle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (le_of_lt h2xpos)
        have hstep : (Real.sin (2 * x)) ^ (γ - 2) ≤ (2 * x) ^ (γ - 2) :=
          Real.rpow_le_rpow (le_of_lt hsinpos) hsle hr0
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hxpos)] at hstep
        exact hstep.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hxr)
      · -- negative exponent: Jordan's inequality `sin(2x) ≥ (4/π)x`
        have hjord : (4 / Real.pi) * x ≤ Real.sin (2 * x) := by
          have h := Real.mul_le_sin (x := 2 * x) (le_of_lt h2xpos) h2xle
          have he : 2 / Real.pi * (2 * x) = (4 / Real.pi) * x := by ring
          rwa [he] at h
        have hbase : 0 < (4 / Real.pi) * x := by positivity
        have hstep : (Real.sin (2 * x)) ^ (γ - 2) ≤ ((4 / Real.pi) * x) ^ (γ - 2) :=
          Real.rpow_le_rpow_of_nonpos hbase hjord (le_of_lt hr0)
        have hsplit : ((4 / Real.pi) * x) ^ (γ - 2)
            = (4 / Real.pi) ^ (γ - 2) * x ^ (γ - 2) :=
          Real.mul_rpow (by positivity) (le_of_lt hxpos)
        have hcoef : (4 / Real.pi) ^ (γ - 2) ≤ 1 := by
          have hp4 : (0 : ℝ) < Real.pi / 4 := by positivity
          have hle1 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
          have h' : (4 / Real.pi) = (Real.pi / 4)⁻¹ := by rw [inv_div]
          rw [h', Real.inv_rpow (le_of_lt hp4), ← Real.rpow_neg (le_of_lt hp4)]
          exact Real.rpow_le_one (le_of_lt hp4) hle1 (neg_nonneg.mpr (le_of_lt hr0))
        calc (Real.sin (2 * x)) ^ (γ - 2) ≤ ((4 / Real.pi) * x) ^ (γ - 2) := hstep
          _ = (4 / Real.pi) ^ (γ - 2) * x ^ (γ - 2) := hsplit
          _ ≤ 1 * x ^ (γ - 2) := mul_le_mul_of_nonneg_right hcoef hxr
          _ ≤ max 1 (2 ^ (γ - 2)) * x ^ (γ - 2) := by
              simpa using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (2 ^ (γ - 2))) hxr
  -- The integrand is nonnegative on `(0, b]`.
  have hnn : ((fun _ : ℝ => (0 : ℝ)) ≤ᵐ[volume.restrict (Set.Ioc 0 b)]
      (fun x : ℝ => (Real.sin (2 * x)) ^ (γ - 2))) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
    have h2xle : 2 * x ≤ Real.pi := by linarith [hx.2, hb, Real.pi_pos]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) h2xle) _
  have hstep1 : ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2)
      ≤ ∫ x in (0 : ℝ)..b, (Real.sin (2 * x)) ^ (γ - 2) :=
    intervalIntegral.integral_mono_interval (c := 0) (d := b) ha hab le_rfl hnn hfint
  have hstep2 : ∫ x in (0 : ℝ)..b, (Real.sin (2 * x)) ^ (γ - 2) ≤ b ^ (γ - 1) / (γ - 1) := by
    have h := Work.FTS.GalBasis.cc.sin_pow_int_general (γ := γ) (θ' := b) h1 hb0 hb
    have hmax : max (1 : ℝ) (2 ^ (γ - 2)) = 1 := by
      rw [max_eq_left]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    rwa [hmax, one_mul] at h
  have hsin_nn : 0 ≤ Real.sin (2 * b) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos, hb])
  -- `b ≤ sin(2b)` on `[0, π/4]` (Jordan).
  have hbsin : b ≤ Real.sin (2 * b) := by
    have hj := Real.mul_le_sin (x := 2 * b) (by linarith) hbpi
    have he : 2 / Real.pi * (2 * b) = (4 / Real.pi) * b := by ring
    have h4 : (4 / Real.pi) * b ≤ Real.sin (2 * b) := by rwa [he] at hj
    have h1' : (1 : ℝ) ≤ 4 / Real.pi := by
      rw [one_le_div (by positivity : (0 : ℝ) < Real.pi)]
      exact Real.pi_le_four
    have hble : b ≤ (4 / Real.pi) * b := by
      have := mul_le_mul_of_nonneg_right h1' hb0
      simpa using this
    linarith
  have hbpow : b ^ (γ - 1) ≤ (Real.sin (2 * b)) ^ (γ - 1) :=
    Real.rpow_le_rpow hb0 hbsin (by linarith)
  have hfinal : b ^ (γ - 1) / (γ - 1)
      ≤ (100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1) := by
    have h100 : b ^ (γ - 1) ≤ 100 * (Real.sin (2 * b)) ^ (γ - 1) := by
      have hs0 : 0 ≤ (Real.sin (2 * b)) ^ (γ - 1) := Real.rpow_nonneg hsin_nn _
      linarith
    have hinv : 0 ≤ (γ - 1)⁻¹ := inv_nonneg.mpr (le_of_lt hγ1)
    calc b ^ (γ - 1) / (γ - 1) = b ^ (γ - 1) * (γ - 1)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (100 * (Real.sin (2 * b)) ^ (γ - 1)) * (γ - 1)⁻¹ :=
            mul_le_mul_of_nonneg_right h100 hinv
      _ = (100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1) := by rw [div_eq_mul_inv]; ring
  calc ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2)
      ≤ ∫ x in (0 : ℝ)..b, (Real.sin (2 * x)) ^ (γ - 2) := hstep1
    _ ≤ b ^ (γ - 1) / (γ - 1) := hstep2
    _ ≤ (100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1) := hfinal

end Work.FTS.StrongEps.EpsLocalPStar
