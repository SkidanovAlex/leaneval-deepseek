import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Order.Interval.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB1

open MeasureTheory Set Filter
open scoped Interval Topology

theorem rpow_ode_aux {k M z : ℝ} (hk : 0 < k) (hz : 0 < z) {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ioo 0 (z + 1)))
    (hbdd : ∀ u ∈ Set.Ioo (0 : ℝ) (z + 1), |h u| ≤ M) :
    HasDerivAt (fun z' => ∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (z' * v))
      ((h z - k * (∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (z * v))) / z) z := by
  -- `M` is nonnegative: evaluate the bound at an interior point.
  have hM : 0 ≤ M := by
    have h1 : |h (z / 2)| ≤ M := hbdd (z / 2) ⟨by linarith, by linarith⟩
    have h2 : (0 : ℝ) ≤ |h (z / 2)| := abs_nonneg _
    linarith
  have hzmem : z ∈ Set.Ioo (0 : ℝ) (z + 1) := ⟨hz, by linarith⟩
  -- Basic continuity of the integrand on the open interval.
  have hcφ : ContinuousOn (fun u : ℝ => u ^ (k - 1) * h u) (Set.Ioo 0 (z + 1)) := by
    have h1 : ContinuousOn (fun x : ℝ => x ^ (k - 1)) (Set.Ioo 0 (z + 1)) :=
      continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
    exact h1.mul hcont
  -- Interval integrability of `u ↦ u^(k-1) * h u` on `(0,z)`.
  have hφint : IntervalIntegrable (fun u : ℝ => u ^ (k - 1) * h u) volume 0 z := by
    have hcIoc : ContinuousOn (fun u : ℝ => u ^ (k - 1) * h u) (Set.Ioc 0 z) :=
      hcφ.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
    have hmeas : AEStronglyMeasurable (fun u : ℝ => u ^ (k - 1) * h u)
        (volume.restrict (Set.Ioc 0 z)) :=
      hcIoc.aestronglyMeasurable measurableSet_Ioc
    have hg : IntegrableOn (fun u : ℝ => M * u ^ (k - 1)) (Set.Ioc 0 z) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mp
        ((intervalIntegral.intervalIntegrable_rpow'
          (a := 0) (b := z) (by linarith : (-1 : ℝ) < k - 1)).const_mul M)
    have hle : ∀ᵐ u ∂volume.restrict (Set.Ioc 0 z),
        ‖u ^ (k - 1) * h u‖ ≤ M * u ^ (k - 1) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      have hu' : u ∈ Set.Ioo (0 : ℝ) (z + 1) := ⟨hu.1, by linarith [hu.2]⟩
      have hbu : |h u| ≤ M := hbdd u hu'
      have hx : (0 : ℝ) ≤ u ^ (k - 1) := Real.rpow_nonneg hu.1.le _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
      nlinarith [hbu, hx, hM]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mpr (hg.mono' hmeas hle)
  have hφcontAt : ContinuousAt (fun u : ℝ => u ^ (k - 1) * h u) z :=
    hcφ.continuousAt (isOpen_Ioo.mem_nhds hzmem)
  have hsm : StronglyMeasurableAtFilter (fun u : ℝ => u ^ (k - 1) * h u) (𝓝 z) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun x hx => hcφ.continuousAt (isOpen_Ioo.mem_nhds hx)) z hzmem
  -- FTC: derivative of the primitive.
  have hderivG : HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..t, u ^ (k - 1) * h u)
      (z ^ (k - 1) * h z) z :=
    intervalIntegral.integral_hasDerivAt_right hφint hsm hφcontAt
  -- Product rule with `t^(-k)`.
  have hderiv : HasDerivAt
      (fun t : ℝ => t ^ (-k) * ∫ u in (0 : ℝ)..t, u ^ (k - 1) * h u)
      ((-k) * z ^ (-k - 1) * (∫ u in (0 : ℝ)..z, u ^ (k - 1) * h u)
        + z ^ (-k) * (z ^ (k - 1) * h z)) z := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ (-k)) ((-k) * z ^ (-k - 1)) z := by
      have hlt := Real.hasDerivAt_rpow_const (x := z) (p := -k) (Or.inl hz.ne')
      exact hlt
    exact h1.mul hderivG
  -- The substitution identity, for every `t > 0` (in fact, near `z`).
  have hid : ∀ t ∈ Set.Ioo (0 : ℝ) (z + 1),
      (∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (t * v))
        = t ^ (-k) * ∫ u in (0 : ℝ)..t, u ^ (k - 1) * h u := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hstep1 : (∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (t * v))
        = ∫ v in (0 : ℝ)..1, t ^ (1 - k) * ((t * v) ^ (k - 1) * h (t * v)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
      have hv0 : (0 : ℝ) ≤ v := hv.1
      calc v ^ (k - 1) * h (t * v)
          = (t ^ (1 - k) * t ^ (k - 1)) * (v ^ (k - 1) * h (t * v)) := by
            rw [← Real.rpow_add ht0 (1 - k) (k - 1),
              show (1 - k) + (k - 1) = (0 : ℝ) by ring, Real.rpow_zero, one_mul]
        _ = t ^ (1 - k) * (t ^ (k - 1) * v ^ (k - 1) * h (t * v)) := by ring
        _ = t ^ (1 - k) * ((t * v) ^ (k - 1) * h (t * v)) := by
            rw [Real.mul_rpow ht0.le hv0]
    have hstep2 : (∫ v in (0 : ℝ)..1, t ^ (1 - k) * ((t * v) ^ (k - 1) * h (t * v)))
        = t ^ (1 - k) * ∫ v in (0 : ℝ)..1, (t * v) ^ (k - 1) * h (t * v) :=
      intervalIntegral.integral_const_mul _ _
    have hstep3 : (∫ v in (0 : ℝ)..1, (t * v) ^ (k - 1) * h (t * v))
        = t⁻¹ * ∫ u in (0 : ℝ)..t, u ^ (k - 1) * h u := by
      have h := intervalIntegral.integral_comp_mul_left
        (f := fun u : ℝ => u ^ (k - 1) * h u) (a := (0 : ℝ)) (b := 1) (c := t) ht0.ne'
      simpa [zero_mul, mul_one, smul_eq_mul] using h
    rw [hstep1, hstep2, hstep3, ← mul_assoc, ← Real.rpow_neg_one t,
      ← Real.rpow_add ht0 (1 - k) (-1), show (1 - k) + (-1) = -k by ring]
  -- The derivative value equals the stated one.
  have hD : ((-k) * z ^ (-k - 1) * (∫ u in (0 : ℝ)..z, u ^ (k - 1) * h u)
        + z ^ (-k) * (z ^ (k - 1) * h z))
      = (h z - k * (∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (z * v))) / z := by
    rw [hid z hzmem]
    have hz1 : z ^ (-k - 1) = z ^ (-k) / z := by
      rw [show (-k - 1 : ℝ) = -k + (-1) by ring, Real.rpow_add hz, Real.rpow_neg_one]
      ring
    have hz2 : z ^ (-k) * z ^ (k - 1) = 1 / z := by
      rw [← Real.rpow_add hz (-k) (k - 1),
        show -k + (k - 1) = (-1 : ℝ) by ring, Real.rpow_neg_one]
      ring
    have hz3 : z ^ (-k) * (z ^ (k - 1) * h z) = h z / z := by
      rw [← mul_assoc, hz2]; ring
    rw [hz1, hz3, div_eq_mul_inv]
    ring
  -- Assemble.
  have hev : (fun t : ℝ => ∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (t * v))
      =ᶠ[𝓝 z] (fun t : ℝ => t ^ (-k) * ∫ u in (0 : ℝ)..t, u ^ (k - 1) * h u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzmem] with t ht
    exact hid t ht
  rw [← hD]
  exact hderiv.congr_of_eventuallyEq hev

end Work.FTS_StreamBdry.SB1
