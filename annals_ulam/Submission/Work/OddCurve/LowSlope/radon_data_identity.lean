import Mathlib
import Submission.Work.OddCurve.LowSlope.CruxStatements
import Submission.Work.OddCurve.LowSlope.section_ibp
import Submission.Work.OddCurve.LowSlope.radial_identity
import Submission.Work.OddCurve.LowSlope.sphereArea_eq_ballVol
import Submission.Work.OddCurve.LowSlope.radon_data_eq_inertiaIntegral

/-!
# Prop. `workHARD1` in one dimension

The spherical-Radon data of a body of revolution are the second moments of its central sections.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The pointwise algebra of Prop. `workHARD1`. -/
private lemma key_identity (n : ℕ) (hn : 1 ≤ n) {f ρ : ℝ → ℝ} {s c ν : ℝ}
    (hs : 0 < s)
    (hc : c = (Real.sqrt (1 + s ^ 2))⁻¹)
    (hfC1 : ContDiffOn ℝ 1 f (Set.Icc (-1 : ℝ) 1))
    (hρC1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρ : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u))
    (hν : ν ∈ Set.Ioo (-1 : ℝ) 1)
    (ht1 : ρ (c * ν) * (c * ν) ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - ν ^ 2) ^ (n - 1) * ((c * ν) ^ 2 * ρ (c * ν) ^ (2 * n + 2)) /
        Real.sqrt (1 - ν ^ 2)
      = (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
        * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)) := by
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := by
    apply Real.sqrt_pos.2
    have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
    linarith
  have hcpos : 0 < c := by rw [hc]; positivity
  have hclt : c < 1 := by
    rw [hc]
    refine inv_lt_one_of_one_lt₀ ?_
    have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
    have h : (1 : ℝ) < 1 + s ^ 2 := by linarith
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
  have hcsq : c ^ 2 * (1 + s ^ 2) = 1 := by
    have h : c * c * (1 + s ^ 2) = 1 := by
      rw [hc]; field_simp; rw [Real.sq_sqrt (by positivity)]
    rwa [pow_two]
  have hcu : c * ν ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by nlinarith [hν.1, hcpos, hclt], by nlinarith [hν.2, hcpos, hclt]⟩
  have h1nu : 0 < 1 - ν ^ 2 := by nlinarith [hν.1, hν.2]
  have hrp : 0 < ρ (c * ν) := hρpos _ hcu
  -- derivative facts
  have hρd : HasDerivAt ρ (deriv ρ (c * ν)) (c * ν) :=
    ((hρC1.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hcu) (fun u hu => hu))).hasDerivAt
  have hfd : HasDerivAt f (deriv f (ρ (c * ν) * (c * ν))) (ρ (c * ν) * (c * ν)) :=
    ((hfC1.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht1)
        (fun t ht => ⟨ht.1.le, ht.2.le⟩))).hasDerivAt
  have hrad := radial_identity hcu hrp hρd hfd hρ
  -- the two key relations
  have hf_eq : f (ρ (c * ν) * (c * ν)) = ρ (c * ν) * Real.sqrt (1 - (c * ν) ^ 2) :=
    (hρ _ hcu).symm
  have h1mu : 0 < 1 - (c * ν) ^ 2 := by nlinarith [hcu.1, hcu.2]
  have hRu : (c * ν) ^ 2 * (1 + s ^ 2) = ν ^ 2 := by
    rw [mul_pow]
    linear_combination (ν ^ 2) * hcsq
  have hR : rad0 f s (ρ (c * ν) * (c * ν)) = (ρ (c * ν)) ^ 2 * (1 - ν ^ 2) := by
    rw [rad0, hf_eq]
    have h1 : (ρ (c * ν) * Real.sqrt (1 - (c * ν) ^ 2)) ^ 2
        = (ρ (c * ν)) ^ 2 * (1 - (c * ν) ^ 2) := by rw [mul_pow, Real.sq_sqrt h1mu.le]
    have h2 : (s * (ρ (c * ν) * (c * ν))) ^ 2 = s ^ 2 * (ρ (c * ν)) ^ 2 * (c * ν) ^ 2 := by
      ring
    rw [h1, h2]
    nlinarith [hRu]
  have hsqrtR : Real.sqrt (rad0 f s (ρ (c * ν) * (c * ν)))
      = ρ (c * ν) * Real.sqrt (1 - ν ^ 2) := by
    rw [hR, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hrp.le]
  have hwn : Real.sqrt (1 - ν ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1nu)
  have hrn : ρ (c * ν) ≠ 0 := ne_of_gt hrp
  beta_reduce
  rw [hsqrtR, hR]
  have hreord : (ρ (c * ν) * (c * ν)) ^ 2 * f (ρ (c * ν) * (c * ν))
        * (f (ρ (c * ν) * (c * ν)) - (ρ (c * ν) * (c * ν)) * deriv f (ρ (c * ν) * (c * ν)))
        * ((ρ (c * ν)) ^ 2 * (1 - ν ^ 2)) ^ (n - 1)
        / (ρ (c * ν) * Real.sqrt (1 - ν ^ 2))
        * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν))
      = (ρ (c * ν) * (c * ν)) ^ 2
          * (f (ρ (c * ν) * (c * ν))
            * (f (ρ (c * ν) * (c * ν)) - (ρ (c * ν) * (c * ν)) * deriv f (ρ (c * ν) * (c * ν)))
            * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)))
          * ((ρ (c * ν)) ^ 2 * (1 - ν ^ 2)) ^ (n - 1)
          / (ρ (c * ν) * Real.sqrt (1 - ν ^ 2)) := by ring
  rw [hreord, hrad, mul_pow (ρ (c * ν)) (c * ν) 2,
    mul_pow ((ρ (c * ν)) ^ 2) (1 - ν ^ 2) (n - 1), ← pow_mul]
  have hpow2 : (ρ (c * ν)) ^ 2 * (ρ (c * ν)) ^ 3 * (ρ (c * ν)) ^ (2 * (n - 1))
      = (ρ (c * ν)) ^ (2 * n + 3) := by
    rw [show 2 * n + 3 = 2 + 3 + 2 * (n - 1) by omega, pow_add, pow_add]
  have hreord2 : (ρ (c * ν)) ^ 2 * (c * ν) ^ 2 * (ρ (c * ν)) ^ 3
        * ((ρ (c * ν)) ^ (2 * (n - 1)) * (1 - ν ^ 2) ^ (n - 1))
        / (ρ (c * ν) * Real.sqrt (1 - ν ^ 2))
      = (c * ν) ^ 2 * (1 - ν ^ 2) ^ (n - 1)
        * ((ρ (c * ν)) ^ 2 * (ρ (c * ν)) ^ 3 * (ρ (c * ν)) ^ (2 * (n - 1)))
        / (ρ (c * ν) * Real.sqrt (1 - ν ^ 2)) := by ring
  rw [hreord2, hpow2]
  have hpow3 : (ρ (c * ν)) ^ (2 * n + 3) = (ρ (c * ν)) ^ (2 * n + 2) * ρ (c * ν) := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, pow_succ]
  rw [hpow3, div_eq_div_iff hwn (mul_ne_zero hrn hwn)]
  ring

/-- **Prop. `workHARD1` in one dimension.** -/
theorem radon_data_eq_inertiaIntegral_proof : RadonDataEqInertiaIntegral := by
  intro n hn f ρ x y s hs hfC1 hρpos hρC1 hmono hρ hderivn hend_y hend_x hmem hmx hy hfy hfx
    hrootR hrootL hlt hpos hI1 hI2
  set c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹ with hc
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := by
    apply Real.sqrt_pos.2
    have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
    linarith
  have hsc : c * Real.sqrt (1 + s ^ 2) = 1 := by
    rw [hc, inv_mul_cancel₀ (ne_of_gt hspos)]
  have h1c : (1 : ℝ) / c = Real.sqrt (1 + s ^ 2) := by
    rw [one_div]; exact inv_eq_of_mul_eq_one_right hsc
  -- (1) the pointwise identity
  have hpt : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      (1 - ν ^ 2) ^ (n - 1) * ((c * ν) ^ 2 * ρ (c * ν) ^ (2 * n + 2)) /
          Real.sqrt (1 - ν ^ 2)
        = (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
          * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)) := by
    intro ν hν
    refine key_identity n hn hs hc hfC1 hρC1 hρpos hρ hν ?_
    have hmem' := hmem ν hν
    exact ⟨lt_trans hmx.1 hmem'.1, lt_trans hmem'.2 hy.2⟩
  -- (2) the integral of the pointwise identity
  have hInt1 : (∫ ν in (-1 : ℝ)..1,
        (1 - ν ^ 2) ^ (n - 1) * ((c * ν) ^ 2 * ρ (c * ν) ^ (2 * n + 2)) /
          Real.sqrt (1 - ν ^ 2))
      = ∫ ν in (-1 : ℝ)..1,
          (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
            * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ)] with ν hνne hν
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hν
    exact hpt ν ⟨hν.1, lt_of_le_of_ne hν.2 hνne⟩
  -- (3) pull out the factor `1/c`
  have hInt2 : (∫ ν in (-1 : ℝ)..1,
          (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
            * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)))
      = (1 / c) * ∫ ν in (-1 : ℝ)..1,
          (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
            * (c * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro ν _
    have hcne : c ≠ 0 := by rw [hc]; exact inv_ne_zero (ne_of_gt hspos)
    field_simp
  -- (4) the change of variables
  have hchange := radon_change_of_variables n hs hρpos hρC1 hmono hρ hderivn hend_y hend_x
  -- (5) the integration by parts
  have hfxe : f (-(x s)) = -(s * (-(x s))) := by
    rw [hfx]; ring
  have hibp := section_ibp n hn f (x s) (y s) s hs hfC1 hmx hy hlt hfy hfxe hpos hI1 hI2
  -- assemble
  have hmain : (∫ ν in (-1 : ℝ)..1,
        (1 - ν ^ 2) ^ (n - 1) * ((c * ν) ^ 2 * ρ (c * ν) ^ (2 * n + 2)) /
          Real.sqrt (1 - ν ^ 2))
      = Real.sqrt (1 + s ^ 2) *
        ∫ t in (-(x s))..(y s), t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
          Real.sqrt (rad0 f s t) := by
    rw [hInt1, hInt2, h1c, hchange]
  rw [hmain]
  -- the constants
  have hsphere := sphereArea_eq_ballVol (2 * n - 2)
  have hcast : (((2 * n - 2 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) - 1 := by
    have h2 : 2 * n - 2 = 2 * (n - 1) := by omega
    rw [h2, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn]
    ring
  have hbcast : 2 * n - 2 + 1 = 2 * n - 1 := by omega
  rw [hsphere, hbcast, hcast]
  have hBne : (2 * (n : ℝ) - 1) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  -- final arithmetic
  have hkey : (∫ t in (-(x s))..(y s), t ^ 2 * f t * (f t - t * deriv f t)
        * rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t))
      = (2 * (n : ℝ) + 2) / (2 * (n : ℝ) - 1) * inertiaIntegral n f x y s := by
    have hJ : inertiaIntegral n f x y s
        = ∫ t in (-(x s))..(y s), t ^ 2 * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t) :=
      rfl
    rw [hJ, div_mul_eq_mul_div, eq_div_iff hBne]
    linarith [hibp]
  rw [hkey]
  field_simp

end

end Work.OddCurve.LowSlope
