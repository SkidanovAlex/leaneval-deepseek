import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set

/-- Weighted Cauchy–Schwarz ("psi_cs"): for `p > 0`, `z > 0` and `c` continuous on `(0,∞)`
with `c²` integrable on `(z,∞)`,
`(∫_z^∞ c t · t^{-p-1})² ≤ (1/p) z^{-p} ∫_z^∞ c² t^{-p-1}`.

This is Cauchy–Schwarz with the splitting
`c t · t^{-p-1} = (c t · t^{-(p+1)/2}) · t^{-(p+1)/2}` together with
`∫_z^∞ t^{-p-1} = z^{-p}/p`. -/
theorem psi_cs {p : ℝ} (hp : 0 < p) {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z)
    (h2 : MeasureTheory.IntegrableOn (fun t => (c t) ^ 2) (Set.Ioi z)) :
    (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ (1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by
  set e : ℝ := (-p - 1) / 2 with he
  have he_neg : e < 0 := by rw [he]; linarith
  have hee : e + e = -p - 1 := by rw [he]; ring
  have hp1 : -p - 1 < -1 := by linarith
  have hms : MeasurableSet (Set.Ioi z) := measurableSet_Ioi
  -- `c` is continuous on `(z,∞)`
  have hc' : ContinuousOn c (Set.Ioi z) := hc.mono (fun x hx => hz.trans hx)
  -- `t ↦ t ^ e` is continuous on `(z,∞)`
  have he_cont : ContinuousOn (fun t : ℝ => t ^ e) (Set.Ioi z) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x e (Or.inl (ne_of_gt (hz.trans hx)))).continuousWithinAt
  have hsplit : ∀ t ∈ Set.Ioi z, c t * t ^ (-p - 1) = (c t * t ^ e) * t ^ e := by
    intro t ht
    have ht0 : 0 < t := hz.trans ht
    rw [mul_assoc, ← Real.rpow_add ht0, hee]
  have hsq_f : ∀ t ∈ Set.Ioi z, ‖c t * t ^ e‖ ^ 2 = (c t) ^ 2 * t ^ (-p - 1) := by
    intro t ht
    have ht0 : 0 < t := hz.trans ht
    have hte : 0 ≤ t ^ e := Real.rpow_nonneg ht0.le e
    have h1 : ‖c t * t ^ e‖ = |c t| * t ^ e := by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hte]
    have h2 : (t ^ e) ^ 2 = t ^ (-p - 1) := by
      rw [sq, ← Real.rpow_add ht0, hee]
    rw [h1, mul_pow, sq_abs, h2]
  have hsq_g : ∀ t ∈ Set.Ioi z, (t ^ e) ^ 2 = t ^ (-p - 1) := by
    intro t ht
    have ht0 : 0 < t := hz.trans ht
    rw [sq, ← Real.rpow_add ht0, hee]
  -- integrability and `MemLp` bookkeeping
  have hcaesm : AEStronglyMeasurable c (volume.restrict (Set.Ioi z)) :=
    hc'.aestronglyMeasurable hms
  have hcmem : MemLp c 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hcaesm).2 h2
  have hgaesm : AEStronglyMeasurable (fun t : ℝ => t ^ e) (volume.restrict (Set.Ioi z)) :=
    he_cont.aestronglyMeasurable hms
  have hg_mem : MemLp (fun t : ℝ => t ^ e) 2 (volume.restrict (Set.Ioi z)) := by
    rw [memLp_two_iff_integrable_sq hgaesm]
    refine Integrable.congr (f := fun t : ℝ => t ^ (-p - 1)) ?_ ?_
    · exact integrableOn_Ioi_rpow_of_lt hp1 hz
    · filter_upwards [ae_restrict_mem hms] with t ht
      exact (hsq_g t ht).symm
  have hfaesm : AEStronglyMeasurable (fun t : ℝ => c t * t ^ e) (volume.restrict (Set.Ioi z)) :=
    (hc'.mul he_cont).aestronglyMeasurable hms
  have hf_mem : MemLp (fun t : ℝ => c t * t ^ e) 2 (volume.restrict (Set.Ioi z)) := by
    refine MemLp.of_le_mul (c := z ^ e) hcmem hfaesm ?_
    filter_upwards [ae_restrict_mem hms] with t ht
    have ht0 : 0 < t := hz.trans ht
    have hte : 0 ≤ t ^ e := Real.rpow_nonneg ht0.le e
    have hle : t ^ e ≤ z ^ e := Real.rpow_le_rpow_of_nonpos hz ht.le he_neg.le
    have h1 : ‖c t * t ^ e‖ = ‖c t‖ * t ^ e := by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hte]
    rw [h1, mul_comm (z ^ e)]
    exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  -- Cauchy–Schwarz in `L²`
  have hpq : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict (Set.Ioi z))
    (f := fun t : ℝ => c t * t ^ e) (g := fun t : ℝ => t ^ e) hpq
    (by simpa using hf_mem) (by simpa using hg_mem)
  -- identify the two `L²` norms on the right
  have hB : ∫ t in Set.Ioi z, ‖c t * t ^ e‖ ^ (2 : ℝ) = ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hms] with t ht
    rw [Real.rpow_two]
    exact hsq_f t ht
  have hP : ∫ t in Set.Ioi z, ‖t ^ e‖ ^ (2 : ℝ) = z ^ (-p) / p := by
    have h1 : ∫ t in Set.Ioi z, ‖t ^ e‖ ^ (2 : ℝ) = ∫ t in Set.Ioi z, t ^ (-p - 1) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hms] with t ht
      rw [Real.rpow_two, Real.norm_of_nonneg (Real.rpow_nonneg (hz.trans ht).le e)]
      exact hsq_g t ht
    rw [h1, integral_Ioi_rpow_of_lt hp1 hz, show -p - 1 + 1 = -p by ring, neg_div_neg_eq]
  have hholder' : ∫ t in Set.Ioi z, ‖c t * t ^ e‖ * ‖t ^ e‖
      ≤ Real.sqrt (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) * Real.sqrt (z ^ (-p) / p) := by
    have hh := hholder
    rw [hB, hP] at hh
    rwa [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  -- the `‖∫ f‖ ≤ ∫ ‖f‖` step
  have hnorm : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)|
      ≤ ∫ t in Set.Ioi z, ‖c t * t ^ e‖ * ‖t ^ e‖ := by
    have h1 : ∫ t in Set.Ioi z, c t * t ^ (-p - 1) = ∫ t in Set.Ioi z, (c t * t ^ e) * t ^ e := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hms] with t ht
      exact hsplit t ht
    have h2 : ∫ t in Set.Ioi z, ‖(c t * t ^ e) * t ^ e‖
        = ∫ t in Set.Ioi z, ‖c t * t ^ e‖ * ‖t ^ e‖ := by
      refine integral_congr_ae ?_
      filter_upwards with t
      rw [norm_mul]
    have h3 : ‖∫ t in Set.Ioi z, (c t * t ^ e) * t ^ e‖
        ≤ ∫ t in Set.Ioi z, ‖(c t * t ^ e) * t ^ e‖ := norm_integral_le_integral_norm _
    rw [h2] at h3
    rw [← h1] at h3
    rwa [← Real.norm_eq_abs]
  -- square everything
  have hBI : 0 ≤ ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hms] with t ht
    have ht0 : 0 < t := hz.trans ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le _)
  have hPI : 0 ≤ z ^ (-p) / p :=
    div_nonneg (Real.rpow_nonneg hz.le _) hp.le
  calc (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      = |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ^ 2 := by rw [sq_abs]
    _ ≤ (Real.sqrt (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) * Real.sqrt (z ^ (-p) / p)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hnorm.trans hholder') 2
    _ = (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) * (z ^ (-p) / p) := by
        rw [mul_pow, Real.sq_sqrt hBI, Real.sq_sqrt hPI]
    _ = (1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by ring

end Work.FTS.EllExist.Honesty
