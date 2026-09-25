import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.Analysis.Complex

open MeasureTheory Set
open scoped Topology

private lemma psiKfun_pointwise {ρ : ℂ} {t : ℝ} (ht : 1 < t) :
    (t : ℂ) ^ ρ * (((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) : ℝ) : ℂ)
      = (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹) := by
  have ht0 : t ≠ 0 := by linarith
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  have hsub : (t : ℂ) ^ (ρ - 2) = (t : ℂ) ^ ρ * ((t : ℂ) ^ 2)⁻¹ := by
    have h2 : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
    rw [Complex.cpow_sub ρ 2 htc, h2, Complex.cpow_natCast, div_eq_mul_inv]
  rw [hsub]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add,
    Complex.ofReal_inv, Complex.ofReal_one]
  field_simp

private lemma psiKfun_norm_bound {ρ : ℂ} (hρ : ρ.re = 1 / 2) {t : ℝ} (ht : 2 ≤ t) :
    ‖(t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹)‖
      ≤ (1 / Real.log 2 + 1 / (Real.log 2) ^ 2) * t ^ (-(3 / 2) : ℝ) := by
  have ht0 : (0:ℝ) < t := by linarith
  have ht1 : (1:ℝ) < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : ‖(t : ℂ) ^ (ρ - 2)‖ = t ^ (-(3 / 2) : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, hρ]
    norm_num
  have hB : ‖(↑(Real.log t)⁻¹ + ↑((Real.log t) ^ 2)⁻¹ : ℂ)‖
      ≤ 1 / Real.log 2 + 1 / (Real.log 2) ^ 2 := by
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    have h1 : (Real.log t)⁻¹ ≤ (Real.log 2)⁻¹ := inv_anti₀ hlog2 hlt
    have h2 : ((Real.log t) ^ 2)⁻¹ ≤ ((Real.log 2) ^ 2)⁻¹ :=
      inv_anti₀ (pow_pos hlog2 2) (pow_le_pow_left₀ hlog2.le hlt 2)
    calc ‖(↑(Real.log t)⁻¹ + ↑((Real.log t) ^ 2)⁻¹ : ℂ)‖
        ≤ ‖(↑(Real.log t)⁻¹ : ℂ)‖ + ‖(↑((Real.log t) ^ 2)⁻¹ : ℂ)‖ := norm_add_le _ _
      _ = (Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlogt),
                Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hlogt 2))]
      _ ≤ (Real.log 2)⁻¹ + ((Real.log 2) ^ 2)⁻¹ := add_le_add h1 h2
      _ = 1 / Real.log 2 + 1 / (Real.log 2) ^ 2 := by simp [one_div]
  rw [norm_mul, hA]
  calc t ^ (-(3 / 2) : ℝ) * ‖(↑(Real.log t)⁻¹ + ↑((Real.log t) ^ 2)⁻¹ : ℂ)‖
      ≤ t ^ (-(3 / 2) : ℝ) * (1 / Real.log 2 + 1 / (Real.log 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg ht0.le _)
    _ = (1 / Real.log 2 + 1 / (Real.log 2) ^ 2) * t ^ (-(3 / 2) : ℝ) := by ring

private lemma integrableOn_psiKfun {ρ : ℂ} (hρ : ρ.re = 1 / 2) {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹))
      (Set.Ioi x) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hcont : ContinuousOn
      (fun t : ℝ => (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹)) (Set.Ioi x) := by
    have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.Ioi x) :=
      Real.continuousOn_log.mono (fun t ht => by
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (by linarith [Set.mem_Ioi.mp ht]))
    have hinv : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Ioi x) :=
      hlog.inv₀ (fun t ht => ne_of_gt (Real.log_pos (by linarith [Set.mem_Ioi.mp ht])))
    have hsq : ContinuousOn (fun t : ℝ => ((Real.log t) ^ 2)⁻¹) (Set.Ioi x) :=
      (hlog.pow 2).inv₀ (fun t ht =>
        pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [Set.mem_Ioi.mp ht]))))
    have hB : ContinuousOn
        (fun t : ℝ => (↑((Real.log t)⁻¹) + ↑(((Real.log t) ^ 2)⁻¹) : ℂ)) (Set.Ioi x) :=
      (Complex.continuous_ofReal.comp_continuousOn hinv).add
        (Complex.continuous_ofReal.comp_continuousOn hsq)
    have hA : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (ρ - 2)) (Set.Ioi x) :=
      Complex.continuous_ofReal.continuousOn.cpow_const
        (fun t ht => Complex.ofReal_mem_slitPlane.2 (by linarith [Set.mem_Ioi.mp ht]))
    exact hA.mul hB
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹))
      (volume.restrict (Set.Ioi x)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hg : IntegrableOn
      (fun t : ℝ => (1 / Real.log 2 + 1 / (Real.log 2) ^ 2) * t ^ (-(3 / 2) : ℝ)) (Set.Ioi x) := by
    have h := integrableOn_Ioi_rpow_of_lt (a := -(3 / 2)) (c := x) (by norm_num) hx0
    exact MeasureTheory.Integrable.const_mul h _
  refine Integrable.mono' hg hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  exact psiKfun_norm_bound hρ (by linarith [Set.mem_Ioi.mp ht])

theorem integral_cpow_mul_psiKfun {ρ : ℂ} (hρ : ρ.re = 1 / 2) {x Y : ℝ} (hx : 2 ≤ x) (hxY : x ≤ Y) :
    (∫ t in x..Y, (t : ℂ) ^ ρ * (((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) : ℝ) : ℂ)) =
      (∫ t in Set.Ioi x, (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹)) -
      (∫ t in Set.Ioi Y, (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹)) := by
  have hfx := integrableOn_psiKfun hρ hx
  have hfY : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹)) (Set.Ioi Y) :=
    hfx.mono_set (Set.Ioi_subset_Ioi hxY)
  have hsplit : (∫ t in Set.Ioi x, (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹))
      = (∫ t in Set.Ioc x Y, (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹))
        + (∫ t in Set.Ioi Y, (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹)) := by
    have h := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := x) (b := Y))
        measurableSet_Ioi (hfx.mono_set Set.Ioc_subset_Ioi_self) hfY
    rwa [Set.Ioc_union_Ioi_eq_Ioi hxY] at h
  have hLHS : (∫ t in x..Y, (t : ℂ) ^ ρ * (((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) : ℝ) : ℂ))
      = ∫ t in Set.Ioc x Y, (t : ℂ) ^ (ρ - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹) := by
    rw [intervalIntegral.integral_of_le hxY]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    exact psiKfun_pointwise (by have h := Set.mem_Ioc.mp ht; linarith [h.1])
  rw [hLHS, hsplit]
  ring

end Commons.Analysis.Complex