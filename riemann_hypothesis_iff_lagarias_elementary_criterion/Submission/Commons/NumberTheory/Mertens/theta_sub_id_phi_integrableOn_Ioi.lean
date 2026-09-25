import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Chebyshev

namespace Commons.NumberTheory.Mertens

open MeasureTheory Set Filter
open scoped Topology

/-- For `1 < s` and `1 ≤ c`, the function `t ↦ (log t)^n / t^s` is integrable on `(c, ∞)`. -/
theorem integrableOn_Ioi_log_pow_div_rpow {n : ℕ} {s c : ℝ} (hs : 1 < s) (hc : 1 ≤ c) :
    IntegrableOn (fun t : ℝ => (Real.log t) ^ n / t ^ s) (Ioi c) := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  rcases n with _ | k
  · refine (integrableOn_Ioi_rpow_of_lt (show (-s) < -1 by linarith) hcpos).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have hct : c < t := ht
    have ht0 : 0 ≤ t := by linarith
    show t ^ (-s) = Real.log t ^ 0 / t ^ s
    rw [Real.rpow_neg ht0]
    simp
  · have hs1 : 0 < s - 1 := by linarith
    set ε : ℝ := (s - 1) / (2 * ((k + 1 : ℕ) : ℝ)) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hs1 (by positivity)
    have hεmul : ε * ((k + 1 : ℕ) : ℝ) = (s - 1) / 2 := by
      rw [hεdef]; field_simp
    have key : ∀ t ∈ Ioi c,
        ‖(Real.log t) ^ (k+1) / t ^ s‖ ≤ (ε ^ (k+1))⁻¹ * t ^ (-(s + 1) / 2) := by
      intro t ht
      have htc : c < t := ht
      have ht1 : 1 < t := lt_of_le_of_lt hc htc
      have ht0 : 0 < t := lt_trans zero_lt_one ht1
      have hlog : 0 < Real.log t := Real.log_pos ht1
      have htspos : 0 < t ^ s := Real.rpow_pos_of_pos ht0 s
      have hnum : 0 ≤ (Real.log t) ^ (k+1) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum htspos.le)]
      have hb : Real.log t ≤ t ^ ε / ε := Real.log_le_rpow_div ht0.le hεpos
      have hpow : (Real.log t) ^ (k+1) ≤ (t ^ ε / ε) ^ (k+1) :=
        pow_le_pow_left₀ hlog.le hb (k+1)
      have hrew : (t ^ ε / ε) ^ (k+1) = t ^ ((s-1)/2) / ε ^ (k+1) := by
        have h2 : (t ^ ε) ^ (k+1) = t ^ ((s-1)/2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le, hεmul]
        rw [div_pow, h2]
      rw [hrew] at hpow
      have hstep := div_le_div_of_nonneg_right hpow htspos.le
      have hA : (s-1)/2 - s = -(s+1)/2 := by ring
      have h1 : t ^ ((s-1)/2) / t ^ s = t ^ (-(s+1)/2) := by
        rw [← Real.rpow_sub ht0, hA]
      have hc_eq : (t ^ ((s-1)/2) / ε ^ (k+1)) / t ^ s
          = (ε ^ (k+1))⁻¹ * t ^ (-(s+1)/2) := by
        calc (t ^ ((s-1)/2) / ε ^ (k+1)) / t ^ s
            = (t ^ ((s-1)/2) / t ^ s) / ε ^ (k+1) := by ring
          _ = t ^ (-(s+1)/2) / ε ^ (k+1) := by rw [h1]
          _ = (ε ^ (k+1))⁻¹ * t ^ (-(s+1)/2) := by rw [div_eq_inv_mul]
      exact hstep.trans_eq hc_eq
    have hgint : IntegrableOn (fun t : ℝ => (ε ^ (k+1))⁻¹ * t ^ (-(s+1)/2)) (Ioi c) :=
      (integrableOn_Ioi_rpow_of_lt (show -(s+1)/2 < -1 by linarith) hcpos).const_mul _
    have hmeas : AEStronglyMeasurable (fun t : ℝ => (Real.log t) ^ (k+1) / t ^ s)
        (volume.restrict (Ioi c)) :=
      ((Real.measurable_log.pow_const (k+1)).div
        ((Real.continuous_rpow_const (le_of_lt (lt_trans zero_lt_one hs))).measurable)).aestronglyMeasurable
    rw [IntegrableOn] at hgint ⊢
    refine hgint.mono hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall (fun t ht => ?_)
    have hct : c < t := ht
    have ht0 : 0 < t := by linarith
    have hgnn : 0 ≤ (ε ^ (k+1))⁻¹ * t ^ (-(s+1)/2) :=
      mul_nonneg (le_of_lt (inv_pos.mpr (pow_pos hεpos _))) (le_of_lt (Real.rpow_pos_of_pos ht0 _))
    have hgnorm : ‖(ε ^ (k+1))⁻¹ * t ^ (-(s+1)/2)‖ = (ε ^ (k+1))⁻¹ * t ^ (-(s+1)/2) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hgnn]
    rw [hgnorm]
    exact key t ht

theorem theta_sub_id_phi_integrableOn_Ioi {a₀ : ℝ} (ha0 : 2 ≤ a₀) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, a₀ ≤ t → |Chebyshev.theta t - t| ≤ C * Real.sqrt t * (Real.log t) ^ 10) :
    ∀ a : ℝ, a₀ ≤ a →
      MeasureTheory.IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) *
        ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) (Set.Ioi a) MeasureTheory.volume := by
  intro a ha
  have ha2 : 2 ≤ a := le_trans ha0 ha
  have h9 : IntegrableOn (fun t : ℝ => (Real.log t) ^ 9 / t ^ (3/2 : ℝ)) (Set.Ioi a) :=
    integrableOn_Ioi_log_pow_div_rpow (n := 9) (s := (3/2 : ℝ)) (c := a)
      (by norm_num) (by linarith)
  have h8 : IntegrableOn (fun t : ℝ => (Real.log t) ^ 8 / t ^ (3/2 : ℝ)) (Set.Ioi a) :=
    integrableOn_Ioi_log_pow_div_rpow (n := 8) (s := (3/2 : ℝ)) (c := a)
      (by norm_num) (by linarith)
  have hg : IntegrableOn (fun t : ℝ => C * ((Real.log t) ^ 9 / t ^ (3/2 : ℝ)
      + (Real.log t) ^ 8 / t ^ (3/2 : ℝ))) (Set.Ioi a) :=
    (h9.add h8).const_mul C
  have hpt : ∀ t ∈ Set.Ioi a,
      ‖(Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))‖
        ≤ C * ((Real.log t) ^ 9 / t ^ (3/2 : ℝ) + (Real.log t) ^ 8 / t ^ (3/2 : ℝ)) := by
    intro t ht
    have hta : a < t := ht
    have h2t : 2 < t := lt_of_le_of_lt ha2 hta
    have ht0 : 0 < t := by linarith
    have ht1 : 1 < t := by linarith
    have hlog : 0 < Real.log t := Real.log_pos ht1
    have htne : t ≠ 0 := ne_of_gt ht0
    have hLne : Real.log t ≠ 0 := ne_of_gt hlog
    have hfrac : 0 ≤ (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by positivity
    have hnorm : ‖(Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))‖
        = |Chebyshev.theta t - t| * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hfrac]
    rw [hnorm]
    have hb_t : |Chebyshev.theta t - t| ≤ C * Real.sqrt t * (Real.log t) ^ 10 :=
      hb t (by linarith)
    have hstep1 : |Chebyshev.theta t - t| * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
        ≤ C * Real.sqrt t * (Real.log t) ^ 10 * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) :=
      mul_le_mul_of_nonneg_right hb_t hfrac
    have hsqrt_id : Real.sqrt t / t ^ 2 = 1 / t ^ (3/2 : ℝ) := by
      have h1 : Real.sqrt t / t ^ 2 = t ^ (-(3/2:ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast t 2, ← Real.rpow_sub ht0,
          show (1:ℝ)/2 - ((2:ℕ):ℝ) = -(3/2:ℝ) by norm_num]
      have h2 : (1:ℝ) / t ^ (3/2:ℝ) = t ^ (-(3/2:ℝ)) := by
        rw [one_div, Real.rpow_neg (le_of_lt ht0)]
      rw [h1, h2]
    have hstep2 : C * Real.sqrt t * (Real.log t) ^ 10 * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
        = C * ((Real.log t) ^ 9 / t ^ (3/2 : ℝ) + (Real.log t) ^ 8 / t ^ (3/2 : ℝ)) := by
      have hA : C * Real.sqrt t * (Real.log t) ^ 10 * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
          = C * (Real.log t) ^ 8 * (Real.log t + 1) * (Real.sqrt t / t ^ 2) := by
        field_simp
      rw [hA, hsqrt_id]
      ring_nf
    exact hstep1.trans (le_of_eq hstep2)
  have hmeas_f : Measurable (fun t : ℝ => (Chebyshev.theta t - t) *
      ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) := by
    have h1 : Measurable fun t : ℝ => Chebyshev.theta t - t :=
      (Chebyshev.theta_mono.measurable).sub measurable_id
    have h2 : Measurable fun t : ℝ => (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by
      refine Measurable.div ?_ ?_
      · exact Real.measurable_log.add_const 1
      · exact (measurable_id.pow_const 2).mul (Real.measurable_log.pow_const 2)
    exact h1.mul h2
  rw [IntegrableOn] at hg ⊢
  refine hg.mono hmeas_f.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall (fun t ht => ?_)
  have hta : a < t := ht
  have ht0 : 0 < t := by linarith
  have hlog : 0 ≤ Real.log t := le_of_lt (Real.log_pos (by linarith : 1 < t))
  have htp : 0 < t ^ (3/2 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hsum : 0 ≤ (Real.log t)^9 / t^(3/2:ℝ) + (Real.log t)^8 / t^(3/2:ℝ) := by
    have h1 : 0 ≤ (Real.log t)^9 / t^(3/2:ℝ) := div_nonneg (pow_nonneg hlog 9) (le_of_lt htp)
    have h2 : 0 ≤ (Real.log t)^8 / t^(3/2:ℝ) := div_nonneg (pow_nonneg hlog 8) (le_of_lt htp)
    linarith
  have hgnorm : ‖C * ((Real.log t)^9 / t^(3/2:ℝ) + (Real.log t)^8 / t^(3/2:ℝ))‖
      = C * ((Real.log t)^9 / t^(3/2:ℝ) + (Real.log t)^8 / t^(3/2:ℝ)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hsum)]
  rw [hgnorm]
  exact hpt t ht

end Commons.NumberTheory.Mertens