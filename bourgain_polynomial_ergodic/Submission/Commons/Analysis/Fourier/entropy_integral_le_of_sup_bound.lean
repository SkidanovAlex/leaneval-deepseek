import Mathlib
import Submission.Commons.MeasureTheory.Integral.lintegral_Ioi_rpow_eq

open MeasureTheory Set
open scoped ENNReal Topology

namespace Commons.Analysis.Fourier

/-- Improper integral of `(b/x)^p` over `(c, ∞)`, `p > 1`, `b ≥ 0`, `c > 0`. -/
private theorem lintegral_Ioi_ofReal_div_rpow (b p c : ℝ) (hb : 0 ≤ b) (hp : 1 < p) (hc : 0 < c) :
    (∫⁻ l in Set.Ioi c, (ENNReal.ofReal (b / l)) ^ p)
      = ENNReal.ofReal (b ^ p * c ^ (1 - p) / (p - 1)) := by
  have hppos : 0 ≤ p := by linarith
  have hpt : ∀ l ∈ Set.Ioi c, (ENNReal.ofReal (b / l)) ^ p
      = ENNReal.ofReal (b ^ p) * ENNReal.ofReal (l ^ (-p)) := by
    intro l hl
    have hl0 : 0 < l := lt_trans hc hl
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hppos]
    rw [Real.div_rpow hb (le_of_lt hl0) p, div_eq_mul_inv]
    rw [← Real.rpow_neg (le_of_lt hl0) p]
    rw [ENNReal.ofReal_mul (by positivity)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [Commons.MeasureTheory.Integral.lintegral_Ioi_rpow_eq (-p) c (by linarith) hc]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h1 : -p + 1 = 1 - p := by ring
  rw [h1]
  rw [show (-c ^ (1 - p) / (1 - p)) = c ^ (1 - p) / (p - 1) from by
    rw [div_eq_div_iff (by linarith : (1:ℝ) - p ≠ 0) (by linarith : (p:ℝ) - 1 ≠ 0)]
    ring]
  ring

/-- Elementary real identity behind the split point `l₀ = G·K^{-1/r}`. -/
private theorem sqrt_mul_rpow_neg_add_div_eq (K G r : ℝ) (hK : 0 < K) (hG : 0 < G) (hr : 2 < r) :
    Real.sqrt K * (G * K ^ (-(1 / r))) + G ^ (r / 2) * (G * K ^ (-(1 / r))) ^ (1 - r / 2) / (r / 2 - 1)
      = (1 + 2 / (r - 2)) * K ^ (1 / 2 - 1 / r) * G := by
  have hK0 : 0 ≤ K := le_of_lt hK
  have hG0 : 0 ≤ G := le_of_lt hG
  have hr0 : r ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < r)
  have hsqrt : Real.sqrt K = K ^ (1/2 : ℝ) := Real.sqrt_eq_rpow K
  have hKpow : K ^ (1/2 : ℝ) * K ^ (-(1 / r)) = K ^ (1 / 2 - 1 / r) := by
    rw [← Real.rpow_add hK]; congr 1
  have hrr : r / 2 + (1 - r / 2) = (1:ℝ) := by ring
  have hGpow : G ^ (r / 2) * G ^ (1 - r / 2) = G := by
    rw [← Real.rpow_add hG]
    rw [hrr, Real.rpow_one]
  have hexp2 : (-(1 / r)) * (1 - r / 2) = 1 / 2 - 1 / r := by
    field_simp
    ring
  have hl0pow : (G * K ^ (-(1 / r))) ^ (1 - r / 2) = G ^ (1 - r / 2) * K ^ (1 / 2 - 1 / r) := by
    rw [Real.mul_rpow (z := 1 - r / 2) hG0 (Real.rpow_nonneg hK0 _)]
    congr 1
    rw [← Real.rpow_mul hK0]
    rw [hexp2]
  rw [hsqrt, hl0pow]
  have hkey : G ^ (r / 2) * (G ^ (1 - r / 2) * K ^ (1 / 2 - 1 / r))
      = G * K ^ (1 / 2 - 1 / r) := by
    rw [← mul_assoc, hGpow]
  rw [hkey]
  have hsqrt2 : K ^ (1/2:ℝ) * (G * K ^ (-(1/r))) = G * K ^ (1/2 - 1/r) := by
    rw [← hKpow]; ring
  rw [hsqrt2]
  field_simp

theorem entropy_integral_le_of_sup_bound (M : ℝ → ENNReal) {K r G : ℝ} (hK : 0 ≤ K) (hr : 2 < r) (hG : 0 ≤ G) (hsup : ∀ l : ℝ, 0 < l → ENNReal.ofReal l * M l ^ (1/r) ≤ ENNReal.ofReal G) : (∫⁻ l in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K)) (M l ^ (1/2:ℝ))) ≤ ENNReal.ofReal ((1 + 2/(r-2)) * K^(1/2 - 1/r) * G) := by
  rcases lt_or_eq_of_le hK with hKpos | hK0
  · rcases lt_or_eq_of_le hG with hGpos | hG0
    · -- main case
      have hrpos : 0 < r := by linarith
      have hr0 : r ≠ 0 := ne_of_gt hrpos
      have hr2pos : 0 ≤ r/2 := by linarith
      have hr2gt1 : 1 < r/2 := by linarith
      set l0 : ℝ := G * K ^ (-(1/r)) with hl0def
      have hl0pos : 0 < l0 := by
        rw [hl0def]
        exact mul_pos hGpos (Real.rpow_pos_of_pos hKpos _)
      have hbound : ∀ l, 0 < l →
          min (ENNReal.ofReal (Real.sqrt K)) (M l ^ (1/2:ℝ)) ≤ (ENNReal.ofReal (G/l))^(r/2) := by
        intro l hl
        have h1 : M l ^ (1/r) ≤ ENNReal.ofReal (G/l) := by
          rw [ENNReal.ofReal_div_of_pos hl]
          rw [ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hl)))
            (Or.inr ENNReal.ofReal_ne_top)]
          simpa [mul_comm] using hsup l hl
        have h2 : M l ^ (1/2:ℝ) ≤ (ENNReal.ofReal (G/l))^(r/2) := by
          have step : M l ^ (1/2:ℝ) = (M l ^ (1/r)) ^ (r/2) := by
            rw [← ENNReal.rpow_mul]
            congr 1
            field_simp
          rw [step]
          exact ENNReal.rpow_le_rpow h1 hr2pos
        exact le_trans (min_le_right _ _) h2
      have hsplit : (∫⁻ l in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K)) (M l ^ (1/2:ℝ)))
          = (∫⁻ l in Set.Ioc 0 l0, min (ENNReal.ofReal (Real.sqrt K)) (M l ^ (1/2:ℝ)))
            + (∫⁻ l in Set.Ioi l0, min (ENNReal.ofReal (Real.sqrt K)) (M l ^ (1/2:ℝ))) := by
        rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 l0 ∪ Set.Ioi l0 from by
          ext x; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]; constructor
          · intro hx
            by_cases h : x ≤ l0
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr (lt_of_not_ge h)
          · rintro (⟨hx, _⟩ | hx)
            · exact hx
            · exact lt_trans hl0pos hx]
        rw [lintegral_union measurableSet_Ioi (by
          rw [Set.disjoint_left]
          intro x hxA hxB
          exact absurd hxB (not_lt.mpr hxA.2))]
      have piece1 : (∫⁻ l in Set.Ioc (0:ℝ) l0, ENNReal.ofReal (Real.sqrt K))
          = ENNReal.ofReal (Real.sqrt K * l0) := by
        rw [lintegral_const]
        simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc,
          sub_zero]
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg K)]
      have piece2 : (∫⁻ l in Set.Ioi l0, (ENNReal.ofReal (G/l))^(r/2))
          = ENNReal.ofReal (G^(r/2) * l0^(1-r/2)/(r/2-1)) :=
        lintegral_Ioi_ofReal_div_rpow G (r/2) l0 (le_of_lt hGpos) hr2gt1 hl0pos
      calc (∫⁻ l in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K)) (M l ^ (1/2:ℝ)))
          = (∫⁻ l in Set.Ioc 0 l0, min (ENNReal.ofReal (Real.sqrt K)) (M l ^ (1/2:ℝ)))
              + (∫⁻ l in Set.Ioi l0, min (ENNReal.ofReal (Real.sqrt K)) (M l ^ (1/2:ℝ))) := hsplit
        _ ≤ (∫⁻ l in Set.Ioc 0 l0, ENNReal.ofReal (Real.sqrt K))
              + (∫⁻ l in Set.Ioi l0, (ENNReal.ofReal (G/l))^(r/2)) := by
            apply add_le_add
            · exact lintegral_mono (fun l => min_le_left _ _)
            · apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
              exact hbound l (lt_trans hl0pos hl)
        _ = ENNReal.ofReal (Real.sqrt K * l0)
              + ENNReal.ofReal (G^(r/2) * l0^(1-r/2)/(r/2-1)) := by rw [piece1, piece2]
        _ = ENNReal.ofReal (Real.sqrt K * l0 + G^(r/2) * l0^(1-r/2)/(r/2-1)) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ = ENNReal.ofReal ((1 + 2/(r-2)) * K^(1/2 - 1/r) * G) := by
            congr 1
            rw [hl0def]
            exact sqrt_mul_rpow_neg_add_div_eq K G r hKpos hGpos hr
    · -- G = 0
      have hrpos : 0 < r := by linarith
      have hr0 : r ≠ 0 := ne_of_gt hrpos
      have hM0 : ∀ l, 0 < l → M l = 0 := by
        intro l hl
        have h := hsup l hl
        rw [← hG0] at h
        simp only [ENNReal.ofReal_zero] at h
        have hz : M l ^ (1/r) = 0 := by
          have hprod : ENNReal.ofReal l * M l ^ (1/r) = 0 := le_antisymm h bot_le
          rcases mul_eq_zero.mp hprod with h1 | h1
          · exact absurd h1 (ne_of_gt (ENNReal.ofReal_pos.mpr hl))
          · exact h1
        have hcancel : (1/r) * r = 1 := by rw [one_div, inv_mul_cancel₀ hr0]
        calc M l = (M l ^ (1/r)) ^ r := by
              rw [← ENNReal.rpow_mul, hcancel, ENNReal.rpow_one]
          _ = 0 := by rw [hz, ENNReal.zero_rpow_of_pos hrpos]
      have hzero : ∀ᵐ l ∂(volume.restrict (Set.Ioi (0:ℝ))),
          min (ENNReal.ofReal (Real.sqrt K)) (M l ^ (1/2:ℝ)) = 0 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
        rw [hM0 l hl, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)]
        simp
      rw [← hG0]
      simp only [mul_zero, ENNReal.ofReal_zero]
      rw [lintegral_congr_ae hzero]
      simp
  · -- K = 0
    rw [← hK0]
    have hz : (0:ℝ) ^ (1/2 - 1/r) = 0 := by
      apply Real.zero_rpow
      have h : 1/r < 1/2 := one_div_lt_one_div_of_lt (by norm_num) hr
      linarith
    rw [hz]
    simp [Real.sqrt_zero]

end Commons.Analysis.Fourier
