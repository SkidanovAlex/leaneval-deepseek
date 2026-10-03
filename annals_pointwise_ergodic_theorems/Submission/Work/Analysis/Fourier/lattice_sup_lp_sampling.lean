import Mathlib
import Submission.Commons.Analysis.Fourier.band_limited_reproducing_kernel
import Submission.Commons.Analysis.CalderonZygmund.cz_shift
import Submission.Commons.Analysis.Fourier.schwartz_lattice_sum_bound

open MeasureTheory
open scoped FourierTransform ENNReal BigOperators

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Fourier
noncomputable section

/-- **Weighted Hölder / power-mean inequality** in `ℝ≥0∞`: for `p > 1` and measurable
`f, w : ℝ → ℝ≥0∞`,
`(∫ f w)^p ≤ (∫ w)^{p-1} · ∫ f^p w`. -/
theorem lintegral_mul_rpow_le_rpow_mul_lintegral {p : ℝ} (hp : 1 < p)
    {f w : ℝ → ENNReal} (hf : AEMeasurable f volume) (hw : AEMeasurable w volume) :
    (∫⁻ t, f t * w t) ^ p ≤ (∫⁻ t, w t) ^ (p - 1) * ∫⁻ t, f t ^ p * w t := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hpinv : (0:ℝ) < 1 / p := by positivity
  have hqinv : (0:ℝ) < 1 / (p / (p - 1)) := by positivity
  have hinv : (1:ℝ) / p + 1 / (p / (p - 1)) = 1 := by
    simpa only [one_div] using hpq.inv_add_inv_eq_one
  have hp1 : (1:ℝ) / p * p = 1 := by field_simp
  have hsub : (1:ℝ) / (p / (p - 1)) * p = p - 1 := by field_simp
  have h1 : ∀ t : ℝ, f t * w t ^ ((1:ℝ) / p) * w t ^ ((1:ℝ) / (p / (p - 1))) = f t * w t := by
    intro t
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg (1 / p) (1 / (p / (p - 1))) hpinv.le hqinv.le,
      hinv, ENNReal.rpow_one]
  have h2 : ∀ t : ℝ, (f t * w t ^ ((1:ℝ) / p)) ^ p = f t ^ p * w t := by
    intro t
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, hp1, ENNReal.rpow_one]
  have h3 : ∀ t : ℝ, (w t ^ ((1:ℝ) / (p / (p - 1)))) ^ (p / (p - 1)) = w t := by
    intro t
    have hx : (1:ℝ) / (p / (p - 1)) * (p / (p - 1)) = 1 := by
      rw [one_div]
      exact inv_mul_cancel₀ (by positivity)
    rw [← ENNReal.rpow_mul, hx, ENNReal.rpow_one]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
    (hf.mul (hw.pow_const ((1:ℝ) / p))) (hw.pow_const ((1:ℝ) / (p / (p - 1))))
  simp only [Pi.mul_apply] at hholder
  rw [lintegral_congr (fun t => h1 t), lintegral_congr (fun t => h2 t),
    lintegral_congr (fun t => h3 t)] at hholder
  calc (∫⁻ t, f t * w t) ^ p
      ≤ ((∫⁻ t, f t ^ p * w t) ^ (1 / p) *
            (∫⁻ t, w t) ^ (1 / (p / (p - 1)))) ^ p := ENNReal.rpow_le_rpow hholder hp0.le
    _ = (∫⁻ t, f t ^ p * w t) ^ ((1 / p) * p) *
          (∫⁻ t, w t) ^ ((1 / (p / (p - 1))) * p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.rpow_mul, ENNReal.rpow_mul]
    _ = (∫⁻ t, f t ^ p * w t) * (∫⁻ t, w t) ^ (p - 1) := by
        rw [hp1, hsub, ENNReal.rpow_one]
    _ = (∫⁻ t, w t) ^ (p - 1) * ∫⁻ t, f t ^ p * w t := by ring


private lemma inv_one_add_sq_le (n:ℕ) : (1+(n:ℝ)^2)⁻¹ ≤ 2 * (((n:ℝ)+1)^2)⁻¹ := by
  rw [inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ) < 1 + (n:ℝ)^2)]
  rw [show 2 * (((n:ℝ) + 1)^2)⁻¹ = 2 / ((n:ℝ) + 1)^2 by rw [div_eq_mul_inv]]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < ((n:ℝ)+1)^2)]
  nlinarith [sq_nonneg ((n:ℝ) - 1)]

private lemma summable_nat_inv_one_add_sq : Summable (fun n : ℕ => (1 + (n:ℝ)^2)⁻¹) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr one_lt_two
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h.mul_left 2)
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1), one_div, Real.rpow_ofNat]
  exact inv_one_add_sq_le n

private lemma summable_int_inv_one_add_sq : Summable (fun m : ℤ => (1 + (m:ℝ)^2)⁻¹) := by
  apply Summable.of_nat_of_neg
  · simpa using summable_nat_inv_one_add_sq
  · simpa using summable_nat_inv_one_add_sq

private noncomputable def phiW : ℤ → ℝ := fun m => (1 + (max (|(m:ℝ)| - 1) 0)^2)⁻¹

private lemma phiW_nn : ∀ m, 0 ≤ phiW m := fun m => by rw [phiW]; positivity

private lemma phiW_dom : ∀ m, phiW m ≤ 4 * (1 + (m:ℝ)^2)⁻¹ := by
  intro m
  rw [phiW]
  set A : ℝ := max (|(m:ℝ)| - 1) 0 with hA
  have hkey : 1 + (m:ℝ)^2 ≤ 4 * (1 + A^2) := by
    rcases lt_or_ge (1:ℝ) (|(m:ℝ)|) with h | h
    · rw [hA, max_eq_left (by linarith)]
      nlinarith [sq_nonneg (m:ℝ), sq_abs (m:ℝ), abs_nonneg (m:ℝ), h]
    · rw [hA, max_eq_right (by linarith)]
      nlinarith [sq_nonneg (|(m:ℝ)| - 1), abs_nonneg (m:ℝ), sq_abs (m:ℝ), h,
        sq_nonneg (|(m:ℝ)| - 4/3)]
  rw [show 4 * (1 + (m:ℝ)^2)⁻¹ = ((1 + (m:ℝ)^2) / 4)⁻¹ by rw [inv_div, div_eq_mul_inv]]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  nlinarith [hkey]

private lemma phiW_summable : Summable phiW :=
  Summable.of_nonneg_of_le phiW_nn phiW_dom (summable_int_inv_one_add_sq.mul_left 4)

private lemma phiW_pt (t : ℝ) : ∀ m : ℤ, (1 + ((m:ℝ) - t)^2)⁻¹ ≤ phiW (m - ⌊t⌋) := by
  intro m
  set s := t - ⌊t⌋ with hs
  have hs0 : 0 ≤ s := Int.fract_nonneg t
  have hs1 : s < 1 := Int.fract_lt_one t
  have hcast : (m:ℝ) - t = ((m - ⌊t⌋ : ℤ) : ℝ) - s := by rw [hs]; push_cast; ring
  set j : ℝ := ((m - ⌊t⌋ : ℤ) : ℝ) with hj
  have hA : max (|j| - 1) 0 ≤ |j - s| := by
    rcases lt_or_ge (1:ℝ) (|j|) with hgt | hle
    · rw [max_eq_left (by linarith)]
      rcases lt_or_ge j 0 with hjj | hjj
      · rw [abs_of_nonpos hjj.le, abs_of_nonpos (by linarith)]; rw [neg_sub]; linarith
      · rw [abs_of_nonneg hjj]
        have hj1 : 1 < j := by have := hgt; rwa [abs_of_nonneg hjj] at this
        rw [abs_of_nonneg (by linarith)]
        linarith
    · rw [max_eq_right (by linarith)]; positivity
  have hA2 : (max (|j| - 1) 0)^2 ≤ (j - s)^2 := by
    have h0 := le_max_right (|j| - 1) 0
    nlinarith [hA, abs_nonneg (j - s), sq_abs (j - s), h0]
  rw [phiW, hcast]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  nlinarith [hA2]

private lemma count_weight_le : ∃ B0 : ℝ, 0 < B0 ∧
    ∀ t : ℝ, (∑' m : ℤ, (1 + ((m : ℝ) - t) ^ 2)⁻¹ ≤ B0 ∧
      Summable (fun m : ℤ => (1 + ((m : ℝ) - t) ^ 2)⁻¹)) := by
  refine ⟨∑' m : ℤ, phiW m, ?_, ?_⟩
  · have hφ0 : 0 < phiW 0 := by rw [phiW]; norm_num
    exact lt_of_lt_of_le hφ0 (phiW_summable.le_tsum 0 (fun j hj => phiW_nn j))
  · intro t
    have hg : Summable (fun m : ℤ => phiW (m - ⌊t⌋)) :=
      phiW_summable.comp_injective (fun a b h => by omega)
    have hf : Summable (fun m : ℤ => (1 + ((m:ℝ) - t)^2)⁻¹) :=
      Summable.of_nonneg_of_le (fun m => by positivity) (fun m => phiW_pt t m) hg
    refine ⟨?_, hf⟩
    calc ∑' m : ℤ, (1 + ((m:ℝ) - t)^2)⁻¹ ≤ ∑' m : ℤ, phiW (m - ⌊t⌋) :=
          Summable.tsum_le_tsum (fun m => phiW_pt t m) hf hg
      _ = ∑' j : ℤ, phiW j := Equiv.tsum_eq (Equiv.addRight (-⌊t⌋)) phiW




/-- Weighted Hölder / power-mean inequality for a general measure. -/
theorem lintegral_mul_rpow_le_rpow_mul_lintegral_measure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {p : ℝ} (hp : 1 < p)
    {f w : α → ENNReal} (hf : AEMeasurable f μ) (hw : AEMeasurable w μ) :
    (∫⁻ t, f t * w t ∂μ) ^ p ≤ (∫⁻ t, w t ∂μ) ^ (p - 1) * ∫⁻ t, f t ^ p * w t ∂μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hpinv : (0:ℝ) < 1 / p := by positivity
  have hqinv : (0:ℝ) < 1 / (p / (p - 1)) := by positivity
  have hinv : (1:ℝ) / p + 1 / (p / (p - 1)) = 1 := by
    simpa only [one_div] using hpq.inv_add_inv_eq_one
  have hp1 : (1:ℝ) / p * p = 1 := by field_simp
  have hsub : (1:ℝ) / (p / (p - 1)) * p = p - 1 := by field_simp
  have h1 : ∀ t : α, f t * w t ^ ((1:ℝ) / p) * w t ^ ((1:ℝ) / (p / (p - 1))) = f t * w t := by
    intro t
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg (1 / p) (1 / (p / (p - 1))) hpinv.le hqinv.le,
      hinv, ENNReal.rpow_one]
  have h2 : ∀ t : α, (f t * w t ^ ((1:ℝ) / p)) ^ p = f t ^ p * w t := by
    intro t
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, hp1, ENNReal.rpow_one]
  have h3 : ∀ t : α, (w t ^ ((1:ℝ) / (p / (p - 1)))) ^ (p / (p - 1)) = w t := by
    intro t
    have hx : (1:ℝ) / (p / (p - 1)) * (p / (p - 1)) = 1 := by
      rw [one_div]
      exact inv_mul_cancel₀ (by positivity)
    rw [← ENNReal.rpow_mul, hx, ENNReal.rpow_one]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (hf.mul (hw.pow_const ((1:ℝ) / p))) (hw.pow_const ((1:ℝ) / (p / (p - 1))))
  simp only [Pi.mul_apply] at hholder
  rw [lintegral_congr (fun t => h1 t), lintegral_congr (fun t => h2 t),
    lintegral_congr (fun t => h3 t)] at hholder
  calc (∫⁻ t, f t * w t ∂μ) ^ p
      ≤ ((∫⁻ t, f t ^ p * w t ∂μ) ^ (1 / p) *
            (∫⁻ t, w t ∂μ) ^ (1 / (p / (p - 1)))) ^ p := ENNReal.rpow_le_rpow hholder hp0.le
    _ = (∫⁻ t, f t ^ p * w t ∂μ) ^ ((1 / p) * p) *
          (∫⁻ t, w t ∂μ) ^ ((1 / (p / (p - 1))) * p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.rpow_mul, ENNReal.rpow_mul]
    _ = (∫⁻ t, f t ^ p * w t ∂μ) * (∫⁻ t, w t ∂μ) ^ (p - 1) := by
        rw [hp1, hsub, ENNReal.rpow_one]
    _ = (∫⁻ t, w t ∂μ) ^ (p - 1) * ∫⁻ t, f t ^ p * w t ∂μ := by ring

/-- Schwartz functions decay like `(1 + x ^ 2)⁻¹`. -/
theorem schwartz_decay_one_add_sq (φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖φ x‖ ≤ C / (1 + x ^ 2) := by
  set S0 : ℝ := SchwartzMap.seminorm ℂ 0 0 φ with hS0
  set S2 : ℝ := SchwartzMap.seminorm ℂ 2 0 φ with hS2
  refine ⟨max (S0 + S2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have h0 : ‖φ x‖ ≤ S0 := SchwartzMap.norm_le_seminorm ℂ φ x
  have h2 : ‖x‖ ^ 2 * ‖φ x‖ ≤ S2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ φ 2 x
  have hx2 : ‖x‖ ^ 2 = x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hx2] at h2
  have hsum : (1 + x^2) * ‖φ x‖ ≤ S0 + S2 := by nlinarith [h0, h2]
  have hle : ‖φ x‖ ≤ max (S0 + S2) 1 / (1 + x^2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsum, le_max_left (S0+S2) 1, le_max_right (S0+S2) 1]
  simpa only [div_eq_mul_inv] using hle

end
end Commons.Analysis.Fourier
