import Mathlib
import Submission.Port.Aesm

/-!
# Cauchy–Schwarz for the `ℓ²(ℤ)` pairing

`∑ x, u x * conj (v x)` is the `ℓ²(ℤ; ℂ)` pairing of `u` and `v`.  Its modulus is bounded by
the product of the two `ℒ²` seminorms with respect to counting measure on `ℤ`.

This is the elementary (Hölder at exponent `2`) input used by the "siv" (small-improving)
sections of Area `A4`.
-/

namespace Work.KMTAreas.A4

open MeasureTheory ENNReal
open scoped NNReal

/-- **Finiteness of the square sum from an `ℒ²` bound.**  If `eLpNorm u 2 count` is bounded by
`ENNReal.ofReal A`, then `∑' x, ‖u x‖ ^ 2` converges.  (An `ℒ²` function against counting
measure is a square summable sequence.) -/
theorem summable_norm_sq_of_eLpNorm_le {u : ℤ → ℂ} {A : ℝ}
    (hu : MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal A) :
    Summable (fun x : ℤ => ‖u x‖ ^ 2) := by
  have hlt : MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count < ∞ :=
    lt_of_le_of_lt hu ENNReal.ofReal_lt_top
  have h2 : (∑' x : ℤ, ‖u x‖ₑ ^ (((2:ℕ):ℝ))) < ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2:ℝ≥0∞))
      (by norm_num) (by norm_num) hlt
    rw [lintegral_count] at h
    simpa [ENNReal.toReal_ofNat] using h
  have h3 : (∑' x : ℤ, ENNReal.ofReal (‖u x‖ ^ 2)) < ∞ := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun x => ?_) h2
    apply le_of_eq
    rw [← Real.rpow_natCast (‖u x‖) 2, ← ofReal_norm,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ ((2:ℕ):ℝ))]
  have h4 : Summable (fun x : ℤ => (Real.toNNReal (‖u x‖ ^ 2) : ℝ≥0)) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp h3.ne
  have h5 : Summable (fun x : ℤ => ((Real.toNNReal (‖u x‖ ^ 2) : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr h4
  exact h5.congr (fun x => Real.coe_toNNReal (‖u x‖ ^ 2) (sq_nonneg _))

/-- **The value of the `ℒ²` seminorm against counting measure.**  For a square summable
`u : ℤ → ℂ`, `eLpNorm u 2 count = ofReal ((∑ x, ‖u x‖^2) ^ (1/2))`. -/
theorem eLpNorm_two_count_eq_ofReal {u : ℤ → ℂ}
    (hu : Summable (fun x : ℤ => ‖u x‖ ^ 2)) :
    MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count
      = ENNReal.ofReal ((∑' x : ℤ, ‖u x‖ ^ 2) ^ (1 / 2 : ℝ)) := by
  have hst : (∑' x : ℤ, ‖u x‖ ^ (2 : ℝ)) = ∑' x : ℤ, ‖u x‖ ^ 2 :=
    tsum_congr fun x => Real.rpow_two (‖u x‖)
  have hsumm : Summable (fun n : ℤ => ‖u n‖ ^ (2 : ℝ)) := by
    refine hu.congr fun n => ?_
    rw [Real.rpow_two]
  have h1 : (∑' x : ℤ, ‖u x‖ₑ ^ (2 : ℝ)) = ENNReal.ofReal (∑' x : ℤ, ‖u x‖ ^ (2 : ℝ)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => Real.rpow_nonneg (norm_nonneg (u n)) 2) hsumm]
    refine tsum_congr fun n => ?_
    rw [← ofReal_norm (u n),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  calc MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count
      = (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) ^ (1 / 2 : ℝ) := by
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num)]
        norm_num
    _ = (∑' x : ℤ, ‖u x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [MeasureTheory.lintegral_count]
    _ = (ENNReal.ofReal (∑' x : ℤ, ‖u x‖ ^ (2 : ℝ))) ^ (1 / 2 : ℝ) := by rw [h1]
    _ = ENNReal.ofReal ((∑' x : ℤ, ‖u x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg
          (tsum_nonneg fun n => Real.rpow_nonneg (norm_nonneg (u n)) 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ = ENNReal.ofReal ((∑' x : ℤ, ‖u x‖ ^ 2) ^ (1 / 2 : ℝ)) := by rw [hst]

/-- **The squared `ℓ²` bound.**  An `ℒ²(ℤ, count)` bound `≤ ofReal A` for nonnegative `A`
bounds the sum of squared moduli by `A ^ 2`. -/
theorem tsum_norm_sq_le_sq_of_eLpNorm_le {u : ℤ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hu : MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal A) :
    (∑' x : ℤ, ‖u x‖ ^ 2) ≤ A ^ 2 := by
  have hsu := summable_norm_sq_of_eLpNorm_le hu
  have hle := hu
  rw [eLpNorm_two_count_eq_ofReal hsu] at hle
  have hsqrt : (∑' x : ℤ, ‖u x‖ ^ 2) ^ (1 / 2 : ℝ) ≤ A :=
    (ENNReal.ofReal_le_ofReal_iff hA).mp hle
  have h0 : (0 : ℝ) ≤ ∑' x : ℤ, ‖u x‖ ^ 2 := tsum_nonneg fun x => sq_nonneg _
  calc (∑' x : ℤ, ‖u x‖ ^ 2)
      = ((∑' x : ℤ, ‖u x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt h0]
    _ ≤ A ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg h0 _) hsqrt 2

/-- **Cauchy–Schwarz for the `ℓ²(ℤ; ℂ)` pairing.**  If `u` and `v` are bounded in `ℒ²` (against
counting measure on `ℤ`) by `ofReal A` and `ofReal A'` with `A, A' ≥ 0`, then the pairing
`∑ x, u x * conj (v x)` is bounded by `A * A'` in modulus. -/
theorem sivPairingCS {u v : ℤ → ℂ} {A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hu : MeasureTheory.eLpNorm u 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal A)
    (hv : MeasureTheory.eLpNorm v 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal A') :
    ‖∑' x : ℤ, u x * star (v x)‖ ≤ A * A' := by
  have hsu : Summable (fun x : ℤ => ‖u x‖ ^ 2) := summable_norm_sq_of_eLpNorm_le hu
  have hsv : Summable (fun x : ℤ => ‖v x‖ ^ 2) := summable_norm_sq_of_eLpNorm_le hv
  have hbu : (∑' x : ℤ, ‖u x‖ ^ 2) ≤ A ^ 2 := tsum_norm_sq_le_sq_of_eLpNorm_le hA hu
  have hbv : (∑' x : ℤ, ‖v x‖ ^ 2) ≤ A' ^ 2 := tsum_norm_sq_le_sq_of_eLpNorm_le hA' hv
  have hst_u : (∑' x : ℤ, ‖u x‖ ^ (2 : ℝ)) = ∑' x : ℤ, ‖u x‖ ^ 2 :=
    tsum_congr fun x => Real.rpow_two (‖u x‖)
  have hst_v : (∑' x : ℤ, ‖v x‖ ^ (2 : ℝ)) = ∑' x : ℤ, ‖v x‖ ^ 2 :=
    tsum_congr fun x => Real.rpow_two (‖v x‖)
  -- Hölder at exponent `2`
  obtain ⟨hsum_norm, hCS⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := 2) (q := 2) Real.HolderConjugate.two_two
    (fun x => norm_nonneg (u x)) (fun x => norm_nonneg (v x))
    (by simpa [Real.rpow_two] using hsu) (by simpa [Real.rpow_two] using hsv)
  have hCS' : (∑' x : ℤ, ‖u x‖ * ‖v x‖) ≤
      (∑' x : ℤ, ‖u x‖ ^ 2) ^ (1 / 2 : ℝ) * (∑' x : ℤ, ‖v x‖ ^ 2) ^ (1 / 2 : ℝ) := by
    simpa only [hst_u, hst_v] using hCS
  have hu2 : (∑' x : ℤ, ‖u x‖ ^ 2) ^ (1 / 2 : ℝ) ≤ A := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (∑' x : ℤ, ‖u x‖ ^ 2) ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt hbu
      _ = A := Real.sqrt_sq hA
  have hv2 : (∑' x : ℤ, ‖v x‖ ^ 2) ^ (1 / 2 : ℝ) ≤ A' := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (∑' x : ℤ, ‖v x‖ ^ 2) ≤ Real.sqrt (A' ^ 2) := Real.sqrt_le_sqrt hbv
      _ = A' := Real.sqrt_sq hA'
  have hw : (∑' x : ℤ, ‖u x‖ * ‖v x‖) ≤ A * A' :=
    hCS'.trans (mul_le_mul hu2 hv2
      (Real.rpow_nonneg (tsum_nonneg fun x => sq_nonneg _) _) hA)
  have hnorm_summ : Summable (fun x : ℤ => ‖u x * star (v x)‖) := by
    simpa [norm_mul, norm_star] using hsum_norm
  calc ‖∑' x : ℤ, u x * star (v x)‖
      ≤ ∑' x : ℤ, ‖u x * star (v x)‖ := norm_tsum_le_tsum_norm hnorm_summ
    _ = ∑' x : ℤ, ‖u x‖ * ‖v x‖ := tsum_congr fun x => by rw [norm_mul, norm_star]
    _ ≤ A * A' := hw

end Work.KMTAreas.A4
