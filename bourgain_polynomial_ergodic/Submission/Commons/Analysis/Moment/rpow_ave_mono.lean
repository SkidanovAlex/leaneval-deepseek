import Mathlib.Analysis.MeanInequalitiesPow

namespace Commons.Analysis.Moment

open Finset

theorem rpow_ave_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : 0 < Fintype.card ι)
    (Y : ι → ℝ) (hY : ∀ i, 0 ≤ Y i) {q p : ℝ} (hq : 0 < q) (hqp : q ≤ p) :
    ((∑ i, (Y i) ^ q) / (Fintype.card ι : ℝ)) ^ (1 / q)
      ≤ ((∑ i, (Y i) ^ p) / (Fintype.card ι : ℝ)) ^ (1 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le hq hqp
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hι
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
  set A : ℝ := (∑ i, (Y i) ^ q) / (Fintype.card ι : ℝ) with hA
  set B : ℝ := (∑ i, (Y i) ^ p) / (Fintype.card ι : ℝ) with hB
  have hAge : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hY i) q)) hcard_pos.le
  have hBge : 0 ≤ B := by
    rw [hB]
    exact div_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hY i) p)) hcard_pos.le
  have hAeq : A = ∑ i, (1 / (Fintype.card ι : ℝ)) * (Y i) ^ q := by
    rw [hA, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hBeq : B = ∑ i, (1 / (Fintype.card ι : ℝ)) * (Y i) ^ p := by
    rw [hB, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hpow : ∀ i, ((Y i) ^ q) ^ (p / q) = (Y i) ^ p := by
    intro i
    rw [← Real.rpow_mul (hY i)]
    congr 1
    field_simp
  have hpq1 : 1 ≤ p / q := (one_le_div₀ hq).mpr hqp
  have hw' : ∑ i ∈ (Finset.univ : Finset ι), (1 / (Fintype.card ι : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div, div_self hcard_ne]
  have hJ := Real.arith_mean_le_rpow_mean (s := Finset.univ)
      (w := fun _ : ι => 1 / (Fintype.card ι : ℝ)) (z := fun i => (Y i) ^ q)
      (fun i _ => by positivity)
      hw'
      (fun i _ => Real.rpow_nonneg (hY i) q)
      hpq1
  have hsum : (∑ i ∈ (Finset.univ : Finset ι),
        (1 / (Fintype.card ι : ℝ)) * ((Y i) ^ q) ^ (p / q))
      = ∑ i ∈ (Finset.univ : Finset ι), (1 / (Fintype.card ι : ℝ)) * (Y i) ^ p := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hpow i]
  have hmain : A ≤ B ^ (q / p) := by
    rw [hAeq, hBeq]
    have hJq : (∑ i ∈ (Finset.univ : Finset ι), (1 / (Fintype.card ι : ℝ)) * (Y i) ^ q)
        ≤ (∑ i ∈ (Finset.univ : Finset ι),
            (1 / (Fintype.card ι : ℝ)) * ((Y i) ^ q) ^ (p / q)) ^ (q / p) := by
      simpa only [show (1 : ℝ) / (p / q) = q / p by rw [one_div_div]] using hJ
    exact hJq.trans_eq (by rw [hsum])
  have hmul : (q / p) * (1 / q) = 1 / p := by
    field_simp
  have h1q : 0 < 1 / q := by positivity
  calc A ^ (1 / q) ≤ (B ^ (q / p)) ^ (1 / q) := Real.rpow_le_rpow hAge hmain h1q.le
    _ = B ^ (1 / p) := by rw [← Real.rpow_mul hBge, hmul]

end Commons.Analysis.Moment