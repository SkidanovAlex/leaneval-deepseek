import Mathlib
import Submission.Work.ANum.HLog
import Submission.Work.ANum.MapEncl
import Submission.Work.ANum.norm_pow_succ_sub_pow_succ_le
import Submission.Work.ANum.tsum_log_geom_tail

namespace Work.ANum

open Submission.CDTPlan
open scoped BigOperators

/-- `log ‖h(q)‖` is bounded, uniformly over the closed disc of radius `ρ` about `q₀`, by the
finite initial sum of the logarithmic series plus the geometric tail.  The initial terms are
estimated by Lipschitz continuity of `z ↦ z ^ (n+1)` on the disc of radius `‖q₀‖ + ρ`, the tail
by `log ‖1 + w‖ ≤ ‖w‖`. -/
theorem h_log_bound (q₀ : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hq₀ : 0 < ‖q₀‖) (hρlt : ρ < ‖q₀‖)
    (hsum : ‖q₀‖ + ρ < 1) (M : ℕ) :
    ∀ q : ℂ, ‖q - q₀‖ ≤ ρ →
      Real.log ‖Submission.CDTPlan.hauptH q‖ ≤
        Real.log 256 + Real.log (‖q₀‖ + ρ) +
          24 * (∑ n ∈ Finset.range M,
            Real.log (‖1 + q₀ ^ (n + 1)‖ + ((n : ℝ) + 1) * (‖q₀‖ + ρ) ^ n * ρ)) +
          24 * ((‖q₀‖ + ρ) ^ (M + 1) / (1 - (‖q₀‖ + ρ))) := by
  intro q hq
  set R := ‖q₀‖ + ρ with hR
  have hR0 : 0 ≤ R := by rw [hR]; exact add_nonneg (norm_nonneg _) hρ
  have hR1 : R < 1 := by rw [hR]; exact hsum
  have hq₀R : ‖q₀‖ ≤ R := by rw [hR]; linarith
  have hqR : ‖q‖ ≤ R := by
    have h1 : ‖q‖ ≤ ρ + ‖q₀‖ := by
      calc ‖q‖ = ‖(q - q₀) + q₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖q - q₀‖ + ‖q₀‖ := norm_add_le _ _
        _ ≤ ρ + ‖q₀‖ := by linarith
    rw [hR]; linarith
  have hqpos : 0 < ‖q‖ := by
    have h2 : ‖q₀‖ ≤ ρ + ‖q‖ := by
      calc ‖q₀‖ = ‖(q₀ - q) + q‖ := by rw [sub_add_cancel]
        _ ≤ ‖q₀ - q‖ + ‖q‖ := norm_add_le _ _
        _ = ‖q - q₀‖ + ‖q‖ := by rw [norm_sub_rev]
        _ ≤ ρ + ‖q‖ := by linarith
    linarith
  have hqne : q ≠ 0 := norm_pos_iff.mp hqpos
  have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hqR hR1
  rw [log_norm_hauptH_of_norm_lt_one hq1 hqne]
  have hsumm_g : Summable (fun n : ℕ => Real.log ‖(1 : ℂ) + q ^ (n + 1)‖) := by
    have hgeo : Summable (fun n : ℕ => q ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_iff_norm_lt_one.mpr hq1)
    have := hgeo.norm.summable_log_norm_one_add
    simpa using this
  have hsplit := hsumm_g.sum_add_tsum_nat_add M
  have hfin : (∑ n ∈ Finset.range M, Real.log ‖(1 : ℂ) + q ^ (n + 1)‖)
      ≤ ∑ n ∈ Finset.range M,
          Real.log (‖1 + q₀ ^ (n + 1)‖ + ((n : ℝ) + 1) * R ^ n * ρ) := by
    apply Finset.sum_le_sum
    intro n _
    have hpow : ‖q ^ (n + 1) - q₀ ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * R ^ n * ‖q - q₀‖ :=
      norm_pow_succ_sub_pow_succ_le hqR hq₀R n
    have hb : ‖(1 : ℂ) + q ^ (n + 1)‖ ≤ ‖1 + q₀ ^ (n + 1)‖ + ((n : ℝ) + 1) * R ^ n * ρ := by
      have htri : ‖(1 : ℂ) + q ^ (n + 1)‖
          ≤ ‖1 + q₀ ^ (n + 1)‖ + ‖q ^ (n + 1) - q₀ ^ (n + 1)‖ := by
        have he : (1 : ℂ) + q ^ (n + 1) = (1 + q₀ ^ (n + 1)) + (q ^ (n + 1) - q₀ ^ (n + 1)) := by
          ring
        rw [he]; exact norm_add_le _ _
      have hcoef : 0 ≤ ((n : ℝ) + 1) * R ^ n := by positivity
      have hle : ‖q ^ (n + 1) - q₀ ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * R ^ n * ρ :=
        le_trans hpow (mul_le_mul_of_nonneg_left hq hcoef)
      linarith
    have hp1 : 0 < ‖(1 : ℂ) + q ^ (n + 1)‖ := by
      have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) + q ^ (n + 1)‖ + ‖q ^ (n + 1)‖ := by
        have h := norm_sub_le ((1 : ℂ) + q ^ (n + 1)) (q ^ (n + 1))
        simpa using h
      have h2 : ‖q ^ (n + 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg q) hq1 (Nat.succ_ne_zero n)
      linarith
    exact Real.log_le_log hp1 hb
  have htail : (∑' j : ℕ, Real.log ‖(1 : ℂ) + q ^ (j + M + 1)‖) ≤ R ^ (M + 1) / (1 - R) :=
    tsum_log_geom_tail hR0 hR1 hqR M
  have hkey : (∑' n : ℕ, Real.log ‖(1 : ℂ) + q ^ (n + 1)‖)
      ≤ (∑ n ∈ Finset.range M, Real.log (‖1 + q₀ ^ (n + 1)‖ + ((n : ℝ) + 1) * R ^ n * ρ))
        + R ^ (M + 1) / (1 - R) := by
    rw [← hsplit]
    exact add_le_add hfin htail
  rw [tsum_mul_left]
  have h24 : 24 * (∑' n : ℕ, Real.log ‖(1 : ℂ) + q ^ (n + 1)‖)
      ≤ 24 * (∑ n ∈ Finset.range M,
          Real.log (‖1 + q₀ ^ (n + 1)‖ + ((n : ℝ) + 1) * R ^ n * ρ))
        + 24 * (R ^ (M + 1) / (1 - R)) := by
    have h := mul_le_mul_of_nonneg_left hkey (by norm_num : (0 : ℝ) ≤ 24)
    rwa [mul_add] at h
  have hlogq : Real.log ‖q‖ ≤ Real.log R := Real.log_le_log hqpos hqR
  have hfin' := add_le_add (add_le_add (le_refl (Real.log 256)) hlogq) h24
  linarith

end Work.ANum
