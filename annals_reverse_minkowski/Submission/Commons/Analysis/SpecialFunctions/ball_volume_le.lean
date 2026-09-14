import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace Commons.Analysis.SpecialFunctions

open MeasureTheory


private lemma exp_two_eq : Real.exp 2 = (Real.exp 1)^2 := by
  rw [← Real.exp_nat_mul]
  norm_num

private lemma ratio_pow_le (q : ℕ) (hq : 1 ≤ q) :
    (((q:ℝ)+2)/(q:ℝ))^q ≤ (Real.exp 1)^2 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hr : 0 < ((q:ℝ)+2)/(q:ℝ) := by positivity
  have hlog : Real.log (((q:ℝ)+2)/(q:ℝ)) ≤ 2/(q:ℝ) := by
    have h : ((q:ℝ)+2)/(q:ℝ) - 1 = 2/(q:ℝ) := by field_simp; ring
    calc Real.log (((q:ℝ)+2)/(q:ℝ)) ≤ ((q:ℝ)+2)/(q:ℝ) - 1 := Real.log_le_sub_one_of_pos hr
      _ = 2/(q:ℝ) := h
  have hmain : Real.log ((((q:ℝ)+2)/(q:ℝ))^q) ≤ 2 := by
    rw [Real.log_pow]
    calc (q:ℝ) * Real.log (((q:ℝ)+2)/(q:ℝ)) ≤ (q:ℝ) * (2/(q:ℝ)) := by
          exact mul_le_mul_of_nonneg_left hlog (le_of_lt hq0)
      _ = 2 := by field_simp
  rw [← exp_two_eq]
  rw [← Real.log_le_iff_le_exp (x := (((q:ℝ)+2)/(q:ℝ))^q) (by positivity)]
  exact hmain

private lemma key_pow (q : ℕ) (hq : 1 ≤ q) :
    (2*Real.pi/((q:ℝ)+2))^2 * (2*Real.pi*Real.exp 1/(q:ℝ))^q
      ≤ (2*Real.pi*Real.exp 1/((q:ℝ)+2))^(q+2) := by
  set A : ℝ := 2*Real.pi*Real.exp 1 with hAdef
  have h1 : ((q:ℝ)+2)^q ≤ (Real.exp 1)^2 * (q:ℝ)^q := by
    have hqpow : (0:ℝ) < (q:ℝ)^q := by positivity
    have h := ratio_pow_le q hq
    rw [div_pow] at h
    rw [div_le_iff₀ hqpow] at h
    exact h
  rw [div_pow, div_pow, div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (2*Real.pi)^2 * ((q:ℝ)+2)^q ≤ A^2 * (q:ℝ)^q := by
    have hA2 : A^2 = (2*Real.pi)^2 * (Real.exp 1)^2 := by rw [hAdef]; ring
    rw [hA2]
    nlinarith [h1, sq_nonneg (2*Real.pi), Real.pi_pos.le]
  have h3 : (2*Real.pi)^2 * ((q:ℝ)+2)^q * (A^q * ((q:ℝ)+2)^2)
          ≤ (A^2 * (q:ℝ)^q) * (A^q * ((q:ℝ)+2)^2) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  calc (2*Real.pi)^2 * A^q * ((q:ℝ)+2)^(q+2)
      = (2*Real.pi)^2 * ((q:ℝ)+2)^q * (A^q * ((q:ℝ)+2)^2) := by
          rw [pow_add]; ring
    _ ≤ (A^2 * (q:ℝ)^q) * (A^q * ((q:ℝ)+2)^2) := h3
    _ = A^(q+2) * (((q:ℝ)+2)^2 * (q:ℝ)^q) := by
          rw [show q+2 = 2 + q by omega, pow_add]; ring

private lemma ball_volume_repr (m : ℕ) (hm : 1 ≤ m) :
    MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)
      = (√Real.pi)^m / Real.Gamma ((m:ℝ)/2 + 1) := by
  have hne : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
  have h := EuclideanSpace.volume_ball (Fin m) (0 : EuclideanSpace ℝ (Fin m)) 1
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul] at h
  rw [MeasureTheory.Measure.real, h, ENNReal.toReal_ofReal]
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (le_of_lt (Real.Gamma_pos_of_pos (by positivity)))

private lemma ball_volume_rec (m : ℕ) (hm : 2 ≤ m) :
    (√Real.pi)^m / Real.Gamma ((m:ℝ)/2 + 1)
      = (2 * Real.pi/(m:ℝ)) * ((√Real.pi)^(m-2) / Real.Gamma ((((m-2:ℕ)):ℝ)/2 + 1)) := by
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hcast : ((m:ℝ)/2 : ℝ) = ((((m-2:ℕ)):ℝ)/2 + 1) := by
    have hm2 : (((m-2:ℕ)):ℝ) = (m:ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ m)]
      norm_num
    rw [hm2]; ring
  have hΓ : Real.Gamma ((m:ℝ)/2 + 1) = ((m:ℝ)/2) * Real.Gamma ((((m-2:ℕ)):ℝ)/2 + 1) := by
    rw [← hcast]
    exact Real.Gamma_add_one (by positivity)
  have hpow : (√Real.pi)^m = (√Real.pi)^(m-2) * Real.pi := by
    have : m = (m-2) + 2 := by omega
    rw [this, pow_add]
    simp [Real.sq_sqrt Real.pi_nonneg]
  have hG : Real.Gamma ((((m-2:ℕ)):ℝ)/2 + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  rw [hΓ, hpow]
  field_simp

private lemma vol_sq_le (n : ℕ) : 1 ≤ n →
    ((√Real.pi)^n / Real.Gamma ((n:ℝ)/2 + 1))^2 ≤ (2*Real.pi*Real.exp 1/(n:ℝ))^n := by
  refine Nat.strong_induction_on n ?_
  intro n ih hn
  rcases lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · -- n = 1
      have hΓ : Real.Gamma ((1:ℝ)/2 + 1) = √Real.pi / 2 := by
        rw [Real.Gamma_add_one (by norm_num : ((1:ℝ)/2) ≠ 0), Real.Gamma_one_half_eq]
        ring
      push_cast
      rw [hΓ, pow_one]
      have h2 : √Real.pi/(√Real.pi/2) = 2 := by
        have : √Real.pi ≠ 0 := by positivity
        field_simp
      rw [h2, pow_one, div_one]
      norm_num
      nlinarith [Real.pi_gt_three, Real.exp_one_gt_d9]
    · -- n = 2
      have hΓ : Real.Gamma ((2:ℝ)/2 + 1) = 1 := by
        rw [show (2:ℝ)/2 + 1 = 2 by norm_num, Real.Gamma_two]
      push_cast
      rw [hΓ, div_one, Real.sq_sqrt Real.pi_nonneg]
      have he : 1 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h1 : Real.pi ≤ Real.pi * Real.exp 1 := by nlinarith [Real.pi_pos, he]
      have hpow : 2*Real.pi*Real.exp 1/2 = Real.pi * Real.exp 1 := by ring
      rw [hpow]
      exact pow_le_pow_left₀ Real.pi_pos.le h1 2
  · -- n ≥ 3
    have hn2 : 2 ≤ n := by omega
    have hq : 1 ≤ n - 2 := by omega
    have hrec := ball_volume_rec n hn2
    have ih' := ih (n-2) (by omega) hq
    rw [hrec, mul_pow]
    calc (2*Real.pi/(n:ℝ))^2 * ((√Real.pi)^(n-2) / Real.Gamma ((((n-2:ℕ)):ℝ)/2 + 1))^2
        ≤ (2*Real.pi/(n:ℝ))^2 * (2*Real.pi*Real.exp 1/(((n-2:ℕ)):ℝ))^(n-2) := by
            apply mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ (2*Real.pi*Real.exp 1/(n:ℝ))^n := by
            have hcast : (n:ℝ) = ((((n-2:ℕ)):ℝ) + 2) := by
              rw [Nat.cast_sub hn2]; ring
            have hexp : n = (n-2) + 2 := by omega
            rw [hcast, hexp]
            exact key_pow (n-2) hq


/-- **Volume of the Euclidean unit ball, Stirling form.**  In dimension `m ≥ 1` the volume of
the unit ball is at most `(2πe/m)^{m/2}`.  Equivalently
`vol(B₂ᵐ)^{1/m} ≤ √(2πe/m)`, i.e. `r_m := vol(B₂ᵐ)^{-1/m} ≥ √(m/(2πe))`.

This is the numerical input in the proof of Regev–Stephens-Davidowitz, *A reverse Minkowski
theorem*, Ann. of Math. 199 (2024), Corollary 4.5: their Lemma bounds
`ℓ_{K°}((Aᵀ)^{-1})` from below by `√(m/2π)·r_m > m/(2π√e)`.

Proof route: `MeasureTheory.volume_ball` / `InnerProductSpace.volume_ball` gives
`vol(B₂ᵐ) = π^{m/2} / Γ(m/2 + 1)`; the Stirling lower bound `Γ(x+1) ≥ (x/e)^x` (Mathlib's
`Nat.factorial` bounds, plus `Real.Gamma_nat_add_half`, split into the even and odd cases for
`m`) yields `π^{m/2}/Γ(m/2+1) ≤ (2πe/m)^{m/2}`. -/
theorem ball_volume_le (m : ℕ) (hm : 1 ≤ m) :
    MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1) ≤
      (2 * Real.pi * Real.exp 1 / (m : ℝ)) ^ ((m : ℝ) / 2) := by
  rw [ball_volume_repr m hm]
  have hsq := vol_sq_le m hm
  have hB : (0:ℝ) ≤ 2*Real.pi*Real.exp 1/(m:ℝ) := by positivity
  have hsq2 : ((2*Real.pi*Real.exp 1/(m:ℝ))^((m:ℝ)/2))^2 = (2*Real.pi*Real.exp 1/(m:ℝ))^m := by
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul hB ((m:ℝ)/2) 2]
    rw [show (m:ℝ)/2*2 = (m:ℝ) by ring, Real.rpow_natCast]
  rw [← hsq2] at hsq
  have h1 : (0:ℝ) ≤ (√Real.pi)^m / Real.Gamma ((m:ℝ)/2 + 1) := by positivity
  have h2 : (0:ℝ) ≤ (2*Real.pi*Real.exp 1/(m:ℝ))^((m:ℝ)/2) := Real.rpow_nonneg hB _
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg h1, abs_of_nonneg h2] at this

end Commons.Analysis.SpecialFunctions