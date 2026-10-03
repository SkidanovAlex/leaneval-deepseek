import Mathlib
import Submission.Work.FIArea4.WdyadDefs2
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The Jacobi weight `wChar` has complex norm at most `1`. -/
private lemma norm_wChar_le_one (d1 d2 r : ℕ) : ‖wChar d1 d2 r‖ ≤ 1 := by
  unfold wChar
  split_ifs with h
  · rcases jacobiSym.trichotomy (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) with
      h0 | h1 | h1
    · rw [h0]; norm_num
    · rw [h1]; norm_num
    · rw [h1]; norm_num
  · simp

/-- For `r ∣ m` the absolute value of the integer quotient `m / r` is `|m| / r`. -/
private lemma abs_ediv_cast (m : ℤ) (r : ℕ) (hr : r ≠ 0) (hd : (r : ℤ) ∣ m) :
    |((m / (r : ℤ) : ℤ) : ℝ)| = (m.natAbs : ℝ) / (r : ℝ) := by
  obtain ⟨u, hu⟩ := hd
  have hrne : (r : ℤ) ≠ 0 := by exact_mod_cast hr
  have hdiv : m / (r : ℤ) = u := by rw [hu, Int.mul_ediv_cancel_left u hrne]
  have hnat : m.natAbs = r * u.natAbs := by
    rw [hu, Int.natAbs_mul, Int.natAbs_natCast]
  have huabs : |((u : ℤ) : ℝ)| = (u.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs u]; norm_num
  rw [hdiv, huabs, hnat]
  push_cast
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast hr)]

/-- `((T/2))^{-2} = 4 T^{-2}` for `T > 0`. -/
private lemma rpow_neg_two_div_two (T : ℝ) (hT : 0 < T) :
    (T / 2) ^ (-(2 : ℝ)) = 4 * T ^ (-(2 : ℝ)) := by
  rw [Real.rpow_neg (by positivity) 2, Real.rpow_neg (le_of_lt hT) 2,
    Real.rpow_two, Real.rpow_two, div_pow]
  norm_num
  rw [div_eq_mul_inv]

/-- The elementary size comparison: the term for the divisor `r` of `m` is at most `4` times the
term for the reference value `r = R`. -/
private lemma key_half (σ : ℝ) (hσ : 0 ≤ σ) {n r q R : ℝ} (hn : 0 ≤ n) (hr : 0 < r)
    (hq : 0 < q) (hrR : r ≤ 2 * R) :
    (σ * n / (q * R)) / 2 ≤ σ * (n / (r * q)) := by
  rw [div_div, ← mul_div_assoc]
  apply div_le_div_of_nonneg_left (by positivity)
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_right hrR hq.le]

theorem cCoef_bound : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
    ∀ (F : ℝ → ℂ) (C₀ σ : ℝ) (R : ℕ) (d1 d2 : ℕ) (m : ℤ), 0 < C₀ → 1 ≤ σ → 1 ≤ R → 1 ≤ d1 → 1 ≤ d2 →
      (∀ ξ : ℝ, ‖F ξ‖ ≤ C₀ * σ * (1 + σ * |ξ|) ^ (-(2:ℝ))) → m ≠ 0 →
      ‖Work.FIArea4.cCoef F R d1 d2 m‖ ≤
        C * C₀ * σ * (1 + σ * |(m:ℝ)| / ((Nat.lcm d1 d2 : ℝ) * R)) ^ (-(2:ℝ)) * (m.natAbs : ℝ) ^ δ := by
  intro δ hδ
  obtain ⟨Cδ, hCδpos, hCδ⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow δ hδ
  refine ⟨4 * Cδ, by positivity, ?_⟩
  intro F C₀ σ R d1 d2 m hC₀ hσ hR hd1 hd2 hF hm
  set q : ℕ := Nat.lcm d1 d2 with hq
  set n : ℕ := m.natAbs with hn
  have hn_pos : 0 < n := by rw [hn, Int.natAbs_pos]; exact hm
  have hqpos : 0 < q := by rw [hq]; exact Nat.lcm_pos (by omega) (by omega)
  have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hRposR : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have habs : |(m : ℝ)| = (n : ℝ) := by
    have h1 : ((m.natAbs : ℤ) : ℝ) = |(m : ℝ)| := by exact_mod_cast Int.natCast_natAbs m
    rw [← h1, hn]; norm_num
  set t : ℝ := σ * (n : ℝ) / ((q : ℝ) * (R : ℝ)) with ht
  have ht_nonneg : 0 ≤ t := by rw [ht]; positivity
  have h1t : 0 < 1 + t := by linarith
  have hBnn : 0 ≤ 4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ)) :=
    mul_nonneg (by positivity) (le_of_lt (Real.rpow_pos_of_pos h1t _))
  have hterm : ∀ r ∈ Finset.Ioc R (2 * R),
      ‖(if (r : ℤ) ∣ m then wChar d1 d2 r * F (((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))
        else (0 : ℂ))‖
        ≤ (if (r : ℤ) ∣ m then 4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ)) else 0) := by
    intro r hr
    rw [Finset.mem_Ioc] at hr
    obtain ⟨hrR, hr2R⟩ := hr
    have hrpos : 0 < r := by omega
    have hrposR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
    have hr2R' : (r : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hr2R
    by_cases hd : (r : ℤ) ∣ m
    · rw [if_pos hd, if_pos hd]
      obtain ⟨u, hu⟩ := hd
      have hrne : (r : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos)
      have hdiv : m / (r : ℤ) = u := by rw [hu, Int.mul_ediv_cancel_left u hrne]
      have hnat : m.natAbs = r * u.natAbs := by rw [hu, Int.natAbs_mul, Int.natAbs_natCast]
      have huabs : |((u : ℤ) : ℝ)| = (u.natAbs : ℝ) := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs u]; norm_num
      have hnu : ((u.natAbs : ℕ) : ℝ) = (n : ℝ) / (r : ℝ) := by
        rw [hn, hnat]; push_cast
        rw [mul_div_cancel_left₀ _ (ne_of_gt hrposR)]
      have hξeq : |(((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))| = (n : ℝ) / ((r : ℝ) * (q : ℝ)) := by
        rw [hdiv, abs_div, abs_of_pos hqposR, huabs, hnu, div_div]
      have hhalf : t / 2 ≤ σ * |(((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))| := by
        rw [hξeq, ht]
        exact key_half σ (by linarith) hnnonneg hrposR hqposR hr2R'
      have hlt : (1 + t) / 2 ≤ 1 + σ * |(((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))| := by linarith
      have h1 : (0 : ℝ) < (1 + t) / 2 := by linarith
      have hrpow : (1 + σ * |(((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))|) ^ (-(2 : ℝ))
          ≤ 4 * (1 + t) ^ (-(2 : ℝ)) := by
        have h := Real.rpow_le_rpow_of_nonpos h1 hlt (by norm_num : (-(2 : ℝ)) ≤ 0)
        rwa [rpow_neg_two_div_two (1 + t) (by linarith)] at h
      have hFξ : ‖F (((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))‖ ≤ 4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ)) := by
        calc ‖F (((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))‖
            ≤ C₀ * σ * (1 + σ * |(((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))|) ^ (-(2 : ℝ)) := hF _
          _ ≤ C₀ * σ * (4 * (1 + t) ^ (-(2 : ℝ))) := by
                apply mul_le_mul_of_nonneg_left hrpow; positivity
          _ = 4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ)) := by ring
      calc ‖wChar d1 d2 r * F (((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))‖
          = ‖wChar d1 d2 r‖ * ‖F (((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))‖ := norm_mul _ _
        _ ≤ 1 * (4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ))) :=
              mul_le_mul (norm_wChar_le_one d1 d2 r) hFξ (norm_nonneg _) (by norm_num)
        _ = 4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ)) := by ring
    · rw [if_neg hd, if_neg hd]; simp
  have hcount : ((Finset.Ioc R (2 * R)).filter (fun r : ℕ => (r : ℤ) ∣ m)).card
      ≤ n.divisors.card := by
    apply Finset.card_le_card
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrS, hrd⟩ := hr
    rw [Nat.mem_divisors]
    refine ⟨?_, ?_⟩
    · rw [hn, ← Int.ofNat_dvd]
      exact (Int.dvd_natAbs).mpr hrd
    · omega
  have hcountR : (((Finset.Ioc R (2 * R)).filter (fun r : ℕ => (r : ℤ) ∣ m)).card : ℝ)
      ≤ Cδ * (n : ℝ) ^ δ := le_trans (by exact_mod_cast hcount) (hCδ n)
  have hsum : (∑ r ∈ Finset.Ioc R (2 * R),
        (if (r : ℤ) ∣ m then 4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ)) else 0))
      = 4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ))
        * (((Finset.Ioc R (2 * R)).filter (fun r : ℕ => (r : ℤ) ∣ m)).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring_nf
  have hmain : ‖Work.FIArea4.cCoef F R d1 d2 m‖
      ≤ (4 * Cδ) * C₀ * σ * (1 + σ * |(m : ℝ)| / ((q : ℝ) * (R : ℝ))) ^ (-(2 : ℝ))
        * (n : ℝ) ^ δ := by
    have hcc : Work.FIArea4.cCoef F R d1 d2 m
        = ∑ r ∈ Finset.Ioc R (2 * R),
            (if (r : ℤ) ∣ m then wChar d1 d2 r * F (((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))
              else (0 : ℂ)) := by
      unfold Work.FIArea4.cCoef
      rw [← hq]
    calc ‖Work.FIArea4.cCoef F R d1 d2 m‖
        = ‖∑ r ∈ Finset.Ioc R (2 * R),
            (if (r : ℤ) ∣ m then wChar d1 d2 r * F (((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))
              else (0 : ℂ))‖ := by rw [hcc]
      _ ≤ ∑ r ∈ Finset.Ioc R (2 * R),
            ‖(if (r : ℤ) ∣ m then wChar d1 d2 r * F (((m / (r : ℤ) : ℤ) : ℝ) / (q : ℝ))
              else (0 : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ Finset.Ioc R (2 * R),
            (if (r : ℤ) ∣ m then 4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ)) else 0) :=
              Finset.sum_le_sum hterm
      _ = 4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ))
            * (((Finset.Ioc R (2 * R)).filter (fun r : ℕ => (r : ℤ) ∣ m)).card : ℝ) := hsum
      _ ≤ 4 * C₀ * σ * (1 + t) ^ (-(2 : ℝ)) * (Cδ * (n : ℝ) ^ δ) :=
            mul_le_mul_of_nonneg_left hcountR hBnn
      _ = (4 * Cδ) * C₀ * σ * (1 + σ * |(m : ℝ)| / ((q : ℝ) * (R : ℝ))) ^ (-(2 : ℝ))
            * (n : ℝ) ^ δ := by
            have hte : 1 + t = 1 + σ * |(m : ℝ)| / ((q : ℝ) * (R : ℝ)) := by rw [ht, habs]
            rw [hte]; ring
  exact hmain

end

end Work.FIArea4.Vflip
