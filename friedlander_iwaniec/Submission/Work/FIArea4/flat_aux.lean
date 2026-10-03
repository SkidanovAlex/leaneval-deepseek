import Mathlib
import Submission.Work.FIArea4.flat_defs
import Submission.Work.FIArea4.Vflip.KK_flat_finite
import Submission.Work.FIArea4.Vflip.count_supp_Ioc
import Submission.Work.FIArea4.Vflip.sum_range_mod_collapse

/-!
# The flat (`♭`) block estimate for the dyadic dual variance

For a flat pair `(d₁,d₂)` (`d₁' d₂' = □` on the odd parts) and a bump majorant `f` as in
`BumpData S f F C₀`, the Poisson-expanded block

`∑_{a < [d₁,d₂]} γ_{a%d₁,d₁} conj(γ_{a%d₂,d₂}) KK F R d₁ d₂ a`

is bounded by the average of the two one-dimensional quantities
`W d = ∑_{a<d} ‖γ a d‖² #{r ∈ (R,2R], s ∈ suppBox S : s ≡ r a (mod d)}`.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `suppCount` as a sum of one-dimensional fibre counts. -/
lemma suppCount_eq_sum (S R d a : ℕ) :
    suppCount S R d a = ∑ r ∈ Finset.Ioc R (2*R),
      ((suppBox S).filter (fun s : ℕ => s % d = (r * a) % d)).card := by
  rw [suppCount, Finset.card_filter, Finset.product_eq_sprod]
  simp only [Finset.card_filter]
  rw [Finset.sum_product (Ioc R (2*R)) (suppBox S)
    (fun p : ℕ × ℕ => if p.2 % d = p.1 * a % d then (1:ℕ) else 0)]

set_option maxHeartbeats 1000000 in
/-- Final arithmetic for the flat part: the coefficient
`40 √(2D) (RS/D + min R S + 1)` is dominated by `200 (D^(-1/2) R S + D √(RS))`. -/
lemma flat_arith (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    40 * Real.sqrt (2 * (D : ℝ)) * (((R : ℝ) * (S : ℝ)) / (D : ℝ) + ((min R S : ℕ) : ℝ) + 1)
      ≤ 200 * (((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
          + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) := by
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hRSn : 0 ≤ (R:ℝ)*(S:ℝ) := by positivity
  have hsq2 : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hsqd : Real.sqrt (D:ℝ) ^ 2 = (D:ℝ) := Real.sq_sqrt hD0.le
  have hsqr : Real.sqrt (R:ℝ) ^ 2 = (R:ℝ) := Real.sq_sqrt (by positivity)
  have hsqs : Real.sqrt (S:ℝ) ^ 2 = (S:ℝ) := Real.sq_sqrt (by positivity)
  have h2n : 0 ≤ Real.sqrt (2:ℝ) := Real.sqrt_nonneg 2
  have hdn : 0 ≤ Real.sqrt (D:ℝ) := Real.sqrt_nonneg _
  have hrn : 0 ≤ Real.sqrt (R:ℝ) := Real.sqrt_nonneg _
  have hsn : 0 ≤ Real.sqrt (S:ℝ) := Real.sqrt_nonneg _
  have hSd : 0 < Real.sqrt (D:ℝ) := Real.sqrt_pos.mpr hD0
  have hsd1 : (1:ℝ) ≤ Real.sqrt (D:ℝ) := Real.one_le_sqrt.mpr hD1
  have hsqrS : Real.sqrt (R:ℝ) * Real.sqrt (S:ℝ) = Real.sqrt ((R:ℝ)*(S:ℝ)) :=
    (Real.sqrt_mul (by positivity) (S:ℝ)).symm
  have hmin : ((min R S : ℕ) : ℝ) ≤ Real.sqrt (R:ℝ) * Real.sqrt (S:ℝ) := by
    rw [Nat.cast_min]
    rcases le_total (R:ℝ) (S:ℝ) with h | h
    · rw [min_eq_left h]
      have hle : Real.sqrt (R:ℝ) ≤ Real.sqrt (S:ℝ) := Real.sqrt_le_sqrt h
      nlinarith [hsqr, hsqs, hrn, hsn]
    · rw [min_eq_right h]
      have hle : Real.sqrt (S:ℝ) ≤ Real.sqrt (R:ℝ) := Real.sqrt_le_sqrt h
      nlinarith [hsqr, hsqs, hrn, hsn]
  have hpow : (D:ℝ) ^ (-(1:ℝ)/2) = 1 / Real.sqrt (D:ℝ) := by
    have h := Real.rpow_neg hD0.le ((1:ℝ)/2)
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) from by ring, h, inv_eq_one_div, ← Real.sqrt_eq_rpow]
  have e1 : Real.sqrt (2 * (D:ℝ)) * Real.sqrt (D:ℝ) = Real.sqrt 2 * (D:ℝ) := by
    rw [Real.sqrt_mul (by norm_num) (D:ℝ)]
    linear_combination (Real.sqrt 2) * hsqd
  have key1 : Real.sqrt (D:ℝ) * (40 * Real.sqrt (2*(D:ℝ)) * (((R:ℝ)*(S:ℝ))/(D:ℝ) + ((min R S:ℕ):ℝ) + 1))
      = 40 * Real.sqrt 2 * (((R:ℝ)*(S:ℝ)) + (D:ℝ)*((min R S:ℕ):ℝ) + (D:ℝ)) := by
    rw [show Real.sqrt (D:ℝ) * (40 * Real.sqrt (2*(D:ℝ)) * (((R:ℝ)*(S:ℝ))/(D:ℝ) + ((min R S:ℕ):ℝ) + 1))
        = 40 * (Real.sqrt (2*(D:ℝ)) * Real.sqrt (D:ℝ)) * (((R:ℝ)*(S:ℝ))/(D:ℝ) + ((min R S:ℕ):ℝ) + 1) from by ring]
    rw [e1]
    field_simp
  have key2 : Real.sqrt (D:ℝ) * (200 * (((D:ℝ)^(-(1:ℝ)/2)) * (R:ℝ) * (S:ℝ) + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))))
      = 200 * (((R:ℝ)*(S:ℝ)) + (D:ℝ) * (Real.sqrt (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))) := by
    rw [hpow]
    field_simp
  suffices h : Real.sqrt (D:ℝ) * (40 * Real.sqrt (2 * (D:ℝ)) * (((R:ℝ)*(S:ℝ))/(D:ℝ) + ((min R S:ℕ):ℝ) + 1))
      ≤ Real.sqrt (D:ℝ) * (200 * (((D:ℝ)^(-(1:ℝ)/2)) * (R:ℝ) * (S:ℝ) + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))) by
    exact le_of_mul_le_mul_left h hSd
  rw [key1, key2]
  set P : ℝ := Real.sqrt (R:ℝ) * Real.sqrt (S:ℝ) with hP
  have hPn : 0 ≤ P := by rw [hP]; exact mul_nonneg hrn hsn
  have hP1 : 1 ≤ P := by
    rw [hP]
    have h1 : (1:ℝ) ≤ Real.sqrt (R:ℝ) := Real.one_le_sqrt.mpr hR1
    have h2 : (1:ℝ) ≤ Real.sqrt (S:ℝ) := Real.one_le_sqrt.mpr hS1
    nlinarith [mul_nonneg hrn hsn]
  have h60 : 40 * Real.sqrt (2:ℝ) ≤ 60 := by nlinarith [h2n, hsq2]
  have hb : ((R:ℝ)*(S:ℝ) + (D:ℝ)*((min R S:ℕ):ℝ) + (D:ℝ))
      ≤ ((R:ℝ)*(S:ℝ) + (D:ℝ)*P + (D:ℝ)) := by
    have hdm : (D:ℝ)*((min R S:ℕ):ℝ) ≤ (D:ℝ)*P := mul_le_mul_of_nonneg_left hmin hD0.le
    linarith
  have s1 : 40 * Real.sqrt 2 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*((min R S:ℕ):ℝ) + (D:ℝ))
      ≤ 60 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*P + (D:ℝ)) := by
    calc 40 * Real.sqrt 2 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*((min R S:ℕ):ℝ) + (D:ℝ))
        ≤ 60 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*((min R S:ℕ):ℝ) + (D:ℝ)) :=
          mul_le_mul_of_nonneg_right h60 (by positivity)
      _ ≤ 60 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*P + (D:ℝ)) := mul_le_mul_of_nonneg_left hb (by norm_num)
  have t1 : 60 * ((R:ℝ)*(S:ℝ)) ≤ 200 * ((R:ℝ)*(S:ℝ)) := by linarith [hRSn]
  have t2 : 60 * ((D:ℝ)*P) ≤ 100 * ((D:ℝ)*(Real.sqrt (D:ℝ)*P)) := by
    have h : (60:ℝ) ≤ 100 * Real.sqrt (D:ℝ) := by linarith [hsd1]
    have h2 : P * 60 ≤ P * (100*Real.sqrt (D:ℝ)) := mul_le_mul_of_nonneg_left h hPn
    have h3 : (D:ℝ) * (P*60) ≤ (D:ℝ) * (P*(100*Real.sqrt (D:ℝ))) :=
      mul_le_mul_of_nonneg_left h2 hD0.le
    calc 60 * ((D:ℝ)*P) = (D:ℝ) * (P*60) := by ring
      _ ≤ (D:ℝ) * (P*(100*Real.sqrt (D:ℝ))) := h3
      _ = 100 * ((D:ℝ)*(Real.sqrt (D:ℝ)*P)) := by ring
  have t3 : 60 * (D:ℝ) ≤ 100 * ((D:ℝ)*(Real.sqrt (D:ℝ)*P)) := by
    have h : (60:ℝ) ≤ 100 * (Real.sqrt (D:ℝ) * P) := by nlinarith [hsd1, hP1]
    have h2 : (D:ℝ) * 60 ≤ (D:ℝ) * (100 * (Real.sqrt (D:ℝ)*P)) :=
      mul_le_mul_of_nonneg_left h hD0.le
    calc 60 * (D:ℝ) = (D:ℝ) * 60 := by ring
      _ ≤ (D:ℝ) * (100 * (Real.sqrt (D:ℝ)*P)) := h2
      _ = 100 * ((D:ℝ)*(Real.sqrt (D:ℝ)*P)) := by ring
  have hfin : 60 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*P + (D:ℝ))
      ≤ 200 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*(Real.sqrt (D:ℝ)*P)) := by linarith [t1, t2, t3]
  calc 40 * Real.sqrt 2 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*((min R S:ℕ):ℝ) + (D:ℝ))
      ≤ 60 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*P + (D:ℝ)) := s1
    _ ≤ 200 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*(Real.sqrt (D:ℝ)*P)) := hfin
    _ = 200 * ((R:ℝ)*(S:ℝ) + (D:ℝ)*(Real.sqrt (D:ℝ)*Real.sqrt ((R:ℝ)*(S:ℝ)))) := by rw [hsqrS]

set_option maxHeartbeats 1600000 in
/-- **The flat block estimate.** -/
lemma flat_block_le (S : ℕ) (hS : 1 ≤ S) (f : ℝ → ℝ) (F : ℝ → ℂ) (C₀ : ℝ)
    (hM : BumpData S f F C₀) (R : ℕ) (γ : ℕ → ℕ → ℂ) (d1 d2 : ℕ)
    (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2) (hflat : flatPair d1 d2) :
    ‖∑ a ∈ Finset.range (Nat.lcm d1 d2), γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)
        * KK F R d1 d2 a‖
      ≤ (1/2) * (∑ a ∈ Finset.range d1, ‖γ a d1‖ ^ 2 * ((suppCount S R d1 a : ℕ) : ℝ))
        + (1/2) * (∑ a ∈ Finset.range d2, ‖γ a d2‖ ^ 2 * ((suppCount S R d2 a : ℕ) : ℝ)) := by
  obtain ⟨hfn, hf1, hfsup, hfcont, hC0, hFfour, hFdec⟩ := hM
  have hM' : BumpData S f F C₀ := ⟨hfn, hf1, hfsup, hfcont, hC0, hFfour, hFdec⟩
  set q : ℕ := Nat.lcm d1 d2 with hq
  have hq0 : 0 < q := by rw [hq]; exact Nat.lcm_pos (by omega) (by omega)
  have hq1 : 1 ≤ q := hq0
  have hd1q : d1 ∣ q := by rw [hq]; exact Nat.dvd_lcm_left d1 d2
  have hd2q : d2 ∣ q := by rw [hq]; exact Nat.dvd_lcm_right d1 d2
  have hqm : q ∣ d1 * d2 := by rw [hq]; exact Nat.lcm_dvd (Nat.dvd_mul_right d1 d2) (Nat.dvd_mul_left d2 d1)
  -- the KK identity for flat pairs
  have hKK0 : ∀ a : ℕ, KK F R d1 d2 a =
      ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
        ∑ s ∈ suppBox S, (if s % Nat.lcm d1 d2 = (r * a) % Nat.lcm d1 d2
          then ((f s : ℝ) : ℂ) else 0) :=
    fun a => Vflip.KK_flat_finite S hS f F C₀ hM' R d1 d2 a hd1 hd2 hflat
  have hKK : ∀ a : ℕ, KK F R d1 d2 a =
      ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
        ∑ s ∈ suppBox S, (if s % q = (r * a) % q then ((f s : ℝ) : ℂ) else 0) := by
    intro a; rw [hKK0 a, hq]
  -- the two auxiliary quantities
  set wsum : ℕ → ℝ := fun a => ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
      ∑ s ∈ suppBox S, (if s % q = (r * a) % q then f s else 0) with hwsum
  set mid : ℕ → ℝ := fun a => ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
      ∑ s ∈ suppBox S, (if s % q = (r * a) % q then (1 : ℝ) else 0) with hmid
  have hw0 : ∀ a, 0 ≤ wsum a := by
    intro a; rw [hwsum]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ =>
      by_cases (fun hc => by rw [if_pos hc]; exact hfn s) (fun hc => by rw [if_neg hc])))
  have hm0 : ∀ a, 0 ≤ mid a := by
    intro a; rw [hmid]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ =>
      by_cases (fun hc => by rw [if_pos hc]; norm_num) (fun hc => by rw [if_neg hc])))
  -- step 1: extract the KK bound
  have hmain : ‖∑ a ∈ Finset.range q, γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)
        * KK F R d1 d2 a‖
      ≤ ∑ a ∈ Finset.range q, ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ * wsum a := by
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro a ha
    have hKa : ‖KK F R d1 d2 a‖ ≤ wsum a := by
      rw [hwsum, hKK a]
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum; intro r hr
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum; intro s hs
      by_cases hc : s % q = (r * a) % q
      · rw [if_pos hc, if_pos hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hfn s)]
      · rw [if_neg hc, if_neg hc, norm_zero]
    calc ‖γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a‖
        = ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ * ‖KK F R d1 d2 a‖ := by
          rw [norm_mul, norm_mul, starRingEnd_apply, norm_star]
      _ ≤ ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ * wsum a :=
          mul_le_mul_of_nonneg_left hKa (by positivity)
  -- step 2: replace the `f`-weight by 1
  have hwle : ∀ a, wsum a ≤ mid a := by
    intro a
    rw [hwsum, hmid]
    apply Finset.sum_le_sum; intro r hr
    apply Finset.sum_le_sum; intro s hs
    by_cases hc : s % q = (r * a) % q
    · rw [if_pos hc, if_pos hc]; exact hf1 s
    · rw [if_neg hc, if_neg hc]
  -- step 3: AM-GM
  have hAB : (∑ a ∈ Finset.range q, ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ * wsum a)
      ≤ (1/2) * (∑ a ∈ Finset.range q, ‖γ (a % d1) d1‖ ^ 2 * mid a)
        + (1/2) * (∑ a ∈ Finset.range q, ‖γ (a % d2) d2‖ ^ 2 * mid a) := by
    have hpt : ∀ a, ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ * wsum a
        ≤ (1/2) * (‖γ (a % d1) d1‖ ^ 2 * mid a) + (1/2) * (‖γ (a % d2) d2‖ ^ 2 * mid a) := by
      intro a
      have hs : ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖
          ≤ (‖γ (a % d1) d1‖ ^ 2 + ‖γ (a % d2) d2‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖γ (a % d1) d1‖ - ‖γ (a % d2) d2‖)]
      calc ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ * wsum a
          ≤ ((‖γ (a % d1) d1‖ ^ 2 + ‖γ (a % d2) d2‖ ^ 2) / 2) * mid a :=
            mul_le_mul hs (hwle a) (hw0 a) (by positivity)
        _ = (1/2) * (‖γ (a % d1) d1‖ ^ 2 * mid a)
              + (1/2) * (‖γ (a % d2) d2‖ ^ 2 * mid a) := by ring
    calc (∑ a ∈ Finset.range q, ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ * wsum a)
        ≤ ∑ a ∈ Finset.range q, ((1/2) * (‖γ (a % d1) d1‖ ^ 2 * mid a)
              + (1/2) * (‖γ (a % d2) d2‖ ^ 2 * mid a)) := Finset.sum_le_sum (fun a _ => hpt a)
      _ = (1/2) * (∑ a ∈ Finset.range q, ‖γ (a % d1) d1‖ ^ 2 * mid a)
            + (1/2) * (∑ a ∈ Finset.range q, ‖γ (a % d2) d2‖ ^ 2 * mid a) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- step 4: the collapse
  have hcollapse : ∀ (d : ℕ), 1 ≤ d → d ∣ q →
      (∑ a ∈ Finset.range q, ‖γ (a % d) d‖ ^ 2 * mid a)
        ≤ ∑ a1 ∈ Finset.range d, ‖γ a1 d‖ ^ 2 * ((suppCount S R d a1 : ℕ) : ℝ) := by
    intro d hd hdq
    have hcq : ∀ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
        Nat.Coprime r q := by
      intro r hr
      exact (Finset.mem_filter.mp hr).2.coprime_dvd_right hqm
    have eA : (∑ a ∈ Finset.range q, ‖γ (a % d) d‖ ^ 2 * mid a)
        = ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
            ∑ s ∈ suppBox S, ∑ a ∈ Finset.range q,
              ‖γ (a % d) d‖ ^ 2 * (if s % q = (r * a) % q then (1 : ℝ) else 0) := by
      rw [hmid]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro r hr
      rw [Finset.sum_comm]
    have eB : (∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
            ∑ s ∈ suppBox S, ∑ a ∈ Finset.range q,
              ‖γ (a % d) d‖ ^ 2 * (if s % q = (r * a) % q then (1 : ℝ) else 0))
        = ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
            ∑ s ∈ suppBox S, ∑ a1 ∈ Finset.range d,
              (if s % d = (r * a1) % d then (1 : ℝ) else 0) * ‖γ a1 d‖ ^ 2 := by
      apply Finset.sum_congr rfl; intro r hr
      apply Finset.sum_congr rfl; intro s hs
      calc ∑ a ∈ Finset.range q, ‖γ (a % d) d‖ ^ 2 * (if s % q = (r * a) % q then (1 : ℝ) else 0)
          = ∑ a ∈ Finset.range q, (if s % q = (r * a) % q then (1 : ℝ) else 0) * ‖γ (a % d) d‖ ^ 2 :=
            Finset.sum_congr rfl (fun a _ => by ring)
        _ = ∑ a1 ∈ Finset.range d, (if s % d = (r * a1) % d then (1 : ℝ) else 0) * ‖γ a1 d‖ ^ 2 :=
            Vflip.sum_range_mod_collapse q d r s hd hq1 hdq (hcq r hr) (fun a => ‖γ a d‖ ^ 2)
    have eC : (∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
            ∑ s ∈ suppBox S, ∑ a1 ∈ Finset.range d,
              (if s % d = (r * a1) % d then (1 : ℝ) else 0) * ‖γ a1 d‖ ^ 2)
        = ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
            ∑ a1 ∈ Finset.range d, ‖γ a1 d‖ ^ 2 *
              (((suppBox S).filter (fun s : ℕ => s % d = (r * a1) % d)).card : ℝ) := by
      apply Finset.sum_congr rfl; intro r hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a1 ha1
      rw [← Finset.sum_mul]
      have hcf : (∑ s ∈ suppBox S, (if s % d = (r * a1) % d then (1 : ℝ) else 0))
          = (((suppBox S).filter (fun s : ℕ => s % d = (r * a1) % d)).card : ℝ) := by
        rw [Finset.card_filter, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hc : s % d = (r * a1) % d <;> simp [hc]
      rw [hcf, mul_comm]
    have eD : (∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
            ∑ a1 ∈ Finset.range d, ‖γ a1 d‖ ^ 2 *
              (((suppBox S).filter (fun s : ℕ => s % d = (r * a1) % d)).card : ℝ))
        ≤ ∑ r ∈ Finset.Ioc R (2 * R),
            ∑ a1 ∈ Finset.range d, ‖γ a1 d‖ ^ 2 *
              (((suppBox S).filter (fun s : ℕ => s % d = (r * a1) % d)).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun r hr hnr => Finset.sum_nonneg (fun a1 _ => by positivity))
    have eE : (∑ r ∈ Finset.Ioc R (2 * R),
            ∑ a1 ∈ Finset.range d, ‖γ a1 d‖ ^ 2 *
              (((suppBox S).filter (fun s : ℕ => s % d = (r * a1) % d)).card : ℝ))
        = ∑ a1 ∈ Finset.range d, ‖γ a1 d‖ ^ 2 * ((suppCount S R d a1 : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a1 ha1
      rw [← Finset.mul_sum]
      congr 1
      rw [← Nat.cast_sum]
      congr 1
      exact (suppCount_eq_sum S R d a1).symm
    rw [eA, eB, eC]
    exact le_trans eD eE.le
  have hF1 := hcollapse d1 hd1 hd1q
  have hF2 := hcollapse d2 hd2 hd2q
  linarith [hmain, hAB, hF1, hF2]

end

end Work.FIArea4
