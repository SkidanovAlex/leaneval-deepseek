/-
# `Submission.Work.FIArea2.R6.pairFibre6Aux` — arithmetic inputs for `polarBox_pairFibre6`

The elementary number theory behind the pair-fibre bound
`Work.FIArea2.R6.polarBox_pairFibre6`:

* `tau_sq_le_sum_Icc_four` — *FI* Lemma 2.2 (`k = 4`) applied to `τ²`: for `m ≤ K⁴`,
  `τ(m)² ≤ 2¹⁶ Σ_{d ∣ m, d ≤ K} τ(d)^16`;
* `tau3_le_tau_sq` / `tau3_le_sum_Icc_four` — the same for `τ₃(m) = Σ_{d ∣ m} τ(m/d)`
  (with the convention `τ₃ 0 = 1`), using `τ₃ ≤ τ²`;
* `pairDivisorSums6` — the three divisor sums that appear after the joint count, with the
  logarithmic budget `(log K + 2)^{2^18}` (`2^18 = 262144`), well inside the `460000` of the
  statement.
-/
import Mathlib
import Submission.Work.FIArea3.lemma_2_2
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Work.FIArea3.sum_tau_pow_div_sqrt_le

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## `4 log 4 / log 2 = 8` (the exponent of Lemma 2.2 at `k = 4`) -/

lemma exp_log_four : (4 : ℝ) * Real.log 4 / Real.log 2 = 8 := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h4]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  norm_num

/-! ## Lemma 2.2 at `k = 4` for `τ²` and `τ₃` -/

/-- **Lemma 2.2 (`k = 4`) for `τ²`**: if `m ≤ K⁴` then `τ(m)² ≤ 2¹⁶ Σ_{d ∣ m, d ≤ K} τ(d)^16`. -/
theorem tau_sq_le_sum_Icc_four (m K : ℕ) (hK : 1 ≤ K)
    (h : (m : ℝ) ≤ (K : ℝ) ^ (4 : ℕ)) :
    (((m.divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
      ≤ 65536 * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hz : (((((0 : ℕ).divisors.card : ℕ)) : ℝ)) ^ (2 : ℕ) = 0 := by
      rw [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, zero_pow (by norm_num)]
    rw [hz]
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity)
  · obtain ⟨d, hdvd, hdk, hbound⟩ := Work.FIArea3.lemma_2_2 (k := 4) (by norm_num) hmpos
    have hd1 : 1 ≤ d := Nat.one_le_of_lt (Nat.pos_of_dvd_of_pos hdvd hmpos)
    have hKn : (m : ℕ) ≤ K ^ (4 : ℕ) := by
      have hR : ((m : ℕ) : ℝ) ≤ ((K ^ (4 : ℕ) : ℕ) : ℝ) := by
        rw [show (((K ^ (4 : ℕ) : ℕ)) : ℝ) = (K : ℝ) ^ (4 : ℕ) by push_cast; ring]
        exact h
      exact_mod_cast hR
    have hdK : d ≤ K := by
      have h4 : d ^ (4 : ℕ) ≤ K ^ (4 : ℕ) := le_trans hdk hKn
      exact (Nat.pow_le_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp h4
    have hbd : (((m.divisors.card : ℕ) : ℝ)) ≤ (2 * ((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ) := by
      have he : ((4 : ℕ) : ℝ) * Real.log (((4 : ℕ) : ℝ)) / Real.log 2 = 8 := by
        have h : ((4 : ℕ) : ℝ) = 4 := by norm_num
        rw [h]; exact exp_log_four
      have hb := hbound
      rw [he] at hb
      simpa using hb
    have hsq : (((m.divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
        ≤ 65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) := by
      have h1 : (((m.divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
          ≤ ((2 * ((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hbd 2
      have h2 : ((2 * ((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) ^ (2 : ℕ)
          = 65536 * ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) := by
        rw [← pow_mul]
        norm_num
        ring
      linarith [h1, h2.ge, h2.le]
    have hmem : d ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hd1, hdK⟩
    have hsingle : ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
        ≤ ∑ d' ∈ Finset.Icc 1 K,
            (if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
      have h := Finset.single_le_sum (f := fun d' => if d' ∣ m
            then ((((d'.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0)
          (fun i _ => by split_ifs <;> positivity) hmem
      rwa [if_pos hdvd] at h
    nlinarith [hsq, hsingle]

/-- **`τ₃(m) ≤ τ(m)²`** for `m ≥ 1` (the round-6 `tau3`, `τ₃(n) = Σ_{d ∣ n} τ(n/d)`). -/
lemma tau3_le_tau_sq {m : ℕ} (hm : 1 ≤ m) : tau3 m ≤ (m.divisors.card) ^ (2 : ℕ) := by
  rw [tau3, if_neg (by omega : m ≠ 0)]
  have hm0 : m ≠ 0 := by omega
  calc ∑ d ∈ m.divisors, (m / d).divisors.card
      ≤ ∑ _d ∈ m.divisors, m.divisors.card := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        refine Finset.card_le_card (fun e he => ?_)
        have hed : e ∣ (m / d) := (Nat.mem_divisors.mp he).1
        exact Nat.mem_divisors.mpr ⟨hed.trans (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1), hm0⟩
    _ = m.divisors.card * m.divisors.card := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (m.divisors.card) ^ (2 : ℕ) := by ring

/-- **Lemma 2.2 (`k = 4`) for `τ₃`**: if `m ≤ K⁴` and `1 ≤ K` then
`τ₃(m) ≤ 2¹⁶ Σ_{d ∣ m, d ≤ K} τ(d)^16`. -/
theorem tau3_le_sum_Icc_four (m K : ℕ) (hK : 1 ≤ K)
    (h : (m : ℝ) ≤ (K : ℝ) ^ (4 : ℕ)) :
    ((tau3 m : ℕ) : ℝ)
      ≤ 65536 * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_refl 1, hK⟩
    have hsingle : (1 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K,
        (if d ∣ 0 then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
      have h := Finset.single_le_sum (f := fun d => if d ∣ 0
            then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0)
          (fun i _ => by split_ifs <;> positivity) hmem
      rw [if_pos (dvd_zero 1)] at h
      simpa using h
    have hT : tau3 0 = 1 := rfl
    rw [hT]
    have hsum0 : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K,
        (if d ∣ 0 then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
    push_cast
    linarith [hsingle, hsum0]
  · have h1 : ((tau3 m : ℕ) : ℝ) ≤ (((m.divisors.card : ℕ) : ℝ)) ^ (2 : ℕ) := by
      exact_mod_cast tau3_le_tau_sq hmpos
    exact le_trans h1 (tau_sq_le_sum_Icc_four m K hK h)

/-! ## The three divisor sums after the joint count -/

/-- **The divisor-sum budget of the pair-fibre bound.**  With `τ = (#divisors)`, for every `K ≥ 1`

* `Σ_{d,e ≤ K} τ(d)^17 τ(e)^16/(de) ≤ C (log K + 2)^{2^18}`,
* `Σ_{d,e ≤ K} τ(d)^17 τ(e)^16/√d ≤ C √K·K (log K + 2)^{2^18}`,
* `Σ_{d,e ≤ K} τ(d)^17 τ(e)^16 ≤ C K·K (log K + 2)^{2^18}`.

Each follows by factorising the double sum and applying `sum_tau_pow_div_le`,
`sum_tau_pow_div_sqrt_le` and `sum_tau_pow_le`. -/
theorem pairDivisorSums6 :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K →
      (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))
            * ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / ((d : ℝ) * (e : ℝ)))
        ≤ C * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ))
      ∧ (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))
            * ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / Real.sqrt (d : ℝ))
        ≤ C * (Real.sqrt (K : ℝ) * (K : ℝ)) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ))
      ∧ (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))
            * ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
        ≤ C * ((K : ℝ) * (K : ℝ)) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FIArea2.sum_tau_pow_div_le 17
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FIArea2.sum_tau_pow_div_le 16
  obtain ⟨C3, hC3pos, hC3⟩ := Work.FIArea3.sum_tau_pow_div_sqrt_le 17
  obtain ⟨C4, hC4pos, hC4⟩ := Work.FIArea2.sum_tau_pow_le 16
  obtain ⟨C5, hC5pos, hC5⟩ := Work.FIArea2.sum_tau_pow_le 17
  refine ⟨max (max (C1 * C2) (C3 * C4)) (C5 * C4), ?_, ?_⟩
  · exact lt_of_lt_of_le (mul_pos hC1pos hC2pos) (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro K hK
    set M : ℝ := max (max (C1 * C2) (C3 * C4)) (C5 * C4) with hMdef
    have hB1 : (1 : ℝ) ≤ Real.log (K : ℝ) + 2 := by
      have := Real.log_natCast_nonneg K; linarith
    have hpow1 : (2 : ℕ) ^ (17 : ℕ) + (2 : ℕ) ^ (16 : ℕ) ≤ (2 : ℕ) ^ (18 : ℕ) := by norm_num
    have hpow2 : (2 : ℕ) ^ (17 : ℕ) + ((2 : ℕ) ^ (16 : ℕ)) ≤ (2 : ℕ) ^ (18 : ℕ) := by
      norm_num
    have hpow3 : (2 : ℕ) ^ (17 : ℕ) + ((2 : ℕ) ^ (16 : ℕ))
        ≤ (2 : ℕ) ^ (18 : ℕ) := by norm_num
    have hC12 : 0 ≤ C1 * C2 := le_of_lt (mul_pos hC1pos hC2pos)
    have hC34 : 0 ≤ C3 * C4 := le_of_lt (mul_pos hC3pos hC4pos)
    have hC54 : 0 ≤ C5 * C4 := le_of_lt (mul_pos hC5pos hC4pos)
    have hM12 : C1 * C2 ≤ M := by
      rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    have hM34 : C3 * C4 ≤ M := by
      rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hM54 : C5 * C4 ≤ M := by rw [hMdef]; exact le_max_right _ _
    have hB0 : (0 : ℝ) ≤ Real.log (K : ℝ) + 2 := le_trans zero_le_one hB1
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hsqrtK0 : (0 : ℝ) ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
    have hnn4r : (0 : ℝ) ≤ C4 * (K : ℝ) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (16 : ℕ)) :=
      mul_nonneg (mul_nonneg hC4pos.le hK0) (pow_nonneg hB0 _)
    have hn2 : (0 : ℝ) ≤ ∑ e ∈ Finset.Icc 1 K,
        ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / (e : ℝ) :=
      Finset.sum_nonneg fun e _ => div_nonneg (by positivity) (Nat.cast_nonneg e)
    have hn4 : (0 : ℝ) ≤ ∑ e ∈ Finset.Icc 1 K,
        ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) :=
      Finset.sum_nonneg fun e _ => by positivity
    refine ⟨?_, ?_, ?_⟩
    · have hfac : (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
            ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))
              * ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / ((d : ℝ) * (e : ℝ)))
          = (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ))
            * (∑ e ∈ Finset.Icc 1 K, ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / (e : ℝ)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
        rw [← div_mul_div_comm]
      rw [hfac]
      calc (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ))
            * (∑ e ∈ Finset.Icc 1 K, ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / (e : ℝ))
          ≤ (C1 * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ)))
            * (C2 * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (16 : ℕ))) :=
            mul_le_mul (hC1 K) (hC2 K) hn2 (mul_nonneg hC1pos.le (pow_nonneg hB0 _))
        _ = C1 * C2 * ((Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ))
              * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (16 : ℕ))) := by ac_rfl
        _ = C1 * C2 * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ) + (2 : ℕ) ^ (16 : ℕ)) := by
            rw [pow_add]
        _ ≤ C1 * C2 * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 hpow1) hC12
        _ ≤ M * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) :=
            mul_le_mul_of_nonneg_right hM12 (by positivity)
    · have hfac : (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
            ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))
              * ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / Real.sqrt (d : ℝ))
          = (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / Real.sqrt (d : ℝ))
            * (∑ e ∈ Finset.Icc 1 K, ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
        rw [div_eq_mul_inv]
        ring
      rw [hfac]
      calc (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / Real.sqrt (d : ℝ))
            * (∑ e ∈ Finset.Icc 1 K, ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
          ≤ (C3 * Real.sqrt (K : ℝ) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ)))
            * (C4 * (K : ℝ) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (16 : ℕ))) :=
            mul_le_mul (hC3 K) (hC4 K) hn4 (mul_nonneg (mul_nonneg hC3pos.le hsqrtK0) (pow_nonneg hB0 _))
        _ = C3 * C4 * (Real.sqrt (K : ℝ) * (K : ℝ))
              * ((Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ))
                 * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (16 : ℕ))) := by ac_rfl
        _ = C3 * C4 * (Real.sqrt (K : ℝ) * (K : ℝ))
              * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ) + ((2 : ℕ) ^ (16 : ℕ))) := by
            rw [pow_add]
        _ ≤ C3 * C4 * (Real.sqrt (K : ℝ) * (K : ℝ))
              * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 hpow2)
              (mul_nonneg hC34 (mul_nonneg hsqrtK0 hK0))
        _ ≤ M * (Real.sqrt (K : ℝ) * (K : ℝ)) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) := by
            have hbr : (0 : ℝ) ≤ (Real.sqrt (K : ℝ) * (K : ℝ))
                * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) :=
              mul_nonneg (mul_nonneg hsqrtK0 hK0) (pow_nonneg hB0 _)
            calc C3 * C4 * (Real.sqrt (K : ℝ) * (K : ℝ))
                  * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ))
                = (C3 * C4) * ((Real.sqrt (K : ℝ) * (K : ℝ))
                    * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ))) := by ac_rfl
              _ ≤ M * ((Real.sqrt (K : ℝ) * (K : ℝ))
                    * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ))) :=
                  mul_le_mul_of_nonneg_right hM34 hbr
              _ = M * (Real.sqrt (K : ℝ) * (K : ℝ))
                    * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) := by ac_rfl
    · have hfac : (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
            ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))
              * ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
          = (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)))
            * (∑ e ∈ Finset.Icc 1 K, ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))) := by
        rw [Finset.sum_mul_sum]
      rw [hfac]
      calc (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)))
            * (∑ e ∈ Finset.Icc 1 K, ((((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
          ≤ (C5 * (K : ℝ) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ)))
            * (C4 * (K : ℝ) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (16 : ℕ))) :=
            mul_le_mul (hC5 K) (hC4 K) hn4 (mul_nonneg (mul_nonneg hC5pos.le hK0) (pow_nonneg hB0 _))
        _ = C5 * C4 * ((K : ℝ) * (K : ℝ))
              * ((Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ))
                 * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (16 : ℕ))) := by ac_rfl
        _ = C5 * C4 * ((K : ℝ) * (K : ℝ))
              * (Real.log (K : ℝ) + 2) ^ (((2 : ℕ) ^ (17 : ℕ))
                 + ((2 : ℕ) ^ (16 : ℕ))) := by rw [pow_add]
        _ ≤ C5 * C4 * ((K : ℝ) * (K : ℝ))
              * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 hpow3)
              (mul_nonneg hC54 (mul_nonneg hK0 hK0))
        _ ≤ M * ((K : ℝ) * (K : ℝ)) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) := by
            have hbr : (0 : ℝ) ≤ ((K : ℝ) * (K : ℝ))
                * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) :=
              mul_nonneg (mul_nonneg hK0 hK0) (pow_nonneg hB0 _)
            calc C5 * C4 * ((K : ℝ) * (K : ℝ))
                  * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ))
                = (C5 * C4) * (((K : ℝ) * (K : ℝ))
                    * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ))) := by ac_rfl
              _ ≤ M * (((K : ℝ) * (K : ℝ))
                    * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ))) :=
                  mul_le_mul_of_nonneg_right hM54 hbr
              _ = M * ((K : ℝ) * (K : ℝ))
                    * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) := by ac_rfl

end

end Work.FIArea2.R6
