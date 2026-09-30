import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open Finset

/-- The number of integers in the real interval `[P, Q]` is at most `Q - P + 1`. -/
lemma card_Icc_real_le (P Q : ℝ) (hQ0 : 0 ≤ Q) (hPQ : P ≤ Q) :
    ((Finset.Icc ⌈P⌉₊ ⌊Q⌋₊).card : ℝ) ≤ Q - P + 1 := by
  have hfloorQ : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le hQ0
  have hceilP : P ≤ (⌈P⌉₊ : ℝ) := Nat.le_ceil P
  rcases le_or_gt ⌈P⌉₊ ⌊Q⌋₊ with h | h
  · rw [Nat.card_Icc]
    have hle : ⌈P⌉₊ ≤ ⌊Q⌋₊ + 1 := by omega
    have hcast : ((⌊Q⌋₊ + 1 - ⌈P⌉₊ : ℕ) : ℝ) = ((⌊Q⌋₊ : ℝ) + 1 - ⌈P⌉₊) := by
      rw [Nat.cast_sub hle]; push_cast; ring
    rw [hcast]; linarith
  · have hzero : (Finset.Icc ⌈P⌉₊ ⌊Q⌋₊).card = 0 := by
      rw [Nat.card_Icc]; omega
    rw [hzero, Nat.cast_zero]
    linarith

/-- The number of `n ∈ ℕ ∩ [a,b]` divisible by `p` is at most `⌊b⌋₊ / p`
(equivalently the number of positive multiples of `p` that are `≤ ⌊b⌋₊`). -/
lemma card_filter_dvd_le_floor (a b : ℝ) (p : ℕ) (ha : 0 < a) :
    ((Work.BMF.natIcc a b).filter (fun n => p ∣ n)).card ≤ ⌊b⌋₊ / p := by
  have hsub : (Work.BMF.natIcc a b).filter (fun n => p ∣ n) ⊆
      (Finset.Ioc 0 ⌊b⌋₊).filter (fun n => p ∣ n) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnN, hpd⟩ := hn
    rw [Work.BMF.natIcc, Finset.mem_Icc] at hnN
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_Ioc.mpr
      ⟨by have h1 : 0 < ⌈a⌉₊ := Nat.ceil_pos.mpr ha; omega, hnN.2⟩, hpd⟩
  calc ((Work.BMF.natIcc a b).filter (fun n => p ∣ n)).card
      ≤ ((Finset.Ioc 0 ⌊b⌋₊).filter (fun n => p ∣ n)).card := Finset.card_le_card hsub
    _ = ⌊b⌋₊ / p := Nat.Ioc_filter_dvd_card_eq_div _ _

/-- The number of `n ∈ ℕ ∩ [X, 2X]` having a prime divisor in `[P, Q]` is at most
`12 X (1/K + 1/P)`, provided the interval `[P, Q]` is `K`-short:
`K log(Q/P) < 1`. -/
lemma card_has_prime_factor_le (X K P Q : ℝ) (hX : 1 ≤ X) (hK : 1 ≤ K) (hP : 2 ≤ P)
    (hPQ : P ≤ Q) (hsmall : K * Real.log (Q / P) < 1) :
    ((Work.BMF.natIcc X (2 * X)).filter
        (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n)).card
      ≤ 12 * X * (1 / K + 1 / P) := by
  have hXpos : 0 < X := by linarith
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hQpos : 0 < Q := by linarith
  have h2X0 : 0 ≤ 2 * X := by linarith
  set S : Finset ℕ := Work.BMF.mrDirect.primeSet P Q with hS
  have hmemS : ∀ p : ℕ, p ∈ S ↔ p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q := by
    intro p; rw [hS, Work.BMF.mrDirect.mem_primeSet hQ0]
  -- Step 1: the set of `n` is contained in the union of the `p`-multiples.
  have hsub : (Work.BMF.natIcc X (2 * X)).filter (fun n => ∃ p ∈ S, p ∣ n) ⊆
      S.biUnion (fun p => (Work.BMF.natIcc X (2 * X)).filter (fun n => p ∣ n)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnN, p, hpS, hpd⟩ := hn
    exact Finset.mem_biUnion.mpr ⟨p, hpS, Finset.mem_filter.mpr ⟨hnN, hpd⟩⟩
  have hcard_nat : ((Work.BMF.natIcc X (2 * X)).filter (fun n => ∃ p ∈ S, p ∣ n)).card
      ≤ ∑ p ∈ S, ⌊2 * X⌋₊ / p := by
    calc ((Work.BMF.natIcc X (2 * X)).filter (fun n => ∃ p ∈ S, p ∣ n)).card
        ≤ (S.biUnion (fun p => (Work.BMF.natIcc X (2 * X)).filter (fun n => p ∣ n))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ p ∈ S, ((Work.BMF.natIcc X (2 * X)).filter (fun n => p ∣ n)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ p ∈ S, ⌊2 * X⌋₊ / p := by
          apply Finset.sum_le_sum
          intro p _
          exact card_filter_dvd_le_floor X (2 * X) p hXpos
  -- Step 2: sum bound, each prime `p ≥ P` contributes `≤ 2X/P`.
  have hsum_le : ((∑ p ∈ S, ⌊2 * X⌋₊ / p : ℕ) : ℝ) ≤ (S.card : ℝ) * (2 * X / P) := by
    have h1 : ((∑ p ∈ S, ⌊2 * X⌋₊ / p : ℕ) : ℝ) ≤ ∑ p ∈ S, (2 * X / P) := by
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpp, hPp, _⟩ := (hmemS p).mp hp
      have hppos : 0 < (p : ℝ) := by exact_mod_cast hpp.pos
      calc ((⌊2 * X⌋₊ / p : ℕ) : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) / (p : ℝ) := Nat.cast_div_le
        _ ≤ (2 * X) / (p : ℝ) := by
            apply div_le_div_of_nonneg_right _ hppos.le
            exact Nat.floor_le h2X0
        _ ≤ (2 * X) / P := div_le_div_of_nonneg_left h2X0 hPpos hPp
    have h2 : (∑ p ∈ S, (2 * X / P)) = (S.card : ℝ) * (2 * X / P) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h2] at h1; exact h1
  -- Step 3: `[P, Q]` is short, so `Q - P ≤ 3P/K`.
  have h3 : Q - P ≤ 3 * P / K := by
    have hratio0 : 0 < Q / P := div_pos hQpos hPpos
    have hlog : Real.log (Q / P) < 1 / K := by
      rw [lt_div_iff₀ hKpos]; linarith [hsmall]
    have hlog1 : Real.log (Q / P) < 1 := by
      have h1k : 1 / K ≤ 1 := by rw [div_le_one hKpos]; linarith
      linarith
    have hQP_lt : Q / P < Real.exp 1 := (Real.log_lt_iff_lt_exp hratio0).mp hlog1
    have hQlt : Q < 3 * P := by
      have h1 : Q / P < 3 := lt_trans hQP_lt Real.exp_one_lt_three
      have h2 : Q / P * P < 3 * P := mul_lt_mul_of_pos_right h1 hPpos
      rwa [div_mul_cancel₀ Q (ne_of_gt hPpos)] at h2
    have hineq : 1 - P / Q < 1 / K := by
      have h := Real.one_sub_inv_le_log_of_pos hratio0
      rw [inv_div] at h
      linarith
    have hQP : Q - P < Q / K := by
      have h1 : (1 - P / Q) * Q < (1 / K) * Q := mul_lt_mul_of_pos_right hineq hQpos
      have e1 : (1 - P / Q) * Q = Q - P := by
        rw [sub_mul, one_mul, div_mul_cancel₀ P (ne_of_gt hQpos)]
      have e2 : (1 / K) * Q = Q / K := by ring
      linarith
    have hdiv : Q / K < 3 * P / K := div_lt_div_of_pos_right hQlt hKpos
    linarith
  -- Step 4: at most `3P/K + 1` primes in `[P, Q]`.
  have hScard : (S.card : ℝ) ≤ 3 * P / K + 1 := by
    have hSsub : S ⊆ Finset.Icc ⌈P⌉₊ ⌊Q⌋₊ := by
      rw [hS, Work.BMF.mrDirect.primeSet]
      exact Finset.filter_subset _ _
    have h1 : S.card ≤ (Finset.Icc ⌈P⌉₊ ⌊Q⌋₊).card := Finset.card_le_card hSsub
    calc (S.card : ℝ) ≤ ((Finset.Icc ⌈P⌉₊ ⌊Q⌋₊).card : ℝ) := by exact_mod_cast h1
      _ ≤ Q - P + 1 := card_Icc_real_le P Q hQ0 hPQ
      _ ≤ 3 * P / K + 1 := by linarith
  -- Step 5: elementary arithmetic.
  have hfinal : (3 * P / K + 1) * (2 * X / P) ≤ 12 * X * (1 / K + 1 / P) := by
    have e1 : (3 * P / K + 1) * (2 * X / P) = 6 * X / K + 2 * X / P := by
      field_simp; ring
    have e2 : 12 * X * (1 / K + 1 / P) = 12 * X / K + 12 * X / P := by ring
    rw [e1, e2]
    simp only [div_eq_mul_inv]
    have hXK : 0 ≤ X * K⁻¹ := by positivity
    have hXP : 0 ≤ X * P⁻¹ := by positivity
    linarith
  calc (((Work.BMF.natIcc X (2 * X)).filter (fun n => ∃ p ∈ S, p ∣ n)).card : ℝ)
      ≤ (S.card : ℝ) * (2 * X / P) := by
        have h0 : (((Work.BMF.natIcc X (2 * X)).filter (fun n => ∃ p ∈ S, p ∣ n)).card : ℝ)
            ≤ ((∑ p ∈ S, ⌊2 * X⌋₊ / p : ℕ) : ℝ) := by exact_mod_cast hcard_nat
        linarith
    _ ≤ (3 * P / K + 1) * (2 * X / P) :=
        mul_le_mul_of_nonneg_right hScard (by positivity)
    _ ≤ 12 * X * (1 / K + 1 / P) := hfinal

end Work.BMF.mr_direct
