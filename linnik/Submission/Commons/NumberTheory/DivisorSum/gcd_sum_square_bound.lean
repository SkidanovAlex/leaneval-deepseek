import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Submission.Commons.Analysis.ExpLog.sum_inv_Icc_le_log

namespace Commons.NumberTheory.DivisorSum

open Finset

/-- The number of multiples of `d` in `{1, …, N}` is `⌊N/d⌋`. -/
lemma card_filter_dvd_Icc (N d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc 1 N).filter (fun a => d ∣ a)).card = N / d := by
  have hcard : (Finset.Icc 1 (N / d)).card = N / d := by
    simp [Nat.card_Icc]
  rw [← hcard]
  refine Finset.card_bij (fun a _ => a / d) ?_ ?_ ?_
  · intro a ha
    obtain ⟨haI, hadvd⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp haI
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right haN⟩
    rw [Nat.one_le_div_iff (by omega : 0 < d)]
    exact Nat.le_of_dvd (by omega : 0 < a) hadvd
  · intro a1 ha1 a2 ha2 heq
    obtain ⟨_, hdvd1⟩ := Finset.mem_filter.mp ha1
    obtain ⟨_, hdvd2⟩ := Finset.mem_filter.mp ha2
    have h1 : d * (a1 / d) = a1 := Nat.mul_div_cancel' hdvd1
    have h2 : d * (a2 / d) = a2 := Nat.mul_div_cancel' hdvd2
    rw [heq] at h1
    exact h1.symm.trans h2
  · intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    refine ⟨d * k, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      have hd0 : 0 < d := by omega
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d k⟩
      calc d * k = k * d := by ring
        _ ≤ N := (Nat.le_div_iff_mul_le hd0).mp hk2
    · exact Nat.mul_div_cancel_left k (by omega : 0 < d)

/-- The sum of `gcd a b` over `1 ≤ a, b ≤ N` is at most `4 N² (log N + 1)`. -/
theorem gcd_sum_square_bound (N : ℕ) :
    ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ((Nat.gcd a b : ℕ) : ℝ)
      ≤ 4 * (N : ℝ) ^ 2 * (Real.log (N : ℝ) + 1) := by
  classical
  -- (1) pointwise: `gcd a b` is a common divisor, so it is bounded by the sum of
  -- all common divisors in `[1, N]`.
  have hpt : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N,
      ((Nat.gcd a b : ℕ) : ℝ) ≤ ∑ d ∈ Icc 1 N, (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0) := by
    intro a ha b hb
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have haN : a ≤ N := (Finset.mem_Icc.mp ha).2
    have hg1 : 1 ≤ Nat.gcd a b := Nat.gcd_pos_of_pos_left b (by omega)
    have hgN : Nat.gcd a b ≤ N :=
      (Nat.le_of_dvd (by omega : 0 < a) (Nat.gcd_dvd_left a b)).trans haN
    have hmem : Nat.gcd a b ∈ Icc 1 N := Finset.mem_Icc.mpr ⟨hg1, hgN⟩
    have hnonneg : ∀ d ∈ Icc 1 N, 0 ≤ (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0) := by
      intro d hd
      by_cases h : d ∣ a ∧ d ∣ b <;> simp [h]
    have hsingle := Finset.single_le_sum hnonneg hmem
    rwa [if_pos ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩] at hsingle
  -- (2) sum the pointwise bound
  have hsum1 : (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ((Nat.gcd a b : ℕ) : ℝ))
      ≤ ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
          (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0) := by
    apply Finset.sum_le_sum; intro a ha
    apply Finset.sum_le_sum; intro b hb
    exact hpt a ha b hb
  -- (3) evaluate the inner double sum for a fixed `d`
  have hinner : ∀ d ∈ Icc 1 N,
      (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0))
        = (d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hcnt : (((Icc 1 N).filter (fun x => d ∣ x)).card : ℝ) = ((N / d : ℕ) : ℝ) := by
      rw [card_filter_dvd_Icc N d hd1]
    have hcol : ∀ a : ℕ,
        (∑ b ∈ Icc 1 N, (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0))
          = if d ∣ a then (d : ℝ) * (((Icc 1 N).filter (fun x => d ∣ x)).card : ℝ) else 0 := by
      intro a
      by_cases hda : d ∣ a
      · rw [if_pos hda]
        have hterm : ∀ b ∈ Icc 1 N,
            (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0)
              = (d : ℝ) * (if d ∣ b then (1 : ℝ) else 0) := by
          intro b hb
          by_cases hdb : d ∣ b
          · rw [if_pos ⟨hda, hdb⟩, if_pos hdb]; ring
          · rw [if_neg (fun h => hdb h.2), if_neg hdb]; ring
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_boole]
      · rw [if_neg hda]
        apply Finset.sum_eq_zero
        intro b hb
        rw [if_neg (fun h => hda h.1)]
    calc (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0))
        = ∑ a ∈ Icc 1 N,
            (if d ∣ a then (d : ℝ) * (((Icc 1 N).filter (fun x => d ∣ x)).card : ℝ) else 0) :=
          Finset.sum_congr rfl (fun a _ => hcol a)
      _ = (d : ℝ) * (((Icc 1 N).filter (fun x => d ∣ x)).card : ℝ)
            * (((Icc 1 N).filter (fun x => d ∣ x)).card : ℝ) := by
          have hterm2 : ∀ a ∈ Icc 1 N,
              (if d ∣ a then (d : ℝ) * (((Icc 1 N).filter (fun x => d ∣ x)).card : ℝ) else 0)
                = (d : ℝ) * (((Icc 1 N).filter (fun x => d ∣ x)).card : ℝ)
                    * (if d ∣ a then (1 : ℝ) else 0) := by
            intro a ha
            by_cases hda : d ∣ a
            · rw [if_pos hda, if_pos hda]; ring
            · rw [if_neg hda, if_neg hda]; ring
          rw [Finset.sum_congr rfl hterm2, ← Finset.mul_sum]
          rw [Finset.sum_boole]
      _ = (d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2 := by rw [hcnt]; ring
  -- (4) reorder the triple sum
  have hreorder : (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
        (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0))
      = ∑ d ∈ Icc 1 N, ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0) := by
    have e1 : (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
          (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0))
        = ∑ a ∈ Icc 1 N, ∑ d ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
          (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro a ha
      exact Finset.sum_comm
    rw [e1]
    exact Finset.sum_comm
  -- (5) termwise bound by `N²/d`
  have hterm_bound : ∀ d ∈ Icc 1 N,
      (d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 * (d : ℝ)⁻¹ := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : 0 < d := by omega
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdc : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hsq : ((N / d : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) / (d : ℝ)) ^ 2 := by
      have h2 : (0 : ℝ) ≤ (N : ℝ) / (d : ℝ) := by positivity
      calc ((N / d : ℕ) : ℝ) ^ 2 = ((N / d : ℕ) : ℝ) * ((N / d : ℕ) : ℝ) := by ring
        _ ≤ ((N : ℝ) / (d : ℝ)) * ((N : ℝ) / (d : ℝ)) :=
              mul_le_mul hdc hdc (Nat.cast_nonneg _) h2
        _ = ((N : ℝ) / (d : ℝ)) ^ 2 := by ring
    calc (d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2
        ≤ (d : ℝ) * ((N : ℝ) / (d : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left hsq (le_of_lt hdR)
      _ = (N : ℝ) ^ 2 * (d : ℝ)⁻¹ := by field_simp
  have hstep3 : (∑ d ∈ Icc 1 N, (d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2)
      ≤ (N : ℝ) ^ 2 * (1 + Real.log (N : ℝ)) := by
    calc (∑ d ∈ Icc 1 N, (d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2)
        ≤ ∑ d ∈ Icc 1 N, (N : ℝ) ^ 2 * (d : ℝ)⁻¹ := Finset.sum_le_sum hterm_bound
      _ = (N : ℝ) ^ 2 * ∑ d ∈ Icc 1 N, (d : ℝ)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (N : ℝ) ^ 2 * (1 + Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (Commons.Analysis.ExpLog.sum_inv_Icc_le_log N)
              (by positivity)
  -- (6) assemble
  have hlog1 : 0 ≤ Real.log (N : ℝ) + 1 := by
    have := Real.log_natCast_nonneg N; linarith
  calc (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ((Nat.gcd a b : ℕ) : ℝ))
      ≤ ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
          (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0) := hsum1
    _ = ∑ d ∈ Icc 1 N, ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
          (if (d ∣ a ∧ d ∣ b) then (d : ℝ) else 0) := hreorder
    _ = ∑ d ∈ Icc 1 N, (d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2 :=
          Finset.sum_congr rfl (fun d hd => hinner d hd)
    _ ≤ (N : ℝ) ^ 2 * (1 + Real.log (N : ℝ)) := hstep3
    _ ≤ 4 * (N : ℝ) ^ 2 * (Real.log (N : ℝ) + 1) := by
          have hA : 0 ≤ (N : ℝ) ^ 2 * (Real.log (N : ℝ) + 1) :=
            mul_nonneg (sq_nonneg _) hlog1
          nlinarith [hA]

end Commons.NumberTheory.DivisorSum