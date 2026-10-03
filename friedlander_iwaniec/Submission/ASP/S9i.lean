/-
  Companion paper, §9: the counting lemma for `E₂₁`, the half `ν > L√D` of (9.12):

      `∑_{n ≤ x} τ(n)³·#{ν > Y : ν² ∣ n} ≪ x (log x)^{71}/Y`.

  The proof is elementary: for `ν² ∣ n` one has `τ(n) ≤ τ(ν²)·τ(n/ν²)` and `τ(ν²) ≤ τ(ν)²`;
  the two classical divisor-sum bounds `∑_{m ≤ M}τ(m)³ ≪ M(log M)^7` and
  `∑_{ν ≤ x}τ(ν)⁶/ν ≪ (log x)^{64}` then give the result after the substitution `n = ν²m`.
-/
import Mathlib
import Submission.Commons.NumberTheory.DivisorSum.sum_tau_pow_le
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.ASP.S9d

namespace Submission.ASP

open Finset

noncomputable section

/-- `τ(ν²) ≤ τ(ν)²`. -/
lemma card_divisors_sq_le_sq (ν : ℕ) : (ν ^ 2).divisors.card ≤ ν.divisors.card ^ 2 := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp
  · have h2 : ν ^ 2 ≠ 0 := pow_ne_zero _ hν
    rw [Nat.card_divisors h2, Nat.card_divisors hν,
      Nat.primeFactors_pow ν (by norm_num : (2 : ℕ) ≠ 0), ← Finset.prod_pow]
    refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => ?_)
    have hfac : (ν ^ 2).factorization p = 2 * ν.factorization p := by
      rw [Nat.factorization_pow]
      simp
    rw [hfac]
    nlinarith [Nat.zero_le (ν.factorization p)]

/-- Reindexing a sum over the multiples of `k` in `[1,x]`: `n = k·m`. -/
lemma sum_filter_dvd_eq_sum_Icc_div (f : ℕ → ℝ) {k x : ℕ} (hk : 0 < k) :
    (∑ n ∈ (Finset.Icc 1 x).filter (fun n => k ∣ n), f n)
      = ∑ m ∈ Finset.Icc 1 (x / k), f (k * m) := by
  refine Finset.sum_bij (fun n _ => n / k) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, hkdvd⟩ := hn
    have hm1 : k * (n / k) = n := Nat.mul_div_cancel' hkdvd
    have hge : 1 ≤ n / k := by
      rcases Nat.eq_zero_or_pos (n / k) with h0 | hpos
      · rw [h0, mul_zero] at hm1; omega
      · exact hpos
    exact Finset.mem_Icc.mpr ⟨hge, Nat.div_le_div_right hnx⟩
  · intro n₁ h₁ n₂ h₂ heq
    rw [Finset.mem_filter] at h₁ h₂
    have h1 := Nat.mul_div_cancel' h₁.2
    have h2 := Nat.mul_div_cancel' h₂.2
    rw [← h1, ← h2, heq]
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmx⟩ := hm
    refine ⟨k * m, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, Dvd.intro m rfl⟩
      · have : 0 < k * m := Nat.mul_pos hk (by omega)
        omega
      · have hmk := (Nat.le_div_iff_mul_le hk).mp hmx
        calc k * m = m * k := by ring
          _ ≤ x := hmk
    · exact Nat.mul_div_cancel_left m hk
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- The `ν`-`n` exchange for a filter depending on both variables. -/
lemma sum_filter_dep_swap {s t : Finset ℕ} (P : ℕ → ℕ → Prop) [DecidableRel P]
    (F : ℕ → ℕ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t.filter (fun b => P a b), F a b)
      = ∑ b ∈ t, ∑ a ∈ s.filter (fun a => P a b), F a b := by
  have h1 : ∀ a, (∑ b ∈ t.filter (fun b => P a b), F a b)
      = ∑ b ∈ t, (if P a b then F a b else 0) := fun a => Finset.sum_filter _ _
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_filter]

/-- **The counting lemma for `E₂₁`**: `∑_{n ≤ x} τ(n)³·#{ν > Y : ν² ∣ n} ≪ x(log x)^{71}/Y`. -/
theorem sum_tau_cube_sqr_dvd_gt_le : ∃ C : ℝ, 0 < C ∧ ∀ (x Y : ℕ), 1 ≤ Y → 1 ≤ x →
    (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ^ 3 *
        (((Finset.Icc 1 x).filter (fun ν => Y < ν ∧ ν ^ 2 ∣ n)).card : ℝ))
      ≤ C * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (Y : ℝ) := by
  classical
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.NumberTheory.DivisorSum.sum_tau_pow_le 3
  obtain ⟨C2, hC2pos, hC2⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 6
  refine ⟨max (C1 * C2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x Y hY hx
  set L : ℝ := Real.log ((x : ℝ) + 2) with hL
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hYpos : (0 : ℝ) < (Y : ℝ) := by
    have : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  -- Step 1: the left-hand side as a double sum
  have hLHS : (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ^ 3 *
        (((Finset.Icc 1 x).filter (fun ν => Y < ν ∧ ν ^ 2 ∣ n)).card : ℝ))
      = ∑ ν ∈ (Finset.Icc 1 x).filter (fun ν => Y < ν),
          ∑ n ∈ (Finset.Icc 1 x).filter (fun n => ν ^ 2 ∣ n), ((n.divisors.card : ℝ)) ^ 3 := by
    have hpt : ∀ n ∈ Finset.Icc 1 x,
        ((n.divisors.card : ℝ)) ^ 3 *
            (((Finset.Icc 1 x).filter (fun ν => Y < ν ∧ ν ^ 2 ∣ n)).card : ℝ)
          = ∑ ν ∈ (Finset.Icc 1 x).filter (fun ν => Y < ν ∧ ν ^ 2 ∣ n),
              ((n.divisors.card : ℝ)) ^ 3 := by
      intro n _
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl hpt,
      sum_filter_dep_swap (fun n ν => Y < ν ∧ ν ^ 2 ∣ n) (fun n _ => ((n.divisors.card : ℝ)) ^ 3)]
    have h1 : ∀ ν ∈ Finset.Icc 1 x,
        (∑ n ∈ (Finset.Icc 1 x).filter (fun n => Y < ν ∧ ν ^ 2 ∣ n), ((n.divisors.card : ℝ)) ^ 3)
          = if Y < ν then
              (∑ n ∈ (Finset.Icc 1 x).filter (fun n => ν ^ 2 ∣ n), ((n.divisors.card : ℝ)) ^ 3)
            else 0 := by
      intro ν _
      by_cases h : Y < ν
      · rw [if_pos h]
        congr 1
        ext n
        rw [Finset.mem_filter, Finset.mem_filter]
        exact ⟨fun hh => ⟨hh.1, hh.2.2⟩, fun hh => ⟨hh.1, h, hh.2⟩⟩
      · rw [if_neg h]
        exact Finset.sum_eq_zero (fun n hn => absurd (Finset.mem_filter.mp hn).2.1 h)
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  rw [hLHS]
  -- Step 2: the inner bound
  have hinner : ∀ ν ∈ (Finset.Icc 1 x).filter (fun ν => Y < ν),
      (∑ n ∈ (Finset.Icc 1 x).filter (fun n => ν ^ 2 ∣ n), ((n.divisors.card : ℝ)) ^ 3)
        ≤ ((ν ^ 2).divisors.card : ℝ) ^ 3 * (C1 * (((x / ν ^ 2 : ℕ)) : ℝ) * L ^ 7) := by
    intro ν hν
    have hν1 : 1 ≤ ν := (Finset.mem_Icc.mp (Finset.mem_filter.mp hν).1).1
    have hYν : Y < ν := (Finset.mem_filter.mp hν).2
    have hν2pos : 0 < ν ^ 2 := by positivity
    rw [sum_filter_dvd_eq_sum_Icc_div (fun n => ((n.divisors.card : ℝ)) ^ 3) hν2pos]
    have hstep : (∑ m ∈ Finset.Icc 1 (x / ν ^ 2), ((ν ^ 2 * m).divisors.card : ℝ) ^ 3)
        ≤ ((ν ^ 2).divisors.card : ℝ) ^ 3 *
            ∑ m ∈ Finset.Icc 1 (x / ν ^ 2), ((m.divisors.card : ℝ)) ^ 3 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun m _ => ?_)
      have h1 : ((ν ^ 2 * m).divisors.card : ℝ)
          ≤ ((ν ^ 2).divisors.card : ℝ) * ((m.divisors.card : ℝ)) := by
        exact_mod_cast Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le (ν ^ 2) m
      calc ((ν ^ 2 * m).divisors.card : ℝ) ^ 3
          ≤ (((ν ^ 2).divisors.card : ℝ) * ((m.divisors.card : ℝ))) ^ 3 :=
            pow_le_pow_left₀ (by positivity) h1 3
        _ = ((ν ^ 2).divisors.card : ℝ) ^ 3 * ((m.divisors.card : ℝ)) ^ 3 := by ring
    refine le_trans hstep ?_
    rcases eq_or_ne (x / ν ^ 2) 0 with h0 | h0
    · rw [h0]
      simp
    · have h1 : (1 : ℕ) ≤ x / ν ^ 2 := Nat.one_le_iff_ne_zero.mpr h0
      have hb := hC1 (x / ν ^ 2) h1
      have hdiv : (((x / ν ^ 2 : ℕ)) : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast Nat.div_le_self x (ν ^ 2)
      have hlog : Real.log (((x / ν ^ 2 : ℕ) : ℝ) + 1) ≤ L := by
        rw [hL]
        refine Real.log_le_log (by positivity) ?_
        linarith
      have hpow : (Real.log (((x / ν ^ 2 : ℕ) : ℝ) + 1)) ^ 7 ≤ L ^ 7 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog 7
      refine le_trans (mul_le_mul_of_nonneg_left hb (by positivity)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
  refine le_trans (Finset.sum_le_sum hinner) ?_
  -- Step 3: extract the constants
  have hfac : (∑ ν ∈ (Finset.Icc 1 x).filter (fun ν => Y < ν),
        ((ν ^ 2).divisors.card : ℝ) ^ 3 * (C1 * (((x / ν ^ 2 : ℕ)) : ℝ) * L ^ 7))
      = C1 * L ^ 7 * ∑ ν ∈ (Finset.Icc 1 x).filter (fun ν => Y < ν),
          ((ν ^ 2).divisors.card : ℝ) ^ 3 * (((x / ν ^ 2 : ℕ)) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    ring
  rw [hfac]
  -- Step 4: `τ(ν²)³·(x/ν²) ≤ (x/Y)·τ(ν)⁶/ν` for `ν > Y`
  have hred : (∑ ν ∈ (Finset.Icc 1 x).filter (fun ν => Y < ν),
        ((ν ^ 2).divisors.card : ℝ) ^ 3 * (((x / ν ^ 2 : ℕ)) : ℝ))
      ≤ ((x : ℝ) / (Y : ℝ)) * ∑ ν ∈ Finset.Icc 1 x, ((ν.divisors.card : ℝ)) ^ 6 / (ν : ℝ) := by
    have hpt : ∀ ν ∈ (Finset.Icc 1 x).filter (fun ν => Y < ν),
        ((ν ^ 2).divisors.card : ℝ) ^ 3 * (((x / ν ^ 2 : ℕ)) : ℝ)
          ≤ ((x : ℝ) / (Y : ℝ)) * (((ν.divisors.card : ℝ)) ^ 6 / (ν : ℝ)) := by
      intro ν hν
      have hYν : Y < ν := (Finset.mem_filter.mp hν).2
      have hν1 : 1 ≤ ν := (Finset.mem_Icc.mp (Finset.mem_filter.mp hν).1).1
      have hνpos : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast (by omega : 0 < ν)
      have htau : ((ν ^ 2).divisors.card : ℝ) ^ 3 ≤ ((ν.divisors.card : ℝ)) ^ 6 := by
        have h := card_divisors_sq_le_sq ν
        have h' : ((ν ^ 2).divisors.card : ℝ) ≤ ((ν.divisors.card : ℝ)) ^ 2 := by exact_mod_cast h
        calc ((ν ^ 2).divisors.card : ℝ) ^ 3 ≤ (((ν.divisors.card : ℝ)) ^ 2) ^ 3 :=
              pow_le_pow_left₀ (by positivity) h' 3
          _ = ((ν.divisors.card : ℝ)) ^ 6 := by ring
      have hxdiv : (((x / ν ^ 2 : ℕ)) : ℝ) ≤ (x : ℝ) / ((ν : ℝ) * (Y : ℝ)) := by
        have h1 : (((x / ν ^ 2 : ℕ)) : ℝ) ≤ (x : ℝ) / (((ν ^ 2 : ℕ)) : ℝ) := Nat.cast_div_le
        have h2 : (((ν ^ 2 : ℕ)) : ℝ) = (ν : ℝ) ^ 2 := by push_cast; ring
        rw [h2] at h1
        refine le_trans h1 (div_le_div_of_nonneg_left (Nat.cast_nonneg x) (by positivity) ?_)
        have : (Y : ℝ) ≤ (ν : ℝ) := by exact_mod_cast le_of_lt hYν
        nlinarith
      calc ((ν ^ 2).divisors.card : ℝ) ^ 3 * (((x / ν ^ 2 : ℕ)) : ℝ)
          ≤ ((ν.divisors.card : ℝ)) ^ 6 * ((x : ℝ) / ((ν : ℝ) * (Y : ℝ))) :=
            mul_le_mul htau hxdiv (by positivity) (by positivity)
        _ = ((x : ℝ) / (Y : ℝ)) * (((ν.divisors.card : ℝ)) ^ 6 / (ν : ℝ)) := by
            field_simp
    have hstep2 : (∑ ν ∈ (Finset.Icc 1 x).filter (fun ν => Y < ν),
          (x : ℝ) / (Y : ℝ) * (((ν.divisors.card : ℝ)) ^ 6 / (ν : ℝ)))
        ≤ (x : ℝ) / (Y : ℝ) * ∑ ν ∈ Finset.Icc 1 x, ((ν.divisors.card : ℝ)) ^ 6 / (ν : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ν _ _ => ?_)
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg x) hYpos.le)
        (div_nonneg (by positivity) (Nat.cast_nonneg ν))
    exact le_trans (Finset.sum_le_sum (fun ν hν => hpt ν hν)) hstep2
  -- Step 5: the `τ⁶/ν` sum and the final bookkeeping
  have htau6 : (∑ ν ∈ Finset.Icc 1 x, ((ν.divisors.card : ℝ)) ^ 6 / (ν : ℝ)) ≤ C2 * L ^ 64 := by
    have h := hC2 x hx
    have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
    rw [h64] at h
    rwa [← hL] at h
  have hb1 : C1 * L ^ 7 * (∑ ν ∈ (Finset.Icc 1 x).filter (fun ν => Y < ν),
        ((ν ^ 2).divisors.card : ℝ) ^ 3 * (((x / ν ^ 2 : ℕ)) : ℝ))
      ≤ C1 * L ^ 7 * ((x : ℝ) / (Y : ℝ) *
          ∑ ν ∈ Finset.Icc 1 x, ((ν.divisors.card : ℝ)) ^ 6 / (ν : ℝ)) :=
    mul_le_mul_of_nonneg_left hred (by positivity)
  have hb2 : C1 * L ^ 7 * ((x : ℝ) / (Y : ℝ) *
        ∑ ν ∈ Finset.Icc 1 x, ((ν.divisors.card : ℝ)) ^ 6 / (ν : ℝ))
      ≤ C1 * L ^ 7 * ((x : ℝ) / (Y : ℝ) * (C2 * L ^ 64)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left htau6 (div_nonneg (Nat.cast_nonneg x) hYpos.le))
      (mul_nonneg hC1pos.le (pow_nonneg hLnn 7))
  refine le_trans (le_trans hb1 hb2) ?_
  have hstep : C1 * L ^ 7 * ((x : ℝ) / (Y : ℝ) * (C2 * L ^ 64))
      = C1 * C2 * (x : ℝ) * L ^ 71 / (Y : ℝ) := by
    rw [show L ^ 71 = L ^ 7 * L ^ 64 by rw [← pow_add]]
    ring
  rw [hstep]
  have hCC : C1 * C2 ≤ max (C1 * C2) 1 := le_max_left _ _
  have hpos : 0 ≤ (x : ℝ) * L ^ 71 / (Y : ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg x) (pow_nonneg hLnn 71)) hYpos.le
  calc C1 * C2 * (x : ℝ) * L ^ 71 / (Y : ℝ)
      = (C1 * C2) * ((x : ℝ) * L ^ 71 / (Y : ℝ)) := by ring
    _ ≤ max (C1 * C2) 1 * ((x : ℝ) * L ^ 71 / (Y : ℝ)) :=
        mul_le_mul_of_nonneg_right hCC hpos
    _ = max (C1 * C2) 1 * (x : ℝ) * L ^ 71 / (Y : ℝ) := by ring


/-- **Companion §9, (9.12), half `ν > Y`, in the concrete form used for `E₂₁`**: with (9.2) the
quantity `EtwoA a t D (Y+1) t` is `≤ √(∑a²)·√(C·t·(log t)^{71}/Y)`. -/
theorem EtwoA_gt_le_concrete (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (t D Y : ℕ) (ht : 1 ≤ t)
    (hY1 : 1 ≤ Y) (hYt : Y ≤ t) {A2 : ℝ}
    (hA2 : (∑ n ∈ Finset.Icc 1 t, a n ^ 2) ≤ A2) :
    ∃ C : ℝ, 0 < C ∧ EtwoA a t D (Y + 1) t
      ≤ Real.sqrt A2 * Real.sqrt (C * (t : ℝ) * (Real.log ((t : ℝ) + 2)) ^ 71 / (Y : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := sum_tau_cube_sqr_dvd_gt_le
  refine ⟨C, hCpos, ?_⟩
  refine le_trans (EtwoA_gt_le a ha t D Y ht
    (X := C * (t : ℝ) * (Real.log ((t : ℝ) + 2)) ^ 71 / (Y : ℝ)) ?_) ?_
  · refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) (hC t Y hY1 ht)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsub' : ((Finset.Icc (Y + 1) t).filter Squarefree).filter (fun ν => ν ^ 2 ∣ n)
        ⊆ (Finset.Icc 1 t).filter (fun ν => Y < ν ∧ ν ^ 2 ∣ n) := by
      intro ν hν
      obtain ⟨hν1, hν2⟩ := Finset.mem_filter.mp hν
      obtain ⟨hν3, hν4⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hν1).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hν4⟩, by omega, hν2⟩
    have hsub : ((((Finset.Icc (Y + 1) t).filter Squarefree).filter
          (fun ν => ν ^ 2 ∣ n)).card : ℝ)
        ≤ (((Finset.Icc 1 t).filter (fun ν => Y < ν ∧ ν ^ 2 ∣ n)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub'
    exact hsub
  · exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hA2) (Real.sqrt_nonneg _)

end

end Submission.ASP
