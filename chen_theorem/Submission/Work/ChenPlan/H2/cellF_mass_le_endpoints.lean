import Mathlib
import Submission.Work.ChenPlan.H2.WindowCells
import Submission.Work.Sieve.RosserLinear.primeRecipsLocalUpper

/-!
# The mass of a window cell is bounded by the Mertens endpoint ratio

`Work.ChenPlan.H2.cellF_mass_le_endpoints`: for every `B > 0` and all large `x`, every window
cell `cellF B x k` (`k ≤ 70`) satisfies

`Σ_{q ∈ cellF B x k} 1/(q-1) ≤ max 0 (log (log (cellHi + 1) / log cellLo)) + 1/10^7`.

The cell is contained in the integer interval `Icc (cellLo B x k) (cellHi B x k)`
(`WindowCells.cellF_subset_Icc`, available because for large `x` every window prime has
`sVal ≥ 5/3 - 2ε > 3/2`), so the left-hand side is at most the prime-reciprocal sum over
`[cellLo, cellHi]`, which is estimated by the local Mertens bound
`Work.Sieve.RosserLinear.primeRecipsLocalUpper`.  The error terms there are `O(log log x / log x)`
and decay to `0`, so they are eventually below the `10^{-7}` slack; this is the numerical part
of the argument, isolated in `eventually_local_error_small`.
-/

open Finset Filter
open scoped BigOperators

namespace Work.ChenPlan.H2

noncomputable section

/-- `1 ≤ siftM x`. -/
lemma one_le_siftM (x : ℕ) : 1 ≤ siftM x := by
  rw [siftM_eq]; omega

/-- `winY x ≥ 2`. -/
lemma two_le_winY (x : ℕ) : 2 ≤ winY x := by
  rw [winY_eq]; omega

/-- **The local Mertens error is eventually below `η`.**  For `siftM x ≤ a ≤ b ≤ winY x`, the
error term `C log (log b / log a) / (log a)^1 + C / (log a)^2` of
`Work.Sieve.RosserLinear.primeRecipsLocalUpper 1` is at most `η` for all large `x`. -/
lemma eventually_local_error_small (C η : ℝ) (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ a b : ℕ, siftM x ≤ a → a ≤ b → b ≤ winY x →
      C * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) / (Real.log (a : ℝ)) ^ (1 : ℝ)
        + C / (Real.log (a : ℝ)) ^ ((1 : ℝ) + 1) ≤ η := by
  have hlog5pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D : ℝ := 400 * C * (1 + Real.log 5) / η with hDdef
  have hDnn : 0 ≤ D := by
    rw [hDdef]; positivity
  filter_upwards [eventually_log_ge (D + 1), Filter.eventually_ge_atTop 4096]
    with x hxK hx4096
  intro a b ha hab hbY
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogx_ge : D + 1 ≤ Real.log (x : ℝ) := hxK
  have hDle : D ≤ Real.log (x : ℝ) := by linarith
  have h4096 : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
  have h12log2 : 12 * Real.log 2 ≤ Real.log (x : ℝ) := by
    have hcast : (4096 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx4096
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4096) hcast
    rwa [h4096] at h
  have hlogx8 : 8 ≤ Real.log (x : ℝ) := by
    nlinarith [Real.log_two_gt_d9]
  have hlogx0 : 0 < Real.log (x : ℝ) := by linarith
  -- the two ends of the interval
  have hM1 : 1 ≤ siftM x := one_le_siftM x
  have ha1 : 1 ≤ a := le_trans hM1 ha
  have hloga : Real.log (x : ℝ) / 10 ≤ Real.log (a : ℝ) := by
    have h1 := log_siftM_ge (x := x) hx1
    have h2 : Real.log (siftM x : ℝ) ≤ Real.log (a : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast ha)
    linarith
  have hloga0 : 0 < Real.log (a : ℝ) := by linarith
  have hb1 : 0 < b := by omega
  have hba : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hlogb : Real.log (b : ℝ) ≤ Real.log (x : ℝ) / 3 + 2 * Real.log 2 := by
    have hwin1 : 1 ≤ winY x - 1 := by
      have := two_le_winY x; omega
    have hwinpos : (0 : ℝ) < (winY x : ℝ) := by
      have : 0 < winY x := by have := two_le_winY x; omega
      exact_mod_cast this
    have hle1 : Real.log (b : ℝ) ≤ Real.log (((winY x : ℕ)) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hb1) (by exact_mod_cast hbY)
    have hcast : ((winY x : ℕ) : ℝ) ≤ 2 * (((winY x - 1 : ℕ)) : ℝ) := by
      have h : winY x ≤ 2 * (winY x - 1) := by omega
      exact_mod_cast h
    have hle2 : Real.log (((winY x : ℕ)) : ℝ) ≤ Real.log 2 + Real.log (((winY x - 1 : ℕ)) : ℝ) := by
      calc Real.log (((winY x : ℕ)) : ℝ) ≤ Real.log (2 * (((winY x - 1 : ℕ)) : ℝ)) :=
            Real.log_le_log hwinpos hcast
        _ = Real.log 2 + Real.log (((winY x - 1 : ℕ)) : ℝ) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
    have hle3 := log_winY_sub_one_le (x := x) (by omega : 0 < x)
    linarith
  have hlogb0 : 0 < Real.log (b : ℝ) := lt_of_lt_of_le hloga0 (Real.log_le_log (by positivity) hba)
  have hratio : Real.log (b : ℝ) / Real.log (a : ℝ) ≤ 5 := by
    rw [div_le_iff₀ hloga0]
    have h5a : 5 * (Real.log (x : ℝ) / 10) ≤ 5 * Real.log (a : ℝ) := by linarith
    nlinarith [hlogb, h12log2, h5a]
  have hlogratio : Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) ≤ Real.log 5 := by
    rcases le_total (Real.log (b : ℝ) / Real.log (a : ℝ)) 1 with h | h
    · exact le_trans (Real.log_nonpos (le_of_lt (div_pos hlogb0 hloga0)) h) hlog5pos.le
    · exact Real.log_le_log (div_pos hlogb0 hloga0) hratio
  -- the two error terms
  have hterm1 : C * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) / (Real.log (a : ℝ)) ^ (1 : ℝ)
      ≤ 10 * C * Real.log 5 / Real.log (x : ℝ) := by
    rw [Real.rpow_one]
    have step1 : C * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) / Real.log (a : ℝ)
        ≤ C * Real.log 5 / Real.log (a : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogratio hC.le) hloga0.le
    have hx10 : 0 < Real.log (x : ℝ) / 10 := by linarith
    have hinv : 1 / Real.log (a : ℝ) ≤ 1 / (Real.log (x : ℝ) / 10) :=
      one_div_le_one_div_of_le hx10 hloga
    have step2 : C * Real.log 5 / Real.log (a : ℝ) ≤ 10 * C * Real.log 5 / Real.log (x : ℝ) := by
      have h2 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ C * Real.log 5)
      calc C * Real.log 5 / Real.log (a : ℝ) = (C * Real.log 5) * (1 / Real.log (a : ℝ)) := by ring
        _ ≤ (C * Real.log 5) * (1 / (Real.log (x : ℝ) / 10)) := h2
        _ = (C * Real.log 5) * (10 / Real.log (x : ℝ)) := by rw [one_div, inv_div]
        _ = 10 * C * Real.log 5 / Real.log (x : ℝ) := by ring
    linarith [step1, step2]
  have hterm2 : C / (Real.log (a : ℝ)) ^ ((1 : ℝ) + 1) ≤ 100 * C / (Real.log (x : ℝ)) ^ 2 := by
    have h2 : ((1 : ℝ) + 1) = 2 := by norm_num
    rw [h2, Real.rpow_two]
    have hx10 : 0 < Real.log (x : ℝ) / 10 := by linarith
    have hsq : (Real.log (x : ℝ) / 10) ^ 2 ≤ (Real.log (a : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hx10.le hloga 2
    have hpos : (0 : ℝ) < (Real.log (x : ℝ) / 10) ^ 2 := by positivity
    have hinv : 1 / (Real.log (a : ℝ)) ^ 2 ≤ 1 / (Real.log (x : ℝ) / 10) ^ 2 :=
      one_div_le_one_div_of_le hpos hsq
    have h3 := mul_le_mul_of_nonneg_left hinv hC.le
    calc C / (Real.log (a : ℝ)) ^ 2 = C * (1 / (Real.log (a : ℝ)) ^ 2) := by ring
      _ ≤ C * (1 / (Real.log (x : ℝ) / 10) ^ 2) := h3
      _ = 100 * C / (Real.log (x : ℝ)) ^ 2 := by
          rw [div_pow, show ((10 : ℝ)) ^ 2 = 100 by norm_num, one_div, inv_div]
          ring
  -- the two numeric bounds
  have hA : 10 * C * Real.log 5 / Real.log (x : ℝ) ≤ η / 2 := by
    rw [div_le_iff₀ hlogx0]
    have hDval : (η / 2) * (400 * C * (1 + Real.log 5) / η) = 200 * C * (1 + Real.log 5) := by
      field_simp
      ring
    have hmul := mul_le_mul_of_nonneg_left hDle (by linarith : (0 : ℝ) ≤ η / 2)
    rw [hDval] at hmul
    nlinarith [hmul, hC.le, hlog5pos]
  have hB : 100 * C / (Real.log (x : ℝ)) ^ 2 ≤ η / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Real.log (x : ℝ)) ^ 2)]
    have hL1 : 1 ≤ Real.log (x : ℝ) := by linarith
    have hDval : (η / 2) * (400 * C * (1 + Real.log 5) / η) = 200 * C * (1 + Real.log 5) := by
      field_simp
      ring
    have hmul := mul_le_mul_of_nonneg_left hDle (by linarith : (0 : ℝ) ≤ η / 2)
    rw [hDval] at hmul
    have hsqle : Real.log (x : ℝ) ≤ (Real.log (x : ℝ)) ^ 2 := by nlinarith
    have hmul2 := mul_le_mul_of_nonneg_left hsqle (by linarith : (0 : ℝ) ≤ η / 2)
    nlinarith [hmul, hmul2, hC.le]
  calc C * Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) / (Real.log (a : ℝ)) ^ (1 : ℝ)
        + C / (Real.log (a : ℝ)) ^ ((1 : ℝ) + 1)
      ≤ 10 * C * Real.log 5 / Real.log (x : ℝ) + 100 * C / (Real.log (x : ℝ)) ^ 2 :=
        add_le_add hterm1 hterm2
    _ ≤ η / 2 + η / 2 := add_le_add hA hB
    _ = η := by ring

/-- The mass of a cell is at most the prime-reciprocal mass of its interval. -/
lemma sum_cellF_le_Icc (B : ℝ) (x k : ℕ) (hM : 1 < (siftM x : ℝ)) (hlvl : 0 < lvlD B x)
    (hσ : sigM B x ≤ 5)
    (hsval : ∀ q ∈ Submission.winPrimes (siftM x) (winY x), 3 / 2 ≤ sVal B x q) (hk : k ≤ 70) :
    (∑ q ∈ cellF B x k, 1 / ((q : ℝ) - 1))
      ≤ ∑ q ∈ (Finset.Icc (cellLo B x k) (cellHi B x k)).filter Nat.Prime,
          1 / ((q : ℝ) - 1) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro q hq
    rw [Finset.mem_filter]
    rw [mem_cellF] at hq
    obtain ⟨hwq, hkq⟩ := hq
    refine ⟨?_, (Submission.mem_winPrimes.mp hwq).1⟩
    rcases lt_or_eq_of_le hk with hlt | heq
    · exact cellF_subset_Icc hlt hM hlvl (hsval q hwq) (by rw [mem_cellF]; exact ⟨hwq, hkq⟩)
    · rw [heq] at hkq ⊢
      have hq' : q ∈ cellF B x 70 := by rw [mem_cellF]; exact ⟨hwq, hkq⟩
      rw [cellF_seventy_empty hσ hM hlvl] at hq'
      simp at hq'
  · intro n hn _
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have h1 : 1 ≤ n := le_trans (le_trans (one_le_siftM x) (le_max_left _ _)) hn.1.1
    have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    exact div_nonneg zero_le_one (by linarith)

theorem cellF_mass_le_endpoints (B : ℝ) (hB : 0 < B) : ∀ᶠ x : ℕ in Filter.atTop, ∀ k : ℕ, k ≤ 70 → (∑ q ∈ Work.ChenPlan.H2.cellF B x k, 1 / ((q : ℝ) - 1)) ≤ max 0 (Real.log (Real.log (((Work.ChenPlan.H2.cellHi B x k) + 1 : ℕ) : ℝ) / Real.log ((Work.ChenPlan.H2.cellLo B x k : ℕ) : ℝ))) + ((1 : ℝ) / 10000000) := by
  obtain ⟨C, hCpos, X₀, hloc⟩ := Work.Sieve.RosserLinear.primeRecipsLocalUpper 1 (by norm_num)
  filter_upwards [eventually_local_error_small C (1 / 10000000) hCpos (by norm_num),
    eventually_siftM_ge X₀, eventually_siftM_le_winY,
    eventually_wVal_le (δ := 1 / 100) (by norm_num),
    eventually_sigM_ge B hB (ε := 1 / 100) (by norm_num) (by norm_num),
    Filter.eventually_ge_atTop 8] with x herr hX₀ hMY hw hσlow hx8
  have hx2 : 2 ≤ x := by omega
  have hlvl : 0 < lvlD B x := lvlD_pos hB hx2
  have hM : 1 < (siftM x : ℝ) := by
    have h2 : 2 ≤ siftM x := by
      rw [siftM_eq]
      have hx1 : ((1 : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
        have h := Real.one_le_rpow (show (1 : ℝ) ≤ (x : ℝ) by exact_mod_cast (by omega : 1 ≤ x))
          (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 10)
        simpa using h
      have := Nat.le_floor hx1
      omega
    exact_mod_cast (by omega : 1 < siftM x)
  have hσ : sigM B x ≤ 5 := sigM_le_five B hB hx8
  have hY1 : 0 < winY x - 1 := by
    have h1 : 1 ≤ siftM x := one_le_siftM x
    have := two_le_winY x
    omega
  have hsval : ∀ q ∈ Submission.winPrimes (siftM x) (winY x), 3 / 2 ≤ sVal B x q := by
    intro q hq
    obtain ⟨hqp, hq3, hqM, hqY⟩ := Submission.mem_winPrimes.mp hq
    have hq0 : 0 < q := by omega
    have hqY' : q ≤ winY x - 1 := by omega
    have h := sVal_ge_sigM_sub_wVal (B := B) hq0 hqY' hM hlvl hY1
    have h5 : (5 : ℝ) - 1 / 100 - (10 / 3 + 1 / 100) = 5 / 3 - 1 / 50 := by norm_num
    linarith [h, hσlow, hw]
  intro k hk
  by_cases hne : (cellF B x k).Nonempty
  · obtain ⟨q, hqmem⟩ := hne
    have hsub := (mem_cellF.mp hqmem).1
    have hklt : k < 70 := by
      rcases lt_or_eq_of_le hk with h | h
      · exact h
      · exfalso
        subst h
        exact Finset.not_nonempty_iff_eq_empty.mpr (cellF_seventy_empty hσ hM hlvl) ⟨q, hqmem⟩
    have hcont := cellF_subset_Icc (B := B) hklt hM hlvl (hsval q hsub) hqmem
    rw [Finset.mem_Icc] at hcont
    obtain ⟨hlo, hhi⟩ := hcont
    have hXY : cellLo B x k ≤ cellHi B x k + 1 := by omega
    have hX0' : X₀ ≤ cellLo B x k := le_trans hX₀ (le_max_left _ _)
    have hbw : cellHi B x k + 1 ≤ winY x := by
      have h1 : cellHi B x k ≤ winY x - 1 := by
        rw [cellHi]; exact min_le_left _ _
      have := two_le_winY x
      omega
    have hloc' := hloc (cellLo B x k) (cellHi B x k + 1) hX0' hXY
    have herr' := herr (cellLo B x k) (cellHi B x k + 1) (le_max_left _ _) hXY hbw
    have hsub' : (cellHi B x k + 1) - 1 = cellHi B x k := by omega
    rw [hsub'] at hloc'
    have hsum := sum_cellF_le_Icc B x k hM hlvl hσ hsval hk
    calc (∑ q ∈ cellF B x k, 1 / ((q : ℝ) - 1))
        ≤ ∑ q ∈ (Finset.Icc (cellLo B x k) (cellHi B x k)).filter Nat.Prime,
            1 / ((q : ℝ) - 1) := hsum
      _ ≤ Real.log (Real.log (((cellHi B x k) + 1 : ℕ) : ℝ) / Real.log ((cellLo B x k : ℕ) : ℝ))
            + (1 / 10000000) := by linarith [hloc', herr']
      _ ≤ max 0 (Real.log (Real.log (((cellHi B x k) + 1 : ℕ) : ℝ)
            / Real.log ((cellLo B x k : ℕ) : ℝ))) + (1 / 10000000) := by
          have := le_max_right (0 : ℝ)
            (Real.log (Real.log (((cellHi B x k) + 1 : ℕ) : ℝ) / Real.log ((cellLo B x k : ℕ) : ℝ)))
          linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    have := le_max_left (0 : ℝ)
      (Real.log (Real.log (((cellHi B x k) + 1 : ℕ) : ℝ) / Real.log ((cellLo B x k : ℕ) : ℝ)))
    linarith

end

end Work.ChenPlan.H2
