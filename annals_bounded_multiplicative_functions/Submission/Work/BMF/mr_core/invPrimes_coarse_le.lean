import Mathlib
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_core.invLog_weight_sum_le
import Mathlib.NumberTheory.Chebyshev

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

/-!
# The Mertens/sieve bound `Σ_{p ∈ [P_c,Q_c]} 1/p ≤ B²/16` for the coarse interval

This file proves `Work.BMF.mr_core.invPrimes_coarse_le`, the Mertens/sieve estimate consumed by
`Work.BMF.mr_core.badSum_le`.  Here `P_c, Q_c` are the coarse-system parameters of
`Submission/Work/BMF/mr_core_defs.lean`:
`logPc Y = (log Y)^{47/48}`, `Pc Y = exp(logPc Y)`, `Ac B = exp(B²/64)`,
`logQc B Y = Ac B · logPc Y`, `Qc B Y = exp(logQc B Y)`; thus `log Q_c / log P_c = e^{B²/64}`.

The proof is an explicit Abel summation: writing `1/p = (log p)·w(p)` with `w(t) = 1/(t log t)` and
summing against `θ(x) = Σ_{p ≤ x} log p ≤ (log 4)·x`, one gets
`Σ_{p ∈ [P_c,Q_c]} 1/p ≤ log 4 · log(log Q_c / log P_c) + O(1/log P_c) = log4·B²/64 + o(1)`,
and the hypothesis `Y ≥ exp (exp (7B²))` makes the `o(1)` term negligible against the slack
`B²/16 - log4·B²/64`.  Concretely, the argument uses the summation-by-parts primitives
`abel_identity_real`, `sum_prime_indicator_log_le` and the telescoping estimate
`Work.BMF.mr_core.invLog_weight_sum_le`.
-/



namespace Work.BMF.mr_core

open Finset Real
open scoped BigOperators

noncomputable section

/-- Abel summation by parts over `Icc N M` (real-valued). -/
private lemma abel_identity_real (a b : ℕ → ℝ) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc N M, a n * b n)
      = (∑ k ∈ Finset.Icc N M, a k) * b M
        + ∑ n ∈ Finset.Icc N (M - 1), (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1)) := by
  induction M, hNM using Nat.le_induction with
  | base =>
      have hempty : Finset.Icc N (N - 1) = ∅ := by
        rw [Finset.Icc_eq_empty_iff]; omega
      rw [hempty, Finset.sum_empty, add_zero, Finset.Icc_self, Finset.sum_singleton,
        Finset.sum_singleton]
  | succ m hm ih =>
      have hmm : m + 1 - 1 = m := by omega
      rw [hmm]
      have hsum1 : (∑ n ∈ Finset.Icc N (m + 1), a n * b n)
          = (∑ n ∈ Finset.Icc N m, a n * b n) + a (m + 1) * b (m + 1) :=
        Finset.sum_Icc_succ_top (by omega) (fun n => a n * b n)
      have hsum2 : (∑ k ∈ Finset.Icc N (m + 1), a k)
          = (∑ k ∈ Finset.Icc N m, a k) + a (m + 1) :=
        Finset.sum_Icc_succ_top (by omega) a
      have hsplit : (∑ n ∈ Finset.Icc N m, (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1)))
          = (∑ n ∈ Finset.Icc N (m - 1), (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1)))
            + (∑ k ∈ Finset.Icc N m, a k) * (b m - b (m + 1)) := by
        have := Finset.sum_Icc_succ_top (a := N) (b := m - 1) (by omega : N ≤ (m - 1) + 1)
          (fun n => (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1)))
        rwa [show (m - 1) + 1 = m from by omega] at this
      rw [hsum1, hsum2, hsplit, ih]
      ring

/-- `Σ_{k=N}^{n} [k prime] log k ≤ log 4 · n`. -/
private lemma sum_prime_indicator_log_le (N n : ℕ) :
    (∑ k ∈ Finset.Icc N n, (if k.Prime then Real.log (k : ℝ) else 0)) ≤ Real.log 4 * n := by
  by_cases hn : n < N
  · rw [Finset.Icc_eq_empty_of_lt hn, Finset.sum_empty]
    have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h5 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [h4, h5]
  · rw [not_lt] at hn
    have h1 : (∑ k ∈ Finset.Icc N n, (if k.Prime then Real.log (k : ℝ) else 0))
        = ∑ k ∈ (Finset.Icc N n).filter Nat.Prime, Real.log (k : ℝ) := by
      rw [Finset.sum_filter]
    rw [h1]
    calc ∑ k ∈ (Finset.Icc N n).filter Nat.Prime, Real.log (k : ℝ)
        ≤ ∑ k ∈ Nat.primesLE n, Real.log (k : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            rw [Finset.mem_filter, Finset.mem_Icc] at hk
            rw [Nat.mem_primesLE]
            exact ⟨hk.1.2, hk.2⟩
          · intro k hk _
            rw [Nat.mem_primesLE] at hk
            exact Real.log_nonneg (by exact_mod_cast (le_of_lt hk.2.one_lt))
      _ = Chebyshev.theta n := (Chebyshev.theta_eq_sum_primesLE_log n).symm
      _ ≤ Real.log 4 * n := Chebyshev.theta_le_log4_mul_x (by positivity)

/-- `1/((n+1) log(n+1)) ≤ 1/(n log n)` for `n ≥ 2`. -/
private lemma one_div_mul_log_anti (n : ℕ) (hn : 2 ≤ n) :
    1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hle : (n : ℝ) * Real.log (n : ℝ) ≤ ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) := by
    have h1 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h2 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hnpos (by linarith)
    exact mul_le_mul h1 h2 hlogpos.le (by linarith)
  exact one_div_le_one_div_of_le (mul_pos hnpos hlogpos) hle

theorem invPrimes_coarse_le :
    ∀ (B Y : ℝ), 5 ≤ B → Real.exp (Real.exp (7 * B ^ 2)) ≤ Y →
      (∑ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y),
          1 / (p : ℝ)) ≤ B ^ 2 / 16 := by
  intro B Y hB hY
  set u : ℝ := Work.BMF.mrCore.logPc Y with hu
  set Ac : ℝ := Work.BMF.mrCore.Ac B with hAc
  have hAc_eq : Ac = Real.exp (B ^ 2 / 64) := by rw [hAc, Work.BMF.mrCore.Ac]
  have hAc_ge1 : 1 ≤ Ac := by rw [hAc_eq]; exact Real.one_le_exp (by positivity)
  have hAc_pos : 0 < Ac := lt_of_lt_of_le zero_lt_one hAc_ge1
  have hB2 : (25 : ℝ) ≤ B ^ 2 := by nlinarith
  have hlogY : Real.exp (7 * B ^ 2) ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp (7 * B ^ 2))) hY
    rwa [Real.log_exp] at h
  have hu_ge : Real.exp (329 * B ^ 2 / 48) ≤ u := by
    rw [hu, Work.BMF.mrCore.logPc]
    calc Real.exp (329 * B ^ 2 / 48) = (Real.exp (7 * B ^ 2)) ^ (47 / 48 : ℝ) := by
          rw [← Real.exp_mul]; congr 1; ring
      _ ≤ (Real.log Y) ^ (47 / 48 : ℝ) :=
          Real.rpow_le_rpow (Real.exp_pos _).le hlogY (by norm_num)
  have hu_ge171 : Real.exp 171 ≤ u := by
    have h1 : Real.exp 171 ≤ Real.exp (329 * B ^ 2 / 48) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hu172 : 172 ≤ u := by
    have := Real.add_one_le_exp (171 : ℝ); linarith
  have hu_pos : 0 < u := by linarith
  have hP : Work.BMF.mrCore.Pc Y = Real.exp u := by rw [Work.BMF.mrCore.Pc, ← hu]
  have hQ : Work.BMF.mrCore.Qc B Y = Real.exp (Ac * u) := by
    rw [Work.BMF.mrCore.Qc, Work.BMF.mrCore.logQc, ← hu, ← hAc]
  set N : ℕ := ⌈Work.BMF.mrCore.Pc Y⌉₊ with hN
  set M : ℕ := ⌊Work.BMF.mrCore.Qc B Y⌋₊ with hM
  have hN_ge : Real.exp u ≤ (N : ℝ) := by
    rw [hN, ← hP]; exact Nat.le_ceil _
  have hM_le : (M : ℝ) ≤ Real.exp (Ac * u) := by
    rw [hM, ← hQ]; exact Nat.floor_le (Real.exp_pos _).le
  have hN2 : 2 ≤ N := by
    have h2 : (2 : ℝ) ≤ Real.exp u := by
      have h1e : Real.exp 1 ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have : (2 : ℝ) ≤ (N : ℝ) := le_trans h2 hN_ge
    exact_mod_cast this
  -- `Qc` is far larger than `Pc`, so `M ≥ exp u`
  have hAc_sub : 1 ≤ (Ac - 1) * u := by
    have h1 : B ^ 2 / 64 ≤ Ac - 1 := by
      have := Real.add_one_le_exp (B ^ 2 / 64); rw [hAc_eq]; linarith
    have h2 : (25 : ℝ) / 64 ≤ Ac - 1 := le_trans (by nlinarith) h1
    have h3 : (25 : ℝ) / 64 * 172 ≤ (Ac - 1) * u :=
      mul_le_mul h2 hu172 (by norm_num) (by linarith)
    linarith
  have hAcu : u + 1 ≤ Ac * u := by nlinarith [hAc_sub]
  have hQge : 2 * Real.exp u ≤ Real.exp (Ac * u) := by
    have h1 : Real.exp (u + 1) ≤ Real.exp (Ac * u) := Real.exp_le_exp.mpr hAcu
    rw [Real.exp_add] at h1
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have h3 : 2 * Real.exp u ≤ Real.exp u * Real.exp 1 := by
      rw [mul_comm (Real.exp u) (Real.exp 1)]
      exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos u).le
    linarith
  have hM_ge_P : Real.exp u ≤ (M : ℝ) := by
    have h1 : Real.exp (Ac * u) < (M : ℝ) + 1 := by
      rw [← hQ]; rw [hM]; exact Nat.lt_floor_add_one _
    have h2 : 1 ≤ Real.exp u := Real.one_le_exp hu_pos.le
    linarith [hQge, h1, h2]
  set a : ℕ → ℝ := fun n => if n.Prime then Real.log (n : ℝ) else 0 with ha
  set b : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log (n : ℝ)) with hb
  have hbm : ∀ m : ℕ, b m = 1 / ((m : ℝ) * Real.log (m : ℝ)) := fun m => by rw [hb]
  have ha0 : ∀ m : ℕ, a m = if m.Prime then Real.log (m : ℝ) else 0 := fun m => by rw [ha]
  have hS : (∑ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y),
        1 / (p : ℝ)) = ∑ n ∈ Finset.Icc N M, a n * b n := by
    rw [Work.BMF.primesIn, Work.BMF.natIcc, ← hN, ← hM, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    rw [ha0 n, hbm n]
    by_cases hp : n.Prime
    · rw [if_pos hp, if_pos hp]
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
      have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      have hn0 : (n : ℝ) ≠ 0 := by linarith
      field_simp
    · rw [if_neg hp, if_neg hp]; ring
  rw [hS]
  by_cases hNM : N ≤ M
  · -- main case N ≤ M
    have habel := abel_identity_real a b (by omega : 1 ≤ N) hNM
    rw [habel]
    have hM2 : 2 ≤ M := le_trans hN2 hNM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hlogN_ge : u ≤ Real.log (N : ℝ) := by
      have := Real.log_le_log (Real.exp_pos u) hN_ge
      rwa [Real.log_exp] at this
    have hlogM_le : Real.log (M : ℝ) ≤ Ac * u := by
      have := Real.log_le_log hMpos hM_le
      rwa [Real.log_exp] at this
    have hlogM_ge : u ≤ Real.log (M : ℝ) := by
      have h1 : Real.log (Real.exp u) ≤ Real.log (M : ℝ) :=
        Real.log_le_log (Real.exp_pos u) hM_ge_P
      rwa [Real.log_exp] at h1
    have hlogMpos : 0 < Real.log (M : ℝ) := by linarith
    have hloglog : Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N : ℝ)) ≤ Real.log Ac := by
      have h1 : Real.log (Real.log (M : ℝ)) ≤ Real.log (Ac * u) :=
        Real.log_le_log hlogMpos hlogM_le
      have h2 : Real.log u ≤ Real.log (Real.log (N : ℝ)) :=
        Real.log_le_log hu_pos hlogN_ge
      have h3 : Real.log (Ac * u) - Real.log u = Real.log Ac := by
        rw [← Real.log_div (mul_ne_zero (ne_of_gt hAc_pos) (ne_of_gt hu_pos)) (ne_of_gt hu_pos)]
        congr 1
        field_simp
      linarith
    have hterm1 : (∑ k ∈ Finset.Icc N M, a k) * b M ≤ Real.log 4 / Real.log (M : ℝ) := by
      have hpa : (∑ k ∈ Finset.Icc N M, a k) ≤ Real.log 4 * M := by
        have := sum_prime_indicator_log_le N M
        simpa only [ha0] using this
      have hbM : 0 ≤ b M := by
        rw [hbm M]
        exact div_nonneg zero_le_one (mul_nonneg (by positivity) hlogMpos.le)
      calc (∑ k ∈ Finset.Icc N M, a k) * b M
          ≤ (Real.log 4 * M) * b M := mul_le_mul_of_nonneg_right hpa hbM
        _ = Real.log 4 / Real.log (M : ℝ) := by
            rw [hbm M]
            have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
            have hlne : Real.log (M : ℝ) ≠ 0 := ne_of_gt hlogMpos
            field_simp
    have hterm2 : (∑ n ∈ Finset.Icc N (M - 1),
            (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1)))
        ≤ Real.log 4 * (1 / Real.log (N : ℝ) +
            (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N : ℝ)))) := by
      have hD1 := invLog_weight_sum_le N M hN2 hNM
      have hsum_eq : (∑ n ∈ Finset.Icc N (M - 1), (n : ℝ) * (b n - b (n + 1)))
          = ∑ n ∈ Finset.Icc N (M - 1), (n : ℝ) *
              (1 / ((n : ℝ) * Real.log (n : ℝ)) -
                1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [hbm n, hbm (n + 1), Nat.cast_add, Nat.cast_one]
      calc (∑ n ∈ Finset.Icc N (M - 1), (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1)))
          ≤ ∑ n ∈ Finset.Icc N (M - 1), (Real.log 4 * n) * (b n - b (n + 1)) := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Finset.mem_Icc] at hn
            have hpa : (∑ k ∈ Finset.Icc N n, a k) ≤ Real.log 4 * n := by
              have := sum_prime_indicator_log_le N n
              simpa only [ha0] using this
            have hbd : 0 ≤ b n - b (n + 1) := by
              rw [hbm n, hbm (n + 1), Nat.cast_add, Nat.cast_one]
              exact sub_nonneg.mpr (one_div_mul_log_anti n (le_trans hN2 hn.1))
            exact mul_le_mul_of_nonneg_right hpa hbd
        _ = Real.log 4 * (∑ n ∈ Finset.Icc N (M - 1), (n : ℝ) * (b n - b (n + 1))) := by
            symm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _; ring
        _ ≤ Real.log 4 * (1 / Real.log (N : ℝ) +
              (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
            rw [hsum_eq]
            exact hD1
    have hstep1 : Real.log 4 / Real.log (M : ℝ) ≤ Real.log 4 / u :=
      div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) hu_pos hlogM_ge
    have hstep2 : 1 / Real.log (N : ℝ) +
          (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N : ℝ)))
        ≤ 1 / u + Real.log Ac := by
      have hinv : 1 / Real.log (N : ℝ) ≤ 1 / u :=
        one_div_le_one_div_of_le hu_pos hlogN_ge
      linarith [hinv, hloglog]
    have hfinal : Real.log 4 / u + Real.log 4 * (1 / u + Real.log Ac) ≤ B ^ 2 / 16 := by
      have hlogAc : Real.log Ac = B ^ 2 / 64 := by rw [hAc_eq, Real.log_exp]
      have hlog4le3 : Real.log 4 ≤ 3 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
      have h2log4u : 2 * Real.log 4 / u ≤ B ^ 2 * (4 - Real.log 4) / 64 := by
        have hA : 2 * Real.log 4 / u ≤ 2 * Real.log 4 / 172 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hu172
        have h1 : 2 * Real.log 4 / 172 ≤ 3 / 86 := by
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 172)]; nlinarith [hlog4le3]
        have h2 : (3 : ℝ) / 86 ≤ B ^ 2 * (4 - Real.log 4) / 64 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 64)]
          nlinarith [hB2, hlog4le3]
        linarith
      rw [hlogAc]
      have hring : Real.log 4 / u + Real.log 4 * (1 / u + B ^ 2 / 64)
          = 2 * Real.log 4 / u + Real.log 4 * B ^ 2 / 64 := by ring
      rw [hring]
      nlinarith [h2log4u]
    calc (∑ k ∈ Finset.Icc N M, a k) * b M
            + ∑ n ∈ Finset.Icc N (M - 1), (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1))
        ≤ Real.log 4 / Real.log (M : ℝ) +
            Real.log 4 * (1 / Real.log (N : ℝ) +
              (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N : ℝ)))) :=
          add_le_add hterm1 hterm2
      _ ≤ Real.log 4 / u + Real.log 4 * (1 / u + Real.log Ac) :=
          add_le_add hstep1 (mul_le_mul_of_nonneg_left hstep2 (Real.log_nonneg (by norm_num)))
      _ ≤ B ^ 2 / 16 := hfinal
  · -- degenerate case: N > M
    have hempty : Finset.Icc N M = ∅ := Finset.Icc_eq_empty_iff.mpr hNM
    rw [hempty, Finset.sum_empty]
    positivity

end

end Work.BMF.mr_core
