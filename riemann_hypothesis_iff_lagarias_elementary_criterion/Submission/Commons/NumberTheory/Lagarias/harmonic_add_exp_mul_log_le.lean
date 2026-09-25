import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Int
import Submission.Commons.NumberTheory.Harmonic.positive

namespace Commons.NumberTheory.Lagarias

private lemma self_mul_add_one_le_exp {y : ℝ} (hy : 2 ≤ y) :
    y * (y + 1) ≤ Real.exp y := by
  have hsum : (1 : ℝ) + y + y ^ 2 / 2 + y ^ 3 / 6 ≤ Real.exp y := by
    have hs := Real.sum_le_exp_of_nonneg (show 0 ≤ y by linarith) 4
    norm_num [Finset.sum_range_succ] at hs
    simpa [Finset.sum_range_succ, pow_succ] using hs
  have hpoly : y * (y + 1) ≤ (1 : ℝ) + y + y ^ 2 / 2 + y ^ 3 / 6 := by
    have hsq := sq_nonneg (y - 2)
    nlinarith
  linarith

private lemma log_lower_two {n : ℕ} (hn : 20 ≤ n) : (2 : ℝ) ≤ Real.log (n : ℝ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have hexp2 : Real.exp (2 : ℝ) = (Real.exp 1) ^ 2 := by
    have := Real.exp_nat_mul (1 : ℝ) 2
    simpa [pow_two] using this
  calc
    Real.exp (2 : ℝ) = (Real.exp 1) ^ 2 := hexp2
    _ ≤ (3 : ℝ) ^ 2 := by
      gcongr
      exact le_of_lt Real.exp_one_lt_three
    _ ≤ (n : ℝ) := by
      norm_num
      exact_mod_cast (show (9 : ℕ) ≤ n by omega)

private lemma one_add_log_le_nat_div_log (n : ℕ) (hn : 20 ≤ n) :
    (1 : ℝ) + Real.log (n : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hlog2 : (2 : ℝ) ≤ Real.log (n : ℝ) := log_lower_two hn
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hmain : Real.log (n : ℝ) * (Real.log (n : ℝ) + 1) ≤ (n : ℝ) := by
    have h := self_mul_add_one_le_exp hlog2
    rwa [Real.exp_log hn_pos] at h
  have hmain' : (1 + Real.log (n : ℝ)) * Real.log (n : ℝ) ≤ (n : ℝ) := by
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hmain
  rw [le_div_iff₀ hlog_pos]
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hmain'

private lemma exp_harmonic_le_euler_mul_n_mul_one_add_two_div (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (harmonic n : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * (1 + 2 / (n : ℝ)) := by
  have hHlt : (harmonic n : ℝ) < Real.eulerMascheroniConstant + Real.log (n + 1 : ℕ) := by
    have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
    have hdef : Real.eulerMascheroniSeq n = (harmonic n : ℝ) - Real.log (n + 1 : ℕ) := by
      simp [Real.eulerMascheroniSeq]
    linarith
  have hlt := Real.exp_lt_exp.mpr hHlt
  have hstep :
      Real.exp (harmonic n : ℝ) <
        Real.exp Real.eulerMascheroniConstant * (n : ℝ) * (1 + 2 / (n : ℝ)) := by
    calc
      Real.exp (harmonic n : ℝ)
          < Real.exp (Real.eulerMascheroniConstant + Real.log (n + 1 : ℕ)) := hlt
      _ = Real.exp Real.eulerMascheroniConstant * Real.exp (Real.log (n + 1 : ℕ)) := by
          rw [Real.exp_add]
      _ = Real.exp Real.eulerMascheroniConstant * ((n : ℝ) + 1) := by
          rw [Real.exp_log]
          · norm_num
          · positivity
      _ ≤ Real.exp Real.eulerMascheroniConstant * (n : ℝ) * (1 + 2 / (n : ℝ)) := by
          have hnpos : 0 < (n : ℝ) := by positivity
          have hcoef :
              Real.exp Real.eulerMascheroniConstant * ((n : ℝ) + 1) ≤
                Real.exp Real.eulerMascheroniConstant * ((n : ℝ) * (1 + 2 / (n : ℝ))) := by
            have harg : (n : ℝ) + 1 ≤ (n : ℝ) * (1 + 2 / (n : ℝ)) := by
              field_simp [hnpos.ne']
              linarith
            exact mul_le_mul_of_nonneg_left harg (Real.exp_pos _).le
          simpa [mul_assoc] using hcoef
  exact le_of_lt hstep

private lemma log_add_one_le_log_add_inv {y : ℝ} (hy : 1 ≤ y) :
    Real.log (1 + y) ≤ Real.log y + 1 / y := by
  have hy0 : 0 < y := by linarith
  have hmul : y * (1 + 1 / y) = 1 + y := by
    field_simp [hy0.ne']
    ring
  have hlog : Real.log (1 + y) = Real.log y + Real.log (1 + 1 / y) := by
    rw [← hmul]
    rw [Real.log_mul hy0.ne' (by positivity)]
  rw [hlog]
  have hle : Real.log (1 + 1 / y) ≤ 1 / y := by
    simpa [sub_eq_add_neg, add_comm] using
      (Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / y by positivity))
  linarith

private lemma log_harmonic_le_log_log_add_inv_log (n : ℕ) (hn : 3 ≤ n) :
    Real.log (harmonic n : ℝ) ≤ Real.log (Real.log (n : ℝ)) + 1 / Real.log (n : ℝ) := by
  have hHpos : 0 < (harmonic n : ℝ) := by
    exact_mod_cast harmonic_pos (show n ≠ 0 by omega)
  have hlog_ge_one : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity : 0 < (n : ℝ))]
    exact le_trans (le_of_lt Real.exp_one_lt_three) (by exact_mod_cast hn)
  have h1 : Real.log (harmonic n : ℝ) ≤ Real.log (1 + Real.log (n : ℝ)) := by
    exact Real.log_le_log hHpos (harmonic_le_one_add_log n)
  have h2 : Real.log (1 + Real.log (n : ℝ)) ≤
      Real.log (Real.log (n : ℝ)) + 1 / Real.log (n : ℝ) := by
    exact log_add_one_le_log_add_inv hlog_ge_one
  exact h1.trans h2

private lemma exp_euler_le_two : Real.exp Real.eulerMascheroniConstant ≤ 2 := by
  have hlt : Real.exp Real.eulerMascheroniConstant < Real.exp (2 / 3 : ℝ) :=
    Real.exp_lt_exp.mpr Real.eulerMascheroniConstant_lt_two_thirds
  have hle : Real.exp (2 / 3 : ℝ) ≤ 2 := by
    have h := Real.exp_le_two_add_div_two_sub (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num : (2 / 3 : ℝ) < 2)
    have h2 : (2 + (2 / 3 : ℝ)) / (2 - (2 / 3 : ℝ)) ≤ 2 := by norm_num
    exact h.trans h2
  exact le_trans (le_of_lt hlt) hle

private lemma exp_mul_log_bound (n : ℕ) (hn : 20 ≤ n) :
    (Real.exp Real.eulerMascheroniConstant * (n : ℝ) * (1 + 2 / (n : ℝ))) *
        (Real.log (Real.log (n : ℝ)) + 1 / Real.log (n : ℝ)) ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
        6 * (n : ℝ) / Real.log (n : ℝ) := by
  let eγ : ℝ := Real.exp Real.eulerMascheroniConstant
  let L : ℝ := Real.log (n : ℝ)
  let LL : ℝ := Real.log (Real.log (n : ℝ))
  have hnpos : 0 < (n : ℝ) := by positivity
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hL_ge_two : 2 ≤ L := by
    dsimp [L]
    exact log_lower_two hn
  have hL_ge_one : 1 ≤ L := by linarith
  have hLL_le_L : LL ≤ L := by
    dsimp [LL, L]
    exact Real.log_le_self (le_trans zero_le_one hL_ge_one)
  have hL_mul : L * (L + 1) ≤ (n : ℝ) := by
    have h := self_mul_add_one_le_exp hL_ge_two
    dsimp [L] at h
    rwa [Real.exp_log hnpos] at h
  have hLL_add_one_le_n_div_L : LL + 1 ≤ (n : ℝ) / L := by
    have hmul : (LL + 1) * L ≤ (n : ℝ) := by
      calc
        (LL + 1) * L ≤ (L + 1) * L := by gcongr
        _ = L * (L + 1) := by ring
        _ ≤ (n : ℝ) := hL_mul
    rw [le_div_iff₀ hL_pos]
    simpa [mul_comm] using hmul
  have heγ_pos : 0 ≤ eγ := (Real.exp_pos _).le
  have heγ_le_two : eγ ≤ 2 := by dsimp [eγ]; exact exp_euler_le_two
  have hterm2 : 2 * eγ * LL + 2 * eγ / L ≤ 2 * eγ * (LL + 1) := by
    have h1L : 1 / L ≤ 1 := by
      rw [div_le_iff₀ hL_pos]
      simpa using hL_ge_one
    have h := mul_le_mul_of_nonneg_left h1L (mul_nonneg zero_le_two heγ_pos)
    have h' : 2 * eγ / L ≤ 2 * eγ := by
      simpa [div_eq_mul_inv, mul_assoc] using h
    linarith
  have hterm_sum : eγ * (n : ℝ) / L + 2 * eγ * (LL + 1) ≤ 6 * (n : ℝ) / L := by
    have hmain : (eγ * (n : ℝ) / L + 2 * eγ * (LL + 1)) * L ≤ 6 * (n : ℝ) := by
      have h1L : eγ * (n : ℝ) ≤ 2 * (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right heγ_le_two (Nat.cast_nonneg n)
      have hLL_mul : (LL + 1) * L ≤ (n : ℝ) := by
        simpa [mul_comm] using (le_div_iff₀ hL_pos).mp hLL_add_one_le_n_div_L
      have h2L : (2 * eγ * (LL + 1)) * L ≤ 4 * (n : ℝ) := by
        have hcoef_nonneg : 0 ≤ 2 * eγ := mul_nonneg zero_le_two heγ_pos
        have hcoef1 := mul_le_mul_of_nonneg_left hLL_mul hcoef_nonneg
        have hcoef2 : 2 * eγ ≤ 4 := by nlinarith
        have hcoef3 := mul_le_mul_of_nonneg_right hcoef2 (Nat.cast_nonneg n)
        calc
          (2 * eγ * (LL + 1)) * L = (2 * eγ) * ((LL + 1) * L) := by ring
          _ ≤ (2 * eγ) * (n : ℝ) := hcoef1
          _ ≤ 4 * (n : ℝ) := hcoef3
      calc
        (eγ * (n : ℝ) / L + 2 * eγ * (LL + 1)) * L
            = (eγ * (n : ℝ) / L) * L + (2 * eγ * (LL + 1)) * L := by ring
        _ = eγ * (n : ℝ) + (2 * eγ * (LL + 1)) * L := by
            field_simp [hL_pos.ne']
        _ ≤ 2 * (n : ℝ) + 4 * (n : ℝ) := by gcongr
        _ = 6 * (n : ℝ) := by ring
    rw [le_div_iff₀ hL_pos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
  calc
    (eγ * (n : ℝ) * (1 + 2 / (n : ℝ))) * (LL + 1 / L)
        = eγ * (n : ℝ) * LL + eγ * (n : ℝ) / L + 2 * eγ * LL + 2 * eγ / L := by
            field_simp [hnpos.ne', hL_pos.ne']
            ring
    _ ≤ eγ * (n : ℝ) * LL + eγ * (n : ℝ) / L + 2 * eγ * (LL + 1) := by
            linarith
    _ ≤ eγ * (n : ℝ) * LL + 6 * (n : ℝ) / L := by
            linarith
    _ = Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
        6 * (n : ℝ) / Real.log (n : ℝ) := by
            dsimp [eγ, LL, L]

theorem harmonic_add_exp_mul_log_le (n : ℕ) (hn : 20 ≤ n) :
    (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
        7 * (n : ℝ) / Real.log (n : ℝ) := by
  have hH_le_one_add_log : (harmonic n : ℝ) ≤ 1 + Real.log (n : ℝ) :=
    harmonic_le_one_add_log n
  have hH_le_n_div_log : (harmonic n : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) := by
    exact hH_le_one_add_log.trans (one_add_log_le_nat_div_log n hn)
  have hExp := exp_harmonic_le_euler_mul_n_mul_one_add_two_div n (by omega)
  have hLog := log_harmonic_le_log_log_add_inv_log n (by omega)
  have hLog_nonneg : 0 ≤ Real.log (harmonic n : ℝ) := by
    apply Real.log_nonneg
    have hH_ge_one : 1 ≤ (harmonic n : ℝ) := by
      have hlow := log_add_one_le_harmonic n
      have hlog_ge_one : 1 ≤ Real.log (n + 1 : ℕ) := by
        rw [Real.le_log_iff_exp_le (by positivity : 0 < ((n + 1 : ℕ) : ℝ))]
        exact le_trans (le_of_lt Real.exp_one_lt_three)
          (by exact_mod_cast (show 3 ≤ n + 1 by omega))
      exact hlog_ge_one.trans hlow
    exact hH_ge_one
  have hExpRHS_nonneg : 0 ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * (1 + 2 / (n : ℝ)) := by
    positivity
  have hmul := mul_le_mul hExp hLog hLog_nonneg hExpRHS_nonneg
  have hprod := hmul.trans (exp_mul_log_bound n hn)
  have hsum := add_le_add hH_le_n_div_log hprod
  -- close the remaining arithmetic rearrangement
  calc
    (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)
        ≤ (n : ℝ) / Real.log (n : ℝ) +
            (Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
              6 * (n : ℝ) / Real.log (n : ℝ)) := hsum
    _ = Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
          (n : ℝ) / Real.log (n : ℝ) + 6 * (n : ℝ) / Real.log (n : ℝ) := by ring
    _ ≤ Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
          7 * (n : ℝ) / Real.log (n : ℝ) := by
          have hL_pos : 0 < Real.log (n : ℝ) := by
            exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
          have hsumdiv : (n : ℝ) / Real.log (n : ℝ) + 6 * (n : ℝ) / Real.log (n : ℝ) =
              7 * (n : ℝ) / Real.log (n : ℝ) := by
            ring
          rw [← hsumdiv]
          exact le_of_eq (by ring)

end Commons.NumberTheory.Lagarias