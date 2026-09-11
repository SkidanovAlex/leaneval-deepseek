import Mathlib
import Submission.Deep

/-!
# Final level inequality for `rao_petal`
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- c0 is between 0 and 1. -/
lemma c0_pos : (0 : ℝ) < c0 := by unfold c0; norm_num
lemma c0_lt_one : c0 < 1 := by unfold c0; norm_num
lemma kap_pos : (0 : ℝ) < kap := by unfold kap; positivity
lemma Bpetal_pos : (0 : ℝ) < Bpetal := by unfold Bpetal; positivity

/-- `log(1/c0) = log(6/5)`: the decay per level is a positive constant. -/
lemma c0_log_decay : (0 : ℝ) < Real.log (1 / c0) := by
  unfold c0
  apply Real.log_pos
  norm_num

/-- Quantitative lower bound on the decay constant: `log(6/5) ≥ 1/6`. -/
lemma c0_log_lower : (1 / 6 : ℝ) ≤ Real.log (1 / c0) := by
  have hc0inv : (1 : ℝ) / c0 = (6 : ℝ) / 5 := by
    unfold c0
    norm_num
  rw [hc0inv]
  have h56 : Real.log ((5 : ℝ) / 6) ≤ (5 : ℝ) / 6 - 1 := by
    exact Real.log_le_sub_one_of_pos (by norm_num)
  have h56log : Real.log ((5 : ℝ) / 6) = -Real.log ((6 : ℝ) / 5) := by
    have hinv : (((6 : ℝ) / 5)⁻¹) = (5 : ℝ) / 6 := by norm_num
    rw [← hinv]
    exact Real.log_inv ((6 : ℝ) / 5)
  linarith

/-- `Bpetal/(2κ) = 2^19`. -/
lemma Bpetal_19 : Bpetal / (2 * kap) = (2 : ℝ) ^ 19 := by
  unfold Bpetal kap
  norm_num

/-- `log c0 = - log (1/c0)`. -/
lemma log_c0_neg : Real.log c0 = -Real.log (1 / c0) := by
  have hc0inv65 : (1 : ℝ) / c0 = (6 : ℝ) / 5 := by unfold c0; norm_num
  have h65 : c0 = ((6 : ℝ) / 5)⁻¹ := by unfold c0; norm_num
  calc
    Real.log c0 = Real.log (((6 : ℝ) / 5)⁻¹) := by rw [h65]
    _ = -Real.log ((6 : ℝ) / 5) := Real.log_inv ((6 : ℝ) / 5)
    _ = -Real.log (1 / c0) := by rw [← hc0inv65]

/-- `c0^j` written with `exp`: `c0^j = exp(-j * log(1/c0))`. -/
lemma c0_pow_exp (j : ℕ) : c0 ^ j = Real.exp (-((j : ℝ) * Real.log (1 / c0))) := by
  have hc0pos : 0 < c0 := by unfold c0; norm_num
  calc
    c0 ^ j = (Real.exp (Real.log c0)) ^ j := by
      conv_lhs => rw [← Real.exp_log hc0pos]
    _ = Real.exp ((j : ℝ) * Real.log c0) := (Real.exp_nat_mul (Real.log c0) j).symm
    _ = Real.exp (-((j : ℝ) * Real.log (1 / c0))) := by
      rw [log_c0_neg]
      congr 1
      ring

/-- From `j ≥ γr/(2κ) - 1` and `r ≥ (Bpetal/γ)·log(2k/ε)` we get `k·c0^j ≤ ε`. -/
lemma level_decay {j k : ℕ} {r γ ε : ℝ}
    (hj : (γ * r / (2 * kap) - 1 : ℝ) ≤ (j : ℝ))
    (hγ0 : 0 < γ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hk2 : 2 ≤ k)
    (hrbig : Bpetal / γ * Real.log (2 * (k : ℝ) / ε) ≤ r) :
    (k : ℝ) * c0 ^ j ≤ ε := by
  let M : ℝ := Real.log ((k : ℝ) / ε)
  let L : ℝ := Real.log (2 * (k : ℝ) / ε)
  let lam : ℝ := Real.log (1 / c0)
  have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hkpos : 0 < (k : ℝ) := by linarith
  have harg1 : 0 < (k : ℝ) / ε := div_pos hkpos hε0
  have harg2 : 0 < 2 * (k : ℝ) / ε := by
    apply div_pos
    · linarith
    · exact hε0
  have hlam0 : 0 < lam := by simpa [lam] using c0_log_decay
  have hlam_low : (1 / 6 : ℝ) ≤ lam := by simpa [lam] using c0_log_lower
  -- M ≤ L
  have hMleL : M ≤ L := by
    dsimp [M, L]
    apply Real.log_le_log harg1
    rw [div_le_div_iff₀ hε0 hε0]
    nlinarith [mul_nonneg (le_of_lt hkpos) (le_of_lt hε0)]
  -- lam ≤ L
  have hlam_le_L : lam ≤ L := by
    dsimp [lam, L]
    have hc0inv65 : (1 : ℝ) / c0 = (6 : ℝ) / 5 := by unfold c0; norm_num
    rw [hc0inv65]
    apply Real.log_le_log (by norm_num : (0 : ℝ) < (6 : ℝ) / 5)
    have h65_4 : (6 : ℝ) / 5 ≤ 4 := by norm_num
    have h4_2k : (4 : ℝ) ≤ 2 * (k : ℝ) := by nlinarith
    have h2k_le : 2 * (k : ℝ) ≤ 2 * (k : ℝ) / ε := by
      rw [le_div_iff₀ hε0]
      have hm := mul_le_mul_of_nonneg_right hε1 (by positivity : 0 ≤ 2 * (k : ℝ))
      simpa [mul_comm, mul_left_comm, mul_assoc] using hm
    exact le_trans (le_trans h65_4 h4_2k) h2k_le
  have hL0 : 0 ≤ L := le_of_lt (lt_of_lt_of_le hlam0 hlam_le_L)
  -- γr/(2κ) is big
  have h1 : Bpetal * L ≤ γ * r := by
    have hm := mul_le_mul_of_nonneg_left hrbig (le_of_lt hγ0)
    field_simp [ne_of_gt hγ0] at hm
    exact hm
  have h2kpos : 0 < 2 * kap := by unfold kap; positivity
  have hdiv : (Bpetal * L) / (2 * kap) ≤ (γ * r) / (2 * kap) :=
    div_le_div_of_nonneg_right h1 (le_of_lt h2kpos)
  set A : ℝ := γ * r / (2 * kap) with hAdef
  have hA_big : (2 : ℝ) ^ 19 * L ≤ A := by
    rw [hAdef]
    calc
      (2 : ℝ) ^ 19 * L = Bpetal / (2 * kap) * L := by rw [← Bpetal_19]
      _ = (Bpetal * L) / (2 * kap) := by rw [div_mul_eq_mul_div]
      _ ≤ (γ * r) / (2 * kap) := hdiv
  have hjA : A - 1 ≤ (j : ℝ) := by rw [hAdef]; exact hj
  have hA19 : (2 : ℝ) ^ 19 * L - 1 ≤ A - 1 := by nlinarith [hA_big]
  -- main numeric bound: L ≤ (2^19 · L - 1) · lam
  have hnum0 : 2 ≤ (2 : ℝ) ^ 19 * (1 / 6) := by norm_num
  have hnum1 : 2 ≤ (2 : ℝ) ^ 19 * lam := by
    have hm := mul_le_mul_of_nonneg_left hlam_low (by norm_num : 0 ≤ (2 : ℝ) ^ 19)
    exact le_trans hnum0 hm
  have hstep : 2 * L ≤ (2 : ℝ) ^ 19 * L * lam := by
    have hm := mul_le_mul_of_nonneg_right hnum1 hL0
    simpa [mul_assoc, mul_comm, mul_left_comm] using hm
  have hsum : L + lam ≤ 2 * L := by nlinarith [hlam_le_L]
  have hmain : L ≤ (2 : ℝ) ^ 19 * L * lam - lam := by nlinarith [hstep, hsum]
  have hmain2 : L ≤ ((2 : ℝ) ^ 19 * L - 1) * lam := by nlinarith [hmain]
  have hMchain : M ≤ ((2 : ℝ) ^ 19 * L - 1) * lam := by nlinarith [hMleL, hmain2]
  have hprod1 : ((2 : ℝ) ^ 19 * L - 1) * lam ≤ (A - 1) * lam :=
    mul_le_mul_of_nonneg_right hA19 (le_of_lt hlam0)
  have hprod2 : (A - 1) * lam ≤ (j : ℝ) * lam :=
    mul_le_mul_of_nonneg_right hjA (le_of_lt hlam0)
  have hMj : M ≤ (j : ℝ) * lam := by nlinarith [hMchain, hprod1, hprod2]
  -- exponentiate
  have h1exp : c0 ^ j = Real.exp (-((j : ℝ) * lam)) := by
    simpa [lam] using (c0_pow_exp j)
  have hneg : -((j : ℝ) * lam) ≤ -M := by nlinarith
  have hexp : Real.exp (-((j : ℝ) * lam)) ≤ Real.exp (-M) := Real.exp_le_exp.mpr hneg
  have hc0le : c0 ^ j ≤ Real.exp (-M) := by
    rw [h1exp]
    exact hexp
  have hfin1 : c0 ^ j ≤ ε / (k : ℝ) := by
    have hexpM : Real.exp (-M) = ε / (k : ℝ) := by
      dsimp [M]
      calc
        Real.exp (-Real.log ((k : ℝ) / ε)) = (Real.exp (Real.log ((k : ℝ) / ε)))⁻¹ := by rw [Real.exp_neg]
        _ = (((k : ℝ) / ε)⁻¹) := by rw [Real.exp_log harg1]
        _ = ε / (k : ℝ) := by rw [inv_div]
    exact le_trans hc0le (le_of_eq hexpM)
  calc
    (k : ℝ) * c0 ^ j = c0 ^ j * (k : ℝ) := by ring
    _ ≤ (ε / (k : ℝ)) * (k : ℝ) := by
      exact mul_le_mul_of_nonneg_right hfin1 (le_of_lt hkpos)
    _ = ε := by field_simp [ne_of_gt hkpos]

/-- rao-level wrapper with concrete hypotheses as they arise in `rao_petal`. -/
lemma final_level_bound {n h m0 j k : ℕ} {r γ ε : ℝ}
    (hj_def : j = m0 / h)
    (hh : 0 < h)
    (hm0ge : γ * (n : ℝ) ≤ (m0 : ℝ))
    (hh_ub : (h : ℝ) ≤ 2 * (kap * (n : ℝ)) / r)
    (hγ0 : 0 < γ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hk2 : 2 ≤ k)
    (hrbig : Bpetal / γ * Real.log (2 * (k : ℝ) / ε) ≤ r)
    (hn : 0 < n) (hr1 : 1 ≤ r) :
    (k : ℝ) * c0 ^ j ≤ ε := by
  apply level_decay (j := j) (k := k) (r := r) (γ := γ) (ε := ε)
  · -- hj : (γr/(2κ) - 1) ≤ j
    have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
    have h2k : 0 < 2 * kap := by unfold kap; positivity
    have hA : (h : ℝ) * r ≤ 2 * kap * (n : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hh_ub (le_of_lt hr0)
      have hrhs : (2 * (kap * (n : ℝ)) / r) * r = 2 * kap * (n : ℝ) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hr0)]
        ring
      rwa [hrhs] at hm
    have hB : (h : ℝ) * r / (2 * kap) ≤ (n : ℝ) := by
      rw [div_le_iff₀ h2k]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hA
    have hC : γ * ((h : ℝ) * r / (2 * kap)) ≤ γ * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hB (le_of_lt hγ0)
    have hD : γ * ((h : ℝ) * r / (2 * kap)) ≤ (m0 : ℝ) := le_trans hC hm0ge
    have hE : (h : ℝ) * (γ * r / (2 * kap)) ≤ (m0 : ℝ) := by
      calc
        (h : ℝ) * (γ * r / (2 * kap)) = γ * ((h : ℝ) * r / (2 * kap)) := by ring_nf
        _ ≤ (m0 : ℝ) := hD
    have hF : γ * r / (2 * kap) ≤ (m0 : ℝ) / (h : ℝ) := by
      rw [le_div_iff₀ hhR]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hE
    -- (m0:ℝ)/(h:ℝ) - 1 ≤ (j:ℝ)
    have hmod : m0 % h < h := Nat.mod_lt m0 (Nat.pos_of_ne_zero (ne_of_gt hh))
    have hfrac : (((m0 % h : ℕ) : ℝ)) / (h : ℝ) < 1 := by
      rw [div_lt_one₀ hhR]
      exact (Nat.cast_lt.mpr hmod)
    have hfracle : (((m0 % h : ℕ) : ℝ)) / (h : ℝ) ≤ 1 := le_of_lt hfrac
    have hm0nat : (m0 : ℕ) = h * (m0 / h) + m0 % h := (Nat.div_add_mod m0 h).symm
    have hm0R1 : (m0 : ℝ) = (((h * (m0 / h) + m0 % h : ℕ) : ℝ)) := by
      exact_mod_cast hm0nat
    have hm0R2 : (m0 : ℝ) = (h : ℝ) * ((m0 / h : ℕ) : ℝ) + ((m0 % h : ℕ) : ℝ) := by
      rw [hm0R1]
      simp [Nat.cast_add, Nat.cast_mul]
    have hmdiv : (m0 : ℝ) / (h : ℝ) = ((m0 / h : ℕ) : ℝ) + (((m0 % h : ℕ) : ℝ)) / (h : ℝ) := by
      rw [hm0R2]
      field_simp [ne_of_gt hhR]
    have hmdiv_le : (m0 : ℝ) / (h : ℝ) - 1 ≤ (j : ℝ) := by
      rw [hj_def]
      rw [hmdiv]
      nlinarith
    linarith
  · exact hγ0
  · exact hε0
  · exact hε1
  · exact hk2
  · exact hrbig

end Submission.Sun
