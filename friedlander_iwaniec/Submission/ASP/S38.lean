/-
  Companion paper, §9: the two threshold lemmas and the `(R)`-type bound for the honest
  remainder `r̃_full` of the squarefree-supported sequence `ã`.

  * `FI_L` — the split point `L(x) = ⌈x^{1/160}⌉₊` used in (9.12);
  * `exists_ceil_sq_le_Rcut`, `exists_log_pow_le_FI_L`, `exists_thresholds` — the arithmetic
    thresholds for `L(x)`;
  * `FI_rtilde_sum_le` — `∑♭_{d ≤ Rcut x}|r̃_d(m)| ≪ A(x)(log x)^{−λ}` (the `τ⁰`-weighted `(R)`);
  * `FI_rtildeFull_sum_le` — the same for `r̃_full = r̃ + A·gtail`.
-/
import Mathlib
import Submission.ASP.S37
import Submission.ASP.S36
import Submission.ASP.S35
import Submission.ASP.S33
import Submission.ASP.S32
import Submission.ASP.S30
import Submission.ASP.S27


namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The §9 split point `L(x) = ⌈x^{1/160}⌉₊`. -/
noncomputable def FI_L (x : ℕ) : ℕ := Nat.ceil ((x : ℝ) ^ ((1 : ℝ) / 160))

lemma FI_L_pos (x : ℕ) (hx : 1 ≤ x) : 1 ≤ FI_L x := by
  have h : (1 : ℝ) ≤ ((Nat.ceil ((x : ℝ) ^ ((1 : ℝ) / 160)) : ℕ) : ℝ) :=
    le_trans (Real.one_le_rpow (by exact_mod_cast hx) (by norm_num : (0:ℝ) ≤ 1/160))
      (Nat.le_ceil _)
  rw [FI_L]
  exact_mod_cast h

/-- `(⌈x^{1/160}⌉₊ + 1)² ≤ ⌊x^{11/16}⌋₊`. -/
lemma exists_ceil_sq_le_Rcut :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x → (FI_L x + 1) ^ 2 ≤ Submission.Rcut x := by
  refine ⟨100, fun x hx => ?_⟩
  have hx100 : (100 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  set u : ℝ := (x : ℝ) ^ ((1 : ℝ) / 160) with hu
  have hu1 : (1 : ℝ) ≤ u := Real.one_le_rpow hx1 (by norm_num)
  have hceil : ((FI_L x : ℕ) : ℝ) < u + 1 := by
    rw [FI_L, hu]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (le_of_lt hx0) _)
  have hu2 : u * u = (x : ℝ) ^ ((1 : ℝ) / 80) := by
    rw [hu, ← Real.rpow_add hx0]
    norm_num
  have hquad : (((FI_L x + 1) ^ 2 : ℕ) : ℝ) < 9 * (x : ℝ) ^ ((1 : ℝ) / 80) := by
    have hLv : ((FI_L x + 1 : ℕ) : ℝ) < u + 2 := by push_cast; linarith
    have h0 : (0 : ℝ) ≤ ((FI_L x + 1 : ℕ) : ℝ) := by positivity
    have h1 : (0 : ℝ) ≤ u + 2 := by linarith
    have h2 : (u + 2) ^ 2 ≤ 9 * (u * u) := by nlinarith
    calc (((FI_L x + 1) ^ 2 : ℕ) : ℝ) = (((FI_L x + 1 : ℕ) : ℝ)) ^ 2 := by push_cast; ring
      _ < (u + 2) ^ 2 := by nlinarith
      _ ≤ 9 * (u * u) := h2
      _ = 9 * (x : ℝ) ^ ((1 : ℝ) / 80) := by rw [hu2]
  have hpow : (9 : ℝ) ≤ (x : ℝ) ^ ((27 : ℝ) / 40) := by
    have h1 : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ ((27 : ℝ) / 40) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h2 : (9 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
      have hxr : (81 : ℝ) ≤ (x : ℝ) := by linarith
      have h9 : (81 : ℝ) ^ ((1 : ℝ) / 2) = 9 := by
        rw [show (81 : ℝ) = (9 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (9 : ℝ) 2,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9)]
        rw [show ((2 : ℕ) : ℝ) * ((1 : ℝ) / 2) = (1 : ℝ) by norm_num, Real.rpow_one]
      rw [← h9]
      exact Real.rpow_le_rpow (by norm_num) hxr (by norm_num)
    linarith
  have hsplit : (x : ℝ) ^ ((11 : ℝ) / 16)
      = (x : ℝ) ^ ((1 : ℝ) / 80) * (x : ℝ) ^ ((27 : ℝ) / 40) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hmain : (((FI_L x + 1) ^ 2 : ℕ) : ℝ) < (x : ℝ) ^ ((11 : ℝ) / 16) := by
    refine lt_of_lt_of_le hquad ?_
    rw [hsplit]
    have hxpos : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 80) := Real.rpow_nonneg (le_of_lt hx0) _
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hpow hxpos
  rw [Submission.Rcut]
  exact Nat.le_floor (le_of_lt hmain)

/-- `∃X, ∀x ≥ X, (8:ℝ) ≤ (log x)^{2^25}`. -/
lemma exists_log_rpow_ge_eight :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x → (8 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) := by
  refine ⟨100, fun x hx => ?_⟩
  have hxr : (8 : ℝ) ≤ (x : ℝ) := by
    have h : (100 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hlog8 : (2 : ℝ) ≤ Real.log 8 := by
    have h : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h]; linarith [Real.log_two_gt_d9]
  have hlogx : (2 : ℝ) ≤ Real.log x :=
    le_trans hlog8 (Real.log_le_log (by norm_num) hxr)
  have h1 : (Real.log x) ^ (3 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h2 : (Real.log x) ^ (3 : ℝ) = (Real.log x) ^ 3 := Real.rpow_natCast _ 3
  rw [h2] at h1
  have h3 : (8 : ℝ) ≤ (Real.log x) ^ 3 := by
    have h4 : (2 : ℝ) ^ 3 ≤ (Real.log x) ^ 3 := pow_le_pow_left₀ (by norm_num) hlogx 3
    norm_num at h4
    exact h4
  linarith

/-- `∃X, ∀x ≥ X, ⌊x^{11/16}⌋₊·⌈x^{1/160}⌉₊² + 1 ≤ ⌊x^{7/10}(log x)^{2^25}⌋₊`. -/
lemma exists_Rcut_mul_L_sq_le :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      Submission.Rcut x * (FI_L x) ^ 2 + 1 ≤ Submission.X2Y4R3.R3cut x := by
  obtain ⟨X1, hX1⟩ := exists_log_rpow_ge_eight
  refine ⟨max 100 X1, fun x hx => ?_⟩
  have hx100 : 100 ≤ x := le_trans (le_max_left _ _) hx
  have hxX1 : X1 ≤ x := le_trans (le_max_right _ _) hx
  have hxr : (100 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx100
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hlog8 : (8 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) := hX1 x hxX1
  have hR : (Submission.Rcut x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) := Nat.floor_le (by positivity)
  have hL : ((FI_L x : ℕ) : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 160) := by
    have hc : ((FI_L x : ℕ) : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 160) + 1 := by
      rw [FI_L]
      exact Nat.ceil_lt_add_one (Real.rpow_nonneg (le_of_lt hx0) _)
    have hu : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 160) := Real.one_le_rpow hx1 (by norm_num)
    linarith
  have hmid : (Submission.Rcut x : ℝ) * ((FI_L x : ℕ) : ℝ) ^ 2
      ≤ 4 * (x : ℝ) ^ ((7 : ℝ) / 10) := by
    have h1 : (Submission.Rcut x : ℝ) * ((FI_L x : ℕ) : ℝ) ^ 2
        ≤ (x : ℝ) ^ ((11 : ℝ) / 16) * (2 * (x : ℝ) ^ ((1 : ℝ) / 160)) ^ 2 :=
      mul_le_mul hR (pow_le_pow_left₀ (by positivity) hL 2) (by positivity) (by positivity)
    have h2 : (2 * (x : ℝ) ^ ((1 : ℝ) / 160)) ^ 2
        = 4 * (x : ℝ) ^ ((1 : ℝ) / 80) := by
      have h3 : ((x : ℝ) ^ ((1 : ℝ) / 160)) ^ (2 : ℕ)
          = (x : ℝ) ^ ((1 : ℝ) / 80) := by
        rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 160)) 2,
          ← Real.rpow_mul (le_of_lt hx0)]
        norm_num
      rw [mul_pow, h3]
      norm_num
    have h4 : (x : ℝ) ^ ((11 : ℝ) / 16) * (4 * (x : ℝ) ^ ((1 : ℝ) / 80))
        = 4 * (x : ℝ) ^ ((7 : ℝ) / 10) := by
      rw [← mul_assoc, mul_comm ((x : ℝ) ^ ((11 : ℝ) / 16)) 4, mul_assoc,
        ← Real.rpow_add hx0]
      norm_num
    calc (Submission.Rcut x : ℝ) * ((FI_L x : ℕ) : ℝ) ^ 2
        ≤ (x : ℝ) ^ ((11 : ℝ) / 16) * (2 * (x : ℝ) ^ ((1 : ℝ) / 160)) ^ 2 := h1
      _ = (x : ℝ) ^ ((11 : ℝ) / 16) * (4 * (x : ℝ) ^ ((1 : ℝ) / 80)) := by rw [h2]
      _ = 4 * (x : ℝ) ^ ((7 : ℝ) / 10) := h4
  have hnum : ((Submission.Rcut x * (FI_L x) ^ 2 + 1 : ℕ) : ℝ)
      ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
    have hp : ((Submission.Rcut x * (FI_L x) ^ 2 + 1 : ℕ) : ℝ)
        = (Submission.Rcut x : ℝ) * ((FI_L x : ℕ) : ℝ) ^ 2 + 1 := by push_cast; ring
    rw [hp]
    have hx710 : (1 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := Real.one_le_rpow hx1 (by norm_num)
    have h5 : 4 * (x : ℝ) ^ ((7 : ℝ) / 10) + 1 ≤ 8 * (x : ℝ) ^ ((7 : ℝ) / 10) := by linarith
    have h6 : (8 : ℝ) * (x : ℝ) ^ ((7 : ℝ) / 10)
        ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
      rw [mul_comm 8 ((x : ℝ) ^ ((7 : ℝ) / 10))]
      exact mul_le_mul_of_nonneg_left hlog8 (by positivity)
    linarith [hmid]
  rw [Submission.X2Y4R3.R3cut]
  exact Nat.le_floor hnum

/-- `∃X, ∀x ≥ X, (⌈x^{1/160}⌉₊ + 1)² < ⌊x^{7/10}(log x)^{2^25}⌋₊`. -/
lemma exists_L_succ_sq_lt_R3 :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      (FI_L x + 1) ^ 2 < Submission.X2Y4R3.R3cut x := by
  obtain ⟨X1, hX1⟩ := exists_log_rpow_ge_eight
  refine ⟨max 100 X1, fun x hx => ?_⟩
  have hx100 : 100 ≤ x := le_trans (le_max_left _ _) hx
  have hxX1 : X1 ≤ x := le_trans (le_max_right _ _) hx
  have hxr : (100 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx100
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hlog8 : (8 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) := hX1 x hxX1
  set u : ℝ := (x : ℝ) ^ ((1 : ℝ) / 160) with hu
  have hu1 : (1 : ℝ) ≤ u := Real.one_le_rpow hx1 (by norm_num)
  have hceil : ((FI_L x : ℕ) : ℝ) < u + 1 := by
    rw [FI_L, hu]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (le_of_lt hx0) _)
  have hu2 : u * u = (x : ℝ) ^ ((1 : ℝ) / 80) := by
    rw [hu, ← Real.rpow_add hx0]
    norm_num
  have hquad : (((FI_L x + 1) ^ 2 : ℕ) : ℝ) < 9 * (x : ℝ) ^ ((1 : ℝ) / 80) := by
    have hLv : ((FI_L x + 1 : ℕ) : ℝ) < u + 2 := by push_cast; linarith
    have h2 : (u + 2) ^ 2 ≤ 9 * (u * u) := by nlinarith
    calc (((FI_L x + 1) ^ 2 : ℕ) : ℝ) = (((FI_L x + 1 : ℕ) : ℝ)) ^ 2 := by push_cast; ring
      _ < (u + 2) ^ 2 := by nlinarith
      _ ≤ 9 * (u * u) := h2
      _ = 9 * (x : ℝ) ^ ((1 : ℝ) / 80) := by rw [hu2]
  have h10 : (10 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
    have hA : (10 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) := by
      have h3 : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      have h9 : (100 : ℝ) ^ ((1 : ℝ) / 2) = 10 := by
        rw [show (100 : ℝ) = (10 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (10 : ℝ) 2,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
        rw [show ((2 : ℕ) : ℝ) * ((1 : ℝ) / 2) = (1 : ℝ) by norm_num, Real.rpow_one]
      have h10' : (10 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← h9]
        exact Real.rpow_le_rpow (by norm_num) hxr (by norm_num)
      linarith
    have hB : (1 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) := by linarith
    have hAB : (10 : ℝ) * 1 ≤ (x : ℝ) ^ ((11 : ℝ) / 16) * (Real.log x) ^ ((2 : ℝ) ^ 25) :=
      mul_le_mul hA hB (by norm_num) (by positivity)
    linarith

  have hsplit : (x : ℝ) ^ ((7 : ℝ) / 10)
      = (x : ℝ) ^ ((1 : ℝ) / 80) * (x : ℝ) ^ ((11 : ℝ) / 16) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hnum : (((FI_L x + 1) ^ 2 + 1 : ℕ) : ℝ)
      ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
    have hp : (((FI_L x + 1) ^ 2 + 1 : ℕ) : ℝ) = (((FI_L x + 1) ^ 2 : ℕ) : ℝ) + 1 := by
      push_cast; ring
    rw [hp]
    have h5 : (((FI_L x + 1) ^ 2 : ℕ) : ℝ) + 1 ≤ 9 * (x : ℝ) ^ ((1 : ℝ) / 80) + 1 := by
      linarith [hquad]
    have h6 : (9 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 80) + 1 ≤ 10 * (x : ℝ) ^ ((1 : ℝ) / 80) := by
      have h7 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 80) := Real.one_le_rpow hx1 (by norm_num)
      linarith
    rw [hsplit]
    have h8 : (10 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 80)
        ≤ ((x : ℝ) ^ ((1 : ℝ) / 80) * (x : ℝ) ^ ((11 : ℝ) / 16))
          * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
      have hx80 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 80) := Real.rpow_nonneg (by positivity) _
      calc (10 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 80)
          = (x : ℝ) ^ ((1 : ℝ) / 80) * 10 := by ring
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 80)
              * ((x : ℝ) ^ ((11 : ℝ) / 16) * (Real.log x) ^ ((2 : ℝ) ^ 25)) :=
            mul_le_mul_of_nonneg_left h10 hx80
        _ = ((x : ℝ) ^ ((1 : ℝ) / 80) * (x : ℝ) ^ ((11 : ℝ) / 16))
              * (Real.log x) ^ ((2 : ℝ) ^ 25) := by ring
    linarith [h5, h6, h8]
  have hle : (FI_L x + 1) ^ 2 + 1 ≤ Submission.X2Y4R3.R3cut x := by
    rw [Submission.X2Y4R3.R3cut]
    exact Nat.le_floor hnum
  omega


/-- `∃X, ∀x ≥ X, (log(x+2))^b ≤ ⌈x^{1/160}⌉₊`. -/
lemma exists_log_pow_le_FI_L (b : ℝ) :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      (Real.log ((x : ℝ) + 2)) ^ (max b 0) ≤ (FI_L x : ℝ) := by
  obtain ⟨X1, -, hX1⟩ := Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
    (K := 1) (by norm_num) (n := ⌈max b 0⌉₊) (r := (1 : ℝ) / 160) (by norm_num)
  refine ⟨max X1 100, fun x hx => ?_⟩
  have hxX1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hx100 : 100 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : (1 : ℝ) ≤ Real.log ((x : ℝ) + 2) := by
    refine le_trans one_le_log_three (Real.log_le_log (by norm_num) ?_)
    have h2 : (100 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx100
    linarith
  have hstep1 : (Real.log ((x : ℝ) + 2)) ^ (max b 0)
      ≤ (Real.log ((x : ℝ) + 2)) ^ (⌈max b 0⌉₊ : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (Nat.le_ceil _)
  have hstep2 : (Real.log ((x : ℝ) + 2)) ^ (⌈max b 0⌉₊ : ℕ) ≤ (x : ℝ) ^ ((1 : ℝ) / 160) := by
    have := hX1 x hxX1
    simpa using this
  have hstep3 : (x : ℝ) ^ ((1 : ℝ) / 160) ≤ (FI_L x : ℝ) := by
    rw [FI_L]
    exact Nat.le_ceil _
  linarith

/-- The arithmetic thresholds for the §9 split point `L = ⌈x^{1/160}⌉₊`. -/
lemma exists_thresholds (lam2 : ℝ) (hlam2 : 0 ≤ lam2) :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x → ∀ m : ℕ, Submission.Rcut x ≤ m →
      1 ≤ FI_L x ∧ 2 ≤ m ∧ (FI_L x + 1) ^ 2 ≤ m ∧
      (FI_L x + 1) ^ 2 < Submission.X2Y4R3.R3cut x ∧
      Submission.Rcut x * (FI_L x) ^ 2 + 1 ≤ Submission.X2Y4R3.R3cut x ∧
      (Real.log ((x : ℝ) + 2)) ^ (8 * lam2 + 100) ≤ (FI_L x : ℝ) := by
  obtain ⟨X1, hX1⟩ := exists_ceil_sq_le_Rcut
  obtain ⟨X2, hX2⟩ := exists_Rcut_mul_L_sq_le
  obtain ⟨X3, hX3⟩ := exists_L_succ_sq_lt_R3
  obtain ⟨X4, hX4⟩ := exists_log_pow_le_FI_L (8 * lam2 + 100)
  refine ⟨max (max (max (max X1 X2) X3) X4) 64, fun x hx m hm => ?_⟩
  have hx1 : X1 ≤ x := by omega
  have hx2 : X2 ≤ x := by omega
  have hx3 : X3 ≤ x := by omega
  have hx4 : X4 ≤ x := by omega
  have hx64 : 64 ≤ x := by omega
  have hx1' : 1 ≤ x := by omega
  have hL1 : 1 ≤ FI_L x := FI_L_pos x hx1'
  have hsq : (FI_L x + 1) ^ 2 ≤ Submission.Rcut x := hX1 x hx1
  have hRcut4 : 4 ≤ Submission.Rcut x := four_le_Rcut hx64
  have hm4 : 4 ≤ m := le_trans hRcut4 hm
  have hlogmax : (Real.log ((x : ℝ) + 2)) ^ (8 * lam2 + 100) ≤ (FI_L x : ℝ) := by
    refine le_trans (le_of_eq ?_) (hX4 x hx4)
    rw [max_eq_left]
    linarith
  exact ⟨hL1, by omega, le_trans hsq hm, hX3 x hx3,
    hX2 x hx2, hlogmax⟩

/-- **The `τ⁰`-weighted `(R)` for the companion's remainder `r̃` of `ã`.** -/
theorem FI_rtilde_sum_le (lam : ℝ) :
    ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ,
      Submission.Rcut x ≤ m → m ≤ x →
      (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree, |rtilde FIr FIgtil d m|)
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
  obtain ⟨C2, B2, X2, hC2, hcube⟩ := sum_FIa_tau_cube_le
  obtain ⟨Cg, Kg, hCg, hKg, hG⟩ := sum_FIgtil_le
  set B2' : ℝ := max B2 0 with hB2'
  have hB2'0 : 0 ≤ B2' := le_max_right _ _
  set lam2 : ℝ := max lam (B2' / 2) with hlam2
  have hlam2_ge : lam ≤ lam2 := le_max_left _ _
  have hlam2_0 : 0 ≤ lam2 := le_trans (by linarith : (0 : ℝ) ≤ B2' / 2) (le_max_right _ _)
  have hcomp : B2' ≤ 2 * lam2 := by
    have h : B2' / 2 ≤ lam2 := le_max_right _ _
    linarith
  set lamT : ℝ := max (Kg + lam) 0 with hlamT
  have hlamT0 : 0 ≤ lamT := le_max_right _ _
  have hlamTge : Kg + lam ≤ lamT := le_max_left _ _
  obtain ⟨X3, C3, hC3, hT⟩ := FIr_T_le lamT hlamT0
  obtain ⟨X1, C1, hC1, hEone⟩ := FI_Eone_le lam
  have hS2 : ∀ x : ℕ, max ⌈X2⌉₊ 100 ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (3 : ℕ))
        ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2' := by
    intro x hx t ht2 htx
    have hx2 : X2 ≤ (x : ℝ) :=
      le_trans (Nat.le_ceil X2) (by exact_mod_cast (le_trans (le_max_left _ _) hx))
    have hx100 : 100 ≤ x := le_trans (le_max_right _ _) hx
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
      exact le_trans one_le_log_three (Real.log_le_log (by norm_num) h3)
    have h := hcube x hx2 t ht2 htx
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC2.le (by positivity))
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (le_max_left _ _)
  obtain ⟨Xe, Ce, hCe, hEtwo⟩ := FI_Etwo_le B2' C2 lam2 hC2 hB2'0 hcomp (max ⌈X2⌉₊ 100) hS2
  obtain ⟨Xth, hth⟩ := exists_thresholds lam2 hlam2_0
  refine ⟨max (max (max (max X1 X3) Xe) (max Xth 64)) 1, C1 + Ce + Cg * C3,
    by positivity, fun x hx m hm hmtx => ?_⟩
  have hx1 : X1 ≤ x := by omega
  have hx3 : X3 ≤ x := by omega
  have hxe : Xe ≤ x := by omega
  have hxth : Xth ≤ x := by omega
  have hx64 : 64 ≤ x := by omega
  obtain ⟨hL1, hm2, hL2m, hL2R3, hRL2R3, hlogL⟩ := hth x hxth m hm
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
    exact le_trans one_le_log_three (Real.log_le_log (by norm_num) h3)
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlogx1
  have hRcut2 : 2 ≤ Submission.Rcut x := le_trans (by norm_num : 2 ≤ 4) (four_le_Rcut hx64)
  have hm2' : 2 ≤ m := le_trans hRcut2 hm
  have hLm : FI_L x < m := by
    have h1 : FI_L x + 1 ≤ (FI_L x + 1) ^ 2 := by nlinarith
    omega
  have hsl : FI_L x < m.sqrt := by
    have h' : (FI_L x + 1) ≤ m.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using hL2m)
    omega
  have he1 := hEone x hx1 m (FI_L x) hm2' hmtx hL1 hRL2R3
  have hlogL' : (Real.log x) ^ (8 * lam2 + 100) ≤ (FI_L x : ℝ) := by
    refine le_trans (Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ Real.log x)
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < x)) (by linarith)) (by linarith)) hlogL
  have he2 := hEtwo x hxe m (FI_L x) hm2' hmtx hm hL1 hsl hL2R3 hlogL'
  have hT' : |∑ ν ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius ν : ℝ) * FIr (ν ^ 2) m|
      ≤ C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT) := hT x hx3 m hm hmtx
  have hGsum : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree, |FIgtil d|)
      ≤ Cg * (Real.log x) ^ Kg := by
    have h := hG (Submission.Rcut x) hRcut2
    have h' : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree, FIgtil d)
        = (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree, |FIgtil d|) :=
      Finset.sum_congr rfl (fun d _ => (abs_of_nonneg (FIgtil_nonneg d)).symm)
    rw [← h']
    have hlogle : Real.log ((Submission.Rcut x : ℕ) : ℝ) ≤ Real.log x :=
      Real.log_le_log (by positivity) (by exact_mod_cast Submission.Rcut_le_self x)
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hRcut2)))
        hlogle hKg) hCg.le
  have hbound := Rtilde_sum_le_signed_of_inputs FIa FIg FIr FIgtil m (Submission.Rcut x)
    (FI_L x) (le_of_lt hLm)
    (X1 := C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam))
    (E2 := Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam2))
    (T := C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT))
    (fun n => FIa_nonneg n) (fun n => FIg_nonneg n) (FI_approx (m : ℝ)) hT' he1 he2
  refine le_trans hbound ?_
  have hAn : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := by
    have h0 : (0 : ℝ) ≤ Acount FIa (x : ℝ) := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
    rw [FI_Acount_eq] at h0
    linarith
  have h2 : Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam2)
      ≤ Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCe.le hAn)
    exact Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
  have h3 : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree, |FIgtil d|)
        * (C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT))
      ≤ Cg * C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    have hAC3 : (0 : ℝ) ≤ C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT) :=
      mul_nonneg (mul_nonneg hC3.le hAn) (Real.rpow_nonneg hlogx0.le _)
    refine le_trans (mul_le_mul_of_nonneg_right hGsum hAC3) ?_
    have hexp : Kg - lamT ≤ -lam := by linarith
    have hLcomb : (Real.log x) ^ Kg * (Real.log x) ^ (-lamT)
        = (Real.log x) ^ (Kg - lamT) := by
      rw [← Real.rpow_add hlogx0]
      ring_nf
    calc (Cg * (Real.log x) ^ Kg) * (C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT))
        = Cg * C3 * (Submission.Aseq x : ℝ)
            * ((Real.log x) ^ Kg * (Real.log x) ^ (-lamT)) := by ring
      _ = Cg * C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (Kg - lamT) := by rw [hLcomb]
      _ ≤ Cg * C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hlogx1 hexp)
            (mul_nonneg (mul_nonneg hCg.le hC3.le) hAn)

  calc C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
        + Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam2)
        + (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree, |FIgtil d|)
          * (C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamT))
      ≤ C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
        + Ce * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
        + Cg * C3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) :=
        add_le_add (add_le_add le_rfl h2) h3
    _ = (C1 + Ce + Cg * C3) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by ring




/-- **The `τ⁰`-weighted `(R)` for the honest remainder `r̃_full = r̃ + A·gtail` of `ã`.** -/
theorem FI_rtildeFull_sum_le (lam : ℝ) :
    ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ,
      Submission.Rcut x ≤ m → m ≤ x →
      (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        |rtildeFull FIr FIg FIgtil FIa d m|)
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
  obtain ⟨X1, C1, hC1, hR⟩ := FI_rtilde_sum_le lam
  obtain ⟨C2, A2, hC2, hA2, hgt⟩ := FI_gtail_sum_le
  obtain ⟨CA, hCA, hAup⟩ := Submission.X2Y4R.Aseq_le_const_mul_rpow
  obtain ⟨cA, hcA, XA, hAlow⟩ := Submission.X2Y4R.exists_const_mul_rpow_le_Aseq
  set lam' : ℝ := max lam 1 with hlam'
  have hKpos : (0 : ℝ) < CA * C2 * 2 ^ (2 * (A2 + 4)) :=
    mul_pos (mul_pos hCA hC2) (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨Y1, hY1x, hY1⟩ := Submission.poly_tail_le (CA * C2 * 2 ^ (2 * (A2 + 4)))
    ((11 : ℝ) / 16) (2 * (A2 + 4)) (cA / 2) lam' hKpos (by norm_num) (by positivity)
    (by linarith [le_max_right lam (1 : ℝ)])
  refine ⟨max (max (max X1 Y1) XA) 64, C1 + 1, by positivity, fun x hx m hm hmtx => ?_⟩
  have hx1 : X1 ≤ x := by omega
  have hxY1 : Y1 ≤ x := by omega
  have hxXA : XA ≤ x := by omega
  have hx64 : 64 ≤ x := by omega
  have hx3 : 3 ≤ x := by omega
  have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
  have hx0 : (0 : ℝ) < (x : ℝ) := by positivity
  have hm1 : 1 ≤ m := le_trans (by norm_num : 1 ≤ 4) (le_trans (four_le_Rcut hx64) hm)
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hD0 : (0 : ℝ) < (Submission.Rcut x : ℝ) := by
    have := four_le_Rcut hx64
    positivity
  have hDx : ((Submission.Rcut x : ℕ) : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast Submission.Rcut_le_self x
  have hlogx0 : (0 : ℝ) < Real.log x := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rw [Real.log_exp] at h
    linarith
  have hlogx1 : (1 : ℝ) ≤ Real.log x :=
    le_trans one_le_log_three (Real.log_le_log (by norm_num) (by exact_mod_cast hx3))
  have hlogx2 : (2 : ℝ) ≤ 2 * Real.log x := by linarith
  have hlog2x : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  have hAn : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := by
    have h0 : (0 : ℝ) ≤ Acount FIa (x : ℝ) := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
    rw [FI_Acount_eq] at h0
    linarith
  have hR' := hR x hx1 m hm hmtx
  -- the two log factors are bounded by `2 log x`
  have hlogD2 : Real.log (((Submission.Rcut x : ℕ) : ℝ) + 2) ≤ 2 * Real.log x := by
    have h1 : ((Submission.Rcut x : ℕ) : ℝ) + 2 ≤ (x : ℝ) * 2 := by linarith
    have h2 : Real.log (((Submission.Rcut x : ℕ) : ℝ) + 2) ≤ Real.log ((x : ℝ) * 2) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (ne_of_gt hx0) (by norm_num)] at h2
    linarith
  have hlogm2 : Real.log ((m : ℝ) + 2) ≤ 2 * Real.log x := by
    have hmx : (m : ℝ) ≤ (x : ℝ) := by exact_mod_cast hmtx
    have h1 : (m : ℝ) + 2 ≤ (x : ℝ) * 2 := by linarith
    have h2 : Real.log ((m : ℝ) + 2) ≤ Real.log ((x : ℝ) * 2) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (ne_of_gt hx0) (by norm_num)] at h2
    linarith
  have hT : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree, |gtail FIg FIgtil d m|)
      ≤ C2 * (Submission.Rcut x : ℝ) * 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4)) / (m : ℝ) := by
    refine le_trans (hgt (Submission.Rcut x) m hm1) ?_
    have hM : (1 : ℝ) ≤ 2 * Real.log x := by linarith
    have hb1 : (Real.log (((Submission.Rcut x : ℕ) : ℝ) + 2)) ^ A2
        * (Real.log ((m : ℝ) + 2)) ^ 4
        ≤ 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4)) := by
      have h2 : (Real.log (((Submission.Rcut x : ℕ) : ℝ) + 2)) ^ A2
          ≤ (2 * Real.log x) ^ (A2 + 4) := by
        refine le_trans (Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlogD2 hA2) ?_
        exact Real.rpow_le_rpow_of_exponent_le hM (by linarith [hA2])
      have h3 : (Real.log ((m : ℝ) + 2)) ^ 4 ≤ (2 * Real.log x) ^ (A2 + 4) := by
        refine le_trans (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlogm2 4) ?_
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hM (by push_cast; linarith [hA2])
      calc (Real.log (((Submission.Rcut x : ℕ) : ℝ) + 2)) ^ A2 * (Real.log ((m : ℝ) + 2)) ^ 4
          ≤ (2 * Real.log x) ^ (A2 + 4) * (2 * Real.log x) ^ (A2 + 4) :=
            mul_le_mul h2 h3 (by positivity) (by positivity)
        _ = (2 * Real.log x) ^ (2 * (A2 + 4)) := by
            rw [← Real.rpow_add (by linarith : (0 : ℝ) < 2 * Real.log x)]
            ring_nf
        _ = 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4)) :=
            Real.mul_rpow (by norm_num) hlogx0.le
    calc C2 * (Submission.Rcut x : ℝ) * (Real.log (((Submission.Rcut x : ℕ) : ℝ) + 2)) ^ A2
          * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ)
        = C2 * (Submission.Rcut x : ℝ)
            * ((Real.log (((Submission.Rcut x : ℕ) : ℝ) + 2)) ^ A2
              * (Real.log ((m : ℝ) + 2)) ^ 4) / (m : ℝ) := by ring
      _ ≤ C2 * (Submission.Rcut x : ℝ)
            * (2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4))) / (m : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hm0.le
          exact mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = C2 * (Submission.Rcut x : ℝ) * 2 ^ (2 * (A2 + 4))
            * (Real.log x) ^ (2 * (A2 + 4)) / (m : ℝ) := by ring
  -- the piece with the counting function
  have hAcm : |Acount FIa (m : ℝ)| ≤ CA * (m : ℝ) ^ ((3 : ℝ) / 4) := by
    have h0 : (0 : ℝ) ≤ Acount FIa (m : ℝ) := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
    rw [abs_of_nonneg h0]
    exact le_trans (by rw [FI_Acount_eq]; linarith) (hAup m hm1)
  have hm34 : (m : ℝ) ^ ((3 : ℝ) / 4) / (m : ℝ) ≤ 1 := by
    have h1 : (m : ℝ) ^ ((3 : ℝ) / 4) ≤ (m : ℝ) := by
      have h2 := Real.rpow_le_rpow_of_exponent_le hm1R (show ((3 : ℝ) / 4) ≤ (1 : ℝ) by norm_num)
      simpa [Real.rpow_one] using h2
    exact (div_le_one hm0).mpr h1
  have hstep2 : CA * (m : ℝ) ^ ((3 : ℝ) / 4)
        * (C2 * (Submission.Rcut x : ℝ) * 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4)) / (m : ℝ))
      ≤ CA * C2 * 2 ^ (2 * (A2 + 4)) * (x : ℝ) ^ ((11 : ℝ) / 16) * (Real.log x) ^ (2 * (A2 + 4)) := by
    have hkey : CA * (m : ℝ) ^ ((3 : ℝ) / 4)
        * (C2 * (Submission.Rcut x : ℝ) * 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4)) / (m : ℝ))
        = CA * C2 * 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4))
          * ((Submission.Rcut x : ℝ) * ((m : ℝ) ^ ((3 : ℝ) / 4) / (m : ℝ))) := by
      field_simp
    rw [hkey]
    have hb : (Submission.Rcut x : ℝ) * ((m : ℝ) ^ ((3 : ℝ) / 4) / (m : ℝ))
        ≤ (x : ℝ) ^ ((11 : ℝ) / 16) := by
      calc (Submission.Rcut x : ℝ) * ((m : ℝ) ^ ((3 : ℝ) / 4) / (m : ℝ))
          ≤ (Submission.Rcut x : ℝ) * 1 := mul_le_mul_of_nonneg_left hm34 (le_of_lt hD0)
        _ = (Submission.Rcut x : ℝ) := mul_one _
        _ ≤ (x : ℝ) ^ ((11 : ℝ) / 16) := Submission.X2Y4R.Rcut_le_rpow x
    have hb' : CA * C2 * 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4))
        * ((Submission.Rcut x : ℝ) * ((m : ℝ) ^ ((3 : ℝ) / 4) / (m : ℝ)))
        ≤ CA * C2 * 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4)) * (x : ℝ) ^ ((11 : ℝ) / 16) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    exact le_trans hb' (le_of_eq (by ring_nf))
  have hstep3 : CA * C2 * 2 ^ (2 * (A2 + 4)) * (x : ℝ) ^ ((11 : ℝ) / 16) * (Real.log x) ^ (2 * (A2 + 4))
      ≤ (cA / 2) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam') :=
    hY1 x hxY1
  have hstep4 : (cA / 2) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam')
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    have h1 : cA * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) := hAlow x hxXA
    have h2 : (Real.log x) ^ (-lam') ≤ (Real.log x) ^ (-lam) :=
      Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith [le_max_left lam (1 : ℝ)])
    have hx34 : (0 : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hx0.le _
    calc (cA / 2) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam')
        ≤ (cA * (x : ℝ) ^ ((3 : ℝ) / 4)) * (Real.log x) ^ (-lam) := by
          refine mul_le_mul ?_ h2 (Real.rpow_nonneg hlogx0.le _) (mul_nonneg hcA.le hx34)
          nlinarith [mul_nonneg hcA.le hx34]
      _ ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hlogx0.le _)
  have hbound2 : |Acount FIa (m : ℝ)|
        * (C2 * (Submission.Rcut x : ℝ) * 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4)) / (m : ℝ))
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    have hT0 : (0 : ℝ) ≤ C2 * (Submission.Rcut x : ℝ) * 2 ^ (2 * (A2 + 4))
        * (Real.log x) ^ (2 * (A2 + 4)) / (m : ℝ) :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC2.le (le_of_lt hD0)) (by positivity))
        (by positivity)) hm0.le
    refine le_trans (mul_le_mul_of_nonneg_right hAcm hT0) ?_
    exact le_trans hstep2 (le_trans hstep3 hstep4)
  have hfull := RtildeFull_sum_le FIr FIg FIgtil FIa m (Submission.Rcut x)
    (R := C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam))
    (T := C2 * (Submission.Rcut x : ℝ) * 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4)) / (m : ℝ)) hR' hT
  refine le_trans hfull ?_
  calc C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
        + |Acount FIa (m : ℝ)|
          * (C2 * (Submission.Rcut x : ℝ) * 2 ^ (2 * (A2 + 4)) * (Real.log x) ^ (2 * (A2 + 4)) / (m : ℝ))
      ≤ C1 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
        + (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := add_le_add le_rfl hbound2
    _ = (C1 + 1) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by ring

end

end Submission.ASP
