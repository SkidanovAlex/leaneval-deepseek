/-
  Companion paper, §9: the `E₁` estimate and the τ⁰-`(R)` for the modified remainder `r̃`.

  This file assembles

      `E₁ = ∑♭_{ν ≤ L}∑♭_{d ≤ D}|r_{[ν²,d]}(t)| ≤ ∑³_{k ≤ DL²}τ(k)|r_k(t)|`  (`S9b.E1_le`)

  together with the `τ²`-version of `(R₃) ⟹ (R′₃)` (Cauchy–Schwarz with weight `τ` instead of
  `τ^{10}`) and the elementary bounds for the two halves of the weight, giving

      `E₁ ≪ A(x)(log x)^{−λ}` for every `λ`, provided `D·L² ≤ R3cut x`.
-/
import Mathlib
import Submission.ASP.S35
import Submission.ASP.S9b
import Submission.ASP.S9c
import Submission.ASP.S9d

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ### The `τ²`-weighted `(R₃) ⟹ (R′₃)` -/

/-- **`(R₃) ⟹ (R′₃)` with weight `τ²`** (instead of the paper's `τ^{10}`): Cauchy–Schwarz in the
form `(∑τ|r|)² ≤ (∑|r|)(∑τ²|r|)`. -/
theorem Rprime3_le_tau2 (r : ℕ → ℝ) (D : ℕ) {W R3 : ℝ}
    (hW : (∑ d ∈ (Finset.Icc 1 D).filter CubefreeN,
        ((d.divisors.card : ℝ)) ^ 2 * |r d|) ≤ W)
    (hR3 : (∑ d ∈ (Finset.Icc 1 D).filter CubefreeN, |r d|) ≤ R3) :
    (∑ d ∈ (Finset.Icc 1 D).filter CubefreeN, (d.divisors.card : ℝ) * |r d|)
      ≤ Real.sqrt W * Real.sqrt R3 := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 D).filter CubefreeN with hS
  have hcs := sq_sum_mul_le_sum_mul_sum_mul_sq (s := S) (x := fun d => |r d|)
    (y := fun d => (d.divisors.card : ℝ)) (fun d _ => abs_nonneg _) (fun d _ => by positivity)
  have hX : (0 : ℝ) ≤ ∑ d ∈ S, |r d| := Finset.sum_nonneg (fun d _ => abs_nonneg _)
  have hX' : (0 : ℝ) ≤ ∑ d ∈ S, |r d| * (d.divisors.card : ℝ) :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (abs_nonneg _) (by positivity))
  have hWnn : (0 : ℝ) ≤ ∑ d ∈ S, ((d.divisors.card : ℝ)) ^ 2 * |r d| :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (by positivity) (abs_nonneg _))
  have hW' : (∑ d ∈ S, |r d| * ((d.divisors.card : ℝ)) ^ 2) ≤ W :=
    le_trans (le_of_eq (Finset.sum_congr rfl (fun d _ => by ring))) hW
  have hR3' : (∑ d ∈ S, |r d|) ≤ R3 := hR3
  have hR3nn : (0 : ℝ) ≤ R3 := le_trans hX hR3'
  have hWnn' : (0 : ℝ) ≤ W := le_trans hWnn hW
  have hWnn2 : (0 : ℝ) ≤ ∑ d ∈ S, |r d| * ((d.divisors.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (abs_nonneg _) (by positivity))
  have hsq : (∑ d ∈ S, |r d| * (d.divisors.card : ℝ)) ^ 2 ≤ R3 * W :=
    le_trans hcs (mul_le_mul hR3' hW' hWnn2 hR3nn)
  calc (∑ d ∈ S, (d.divisors.card : ℝ) * |r d|)
      = ∑ d ∈ S, |r d| * (d.divisors.card : ℝ) :=
        Finset.sum_congr rfl (fun d _ => mul_comm _ _)
    _ ≤ Real.sqrt (R3 * W) :=
        (Real.le_sqrt hX' (mul_nonneg hR3nn hWnn')).mpr hsq
    _ = Real.sqrt R3 * Real.sqrt W := Real.sqrt_mul hR3nn W
    _ = Real.sqrt W * Real.sqrt R3 := by ring

/-! ### The τ²-weight for `(R′₃)` -/

/-- The `A`-part of the `τ²`-weight: `∑_{k ≤ Y}τ(k)²A_k(t) ≤ ∑_{n ≤ t}a_nτ(n)³`. -/
lemma sum_tau_sq_Ad_le (t Y : ℕ) :
    (∑ k ∈ Finset.Icc 1 Y, ((k.divisors.card : ℝ)) ^ 2 * Ad FIa k t)
      ≤ ∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ 3 := by
  have h1 : ∀ k : ℕ, Ad FIa k t = ∑ n ∈ (Finset.Icc 1 t).filter (fun n => k ∣ n), FIa n := by
    intro k; rw [Ad, Nat.floor_natCast]
  have hA : (∑ k ∈ Finset.Icc 1 Y, ((k.divisors.card : ℝ)) ^ 2 * Ad FIa k t)
      = ∑ n ∈ Finset.Icc 1 t, FIa n * (∑ k ∈ (Finset.Icc 1 Y).filter (fun k => k ∣ n),
          ((k.divisors.card : ℝ)) ^ 2) := by
    calc (∑ k ∈ Finset.Icc 1 Y, ((k.divisors.card : ℝ)) ^ 2 * Ad FIa k t)
        = ∑ k ∈ Finset.Icc 1 Y, ∑ n ∈ (Finset.Icc 1 t).filter (fun n => k ∣ n),
            ((k.divisors.card : ℝ)) ^ 2 * FIa n := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [h1 k, Finset.mul_sum]
      _ = ∑ k ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 t,
            (if k ∣ n then ((k.divisors.card : ℝ)) ^ 2 * FIa n else 0) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_filter]
      _ = ∑ n ∈ Finset.Icc 1 t, ∑ k ∈ Finset.Icc 1 Y,
            (if k ∣ n then ((k.divisors.card : ℝ)) ^ 2 * FIa n else 0) := Finset.sum_comm
      _ = ∑ n ∈ Finset.Icc 1 t, FIa n * (∑ k ∈ (Finset.Icc 1 Y).filter (fun k => k ∣ n),
            ((k.divisors.card : ℝ)) ^ 2) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          by_cases hkn : k ∣ n
          · simp only [hkn, if_true]; ring
          · simp only [hkn, if_false, mul_zero]
  rw [hA]
  refine Finset.sum_le_sum (fun n hn => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (FIa_nonneg n)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hsub : (Finset.Icc 1 Y).filter (fun k => k ∣ n) ⊆ n.divisors := by
    intro k hk
    rw [Finset.mem_filter] at hk
    exact Nat.mem_divisors.mpr ⟨hk.2, by omega⟩
  have h3 : (∑ k ∈ n.divisors, ((k.divisors.card : ℕ)) ^ 2) ≤ (n.divisors.card) ^ (3 : ℕ) := by
    simpa using sum_divisors_card_pow_le 2 n
  have h2'' : (∑ k ∈ n.divisors, ((k.divisors.card : ℝ)) ^ 2)
      ≤ ((n.divisors.card : ℝ)) ^ (3 : ℕ) := by exact_mod_cast h3
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)) h2''


/-- The `g`-part of the `τ²`-weight: `∑³_{k ≤ Y}τ(k)²g(k) ≪ (log Y)^{32}`. -/
lemma sum_cubefree_tau_sq_FIg_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 2 ≤ Y →
      (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, ((k.divisors.card : ℝ)) ^ 2 * FIg k)
        ≤ C * (Real.log ((Y : ℝ) + 2)) ^ (32 : ℕ) := by
  obtain ⟨C5, hC5, h5⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 5
  refine ⟨C5, hC5, fun Y hY => ?_⟩
  have hpt : ∀ k ∈ (Finset.Icc 1 Y).filter CubefreeN,
      ((k.divisors.card : ℝ)) ^ 2 * FIg k ≤ ((k.divisors.card : ℝ)) ^ 5 / (k : ℝ) := by
    intro k hk
    obtain ⟨hkI, hcf⟩ := Finset.mem_filter.mp hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkI).1
    have hk0 : 0 < k := by omega
    have hkd : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
    have hτ1 : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by
      have : 1 ≤ k.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
      exact_mod_cast this
    have h3 : FIg k ≤ (3 : ℝ) ^ (k.primeFactors.card) / (k : ℝ) :=
      FIg_le_three_pow_omega_div k hk0 hcf
    have h4 : (3 : ℝ) ^ (k.primeFactors.card) ≤ ((k.divisors.card : ℝ)) ^ 3 := by
      have h6 := three_pow_card_primeFactors_le_card_divisors_sq k hk0
      calc (3 : ℝ) ^ (k.primeFactors.card) ≤ ((k.divisors.card : ℝ)) ^ 2 := h6
        _ ≤ ((k.divisors.card : ℝ)) ^ 3 := pow_le_pow_right₀ hτ1 (by norm_num)
    calc ((k.divisors.card : ℝ)) ^ 2 * FIg k
        ≤ ((k.divisors.card : ℝ)) ^ 2 * ((3 : ℝ) ^ (k.primeFactors.card) / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ ((k.divisors.card : ℝ)) ^ 2 * (((k.divisors.card : ℝ)) ^ 3 / (k : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right h4 hkd.le
      _ = ((k.divisors.card : ℝ)) ^ 5 / (k : ℝ) := by ring
  have hstep : (∑ k ∈ (Finset.Icc 1 Y).filter CubefreeN, ((k.divisors.card : ℝ)) ^ 2 * FIg k)
      ≤ ∑ k ∈ Finset.Icc 1 Y, ((k.divisors.card : ℝ)) ^ 5 / (k : ℝ) :=
    le_trans (Finset.sum_le_sum hpt)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k _ _ => by positivity))
  refine le_trans hstep ?_
  have h := h5 Y (by omega)
  simpa using h

set_option maxHeartbeats 2000000 in
/-- **Companion §9, the `E₁` bound**: with `Rcut x·L² ≤ R3cut x`, the `ν ≤ L` part of the §9 error
term is `≪ A(x)(log x)^{−λ}` for every `λ` (the `(R₃)`-exponent is chosen freely). -/
theorem FI_Eone_le (lam : ℝ) :
    ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ t L : ℕ,
      2 ≤ t → t ≤ x → 1 ≤ L →
      Submission.Rcut x * L ^ 2 + 1 ≤ Submission.X2Y4R3.R3cut x →
      Eone FIr t (Submission.Rcut x) L
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
  obtain ⟨C2, B2, X2, hC2, hcube⟩ := sum_FIa_tau_cube_le
  obtain ⟨Cg, hCg, hg⟩ := sum_cubefree_tau_sq_FIg_le
  set W0 : ℝ := max B2 33 + 1 with hW0
  set lamR : ℝ := W0 + 2 * lam + 10 with hlamR
  set CW : ℝ := (2 * C2 + 2 * Cg + 1) with hCW
  have hW0ge : (33 : ℝ) ≤ W0 := by rw [hW0]; have := le_max_right B2 33; linarith
  have hW0B2 : B2 ≤ W0 := by rw [hW0]; have := le_max_left B2 33; linarith
  have hCW0 : (0 : ℝ) < CW := by rw [hCW]; positivity
  obtain ⟨X3, h3⟩ := FIr_cubefree_sum_le_generic lamR
  obtain ⟨Y1, -, hY1⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := (2 : ℝ)) (by norm_num) (n := ⌈(2 : ℝ) ^ 25 + 3⌉₊) (r := (3 : ℝ) / 10) (by norm_num)
  refine ⟨max (max (max ⌈X2⌉₊ X3) Y1) 64, (1 + Real.sqrt (8 * CW)) * 10, by positivity,
    fun x hx t L ht htx hL1 hR3L => ?_⟩
  have hle := hx
  have hX2c : ⌈X2⌉₊ ≤ x :=
    le_trans (le_trans (le_max_left ⌈X2⌉₊ X3) (le_trans (le_max_left _ _) (le_max_left _ _))) hle
  have hxX2 : X2 ≤ (x : ℝ) :=
    le_trans (Nat.le_ceil X2) (by exact_mod_cast hX2c)
  have hxX3 : X3 ≤ x := le_trans (le_trans (le_max_right ⌈X2⌉₊ X3) (le_trans (le_max_left _ _) (le_max_left _ _))) hle
  have hxY1 : Y1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have hx64 : 64 ≤ x := le_trans (le_max_right _ _) hle
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hx1)
  have hRt : 4 ≤ Submission.Rcut x := four_le_Rcut hx64
  have ht1 : 1 ≤ t := le_trans (by norm_num : 1 ≤ 2) ht
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans (by norm_num : 3 ≤ 64) hx64)
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlogx1
  have hAc1 : (1 : ℝ) ≤ Acount FIa (x : ℝ) := by
      have hmem : (1 : ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, hx1⟩
      have h := Finset.single_le_sum (f := FIa) (fun i _ => FIa_nonneg i) hmem
      rw [Acount, Nat.floor_natCast]
      have h2 : (1 : ℝ) ≤ FIa 1 := by
        rw [FIa]
        exact_mod_cast an_one_pos'
      linarith
  have hAseq : (Submission.Aseq x : ℝ) ≤ 2 * Acount FIa (x : ℝ) := by
    have h4 : (Submission.Aseq x : ℝ) = Acount FIa (x : ℝ) + 1 := by rw [FI_Acount_eq]; ring
    linarith [hAc1]
  -- `(R₃)` for the sub-range
  have hR3 : (∑ k ∈ (Finset.Icc 1 (Submission.Rcut x * L ^ 2)).filter CubefreeN, |FIr k t|)
      ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamR) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => abs_nonneg _))
      (h3 x hxX3 t ht htx)
    intro k hk
    obtain ⟨hkI, hcf⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hkI
    have hk3 : k < Submission.X2Y4R3.R3cut x :=
      Nat.lt_of_succ_le (le_trans (Nat.add_le_add_right hk2 1) hR3L)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk3, hcf⟩
  -- `(log x)^{2^25}·x^{7/10} ≤ x`, hence `R3cut x ≤ x`
  have hbig : (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) ≤ (x : ℝ) / 2 := by
    have h8 := hY1 x hxY1
    have h8' : (Real.log ((x : ℝ) + 2)) ^ (⌈(2 : ℝ) ^ 25 + 3⌉₊ : ℕ) ≤ (x : ℝ) ^ ((3 : ℝ) / 10) / 2 := by
      have h := h8
      linarith
    have h9 : (Real.log x) ^ ((2 : ℝ) ^ 25)
        ≤ (Real.log ((x : ℝ) + 2)) ^ (⌈(2 : ℝ) ^ 25 + 3⌉₊ : ℕ) := by
      have h10 : (Real.log x) ^ ((2 : ℝ) ^ 25) ≤ (Real.log ((x : ℝ) + 2)) ^ ((2 : ℝ) ^ 25) :=
        Real.rpow_le_rpow hlogx0.le (Real.log_le_log (by positivity) (by linarith)) (by norm_num)
      have h11 : (Real.log ((x : ℝ) + 2)) ^ ((2 : ℝ) ^ 25)
          ≤ (Real.log ((x : ℝ) + 2)) ^ (⌈(2 : ℝ) ^ 25 + 3⌉₊ : ℕ) := by
        rw [← Real.rpow_natCast (Real.log ((x : ℝ) + 2)) (⌈(2 : ℝ) ^ 25 + 3⌉₊)]
        refine Real.rpow_le_rpow_of_exponent_le ?_ (le_trans (by norm_num : (2 : ℝ) ^ 25 ≤ (2 : ℝ) ^ 25 + 3) (Nat.le_ceil _))
        have h12 : Real.exp 1 ≤ (x : ℝ) + 2 := by
          have h14 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
          linarith [Real.exp_one_lt_three]
        have h13 := Real.log_le_log (Real.exp_pos 1) h12
        rwa [Real.log_exp] at h13
      exact le_trans h10 h11
    calc (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25)
        ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log ((x : ℝ) + 2)) ^ (⌈(2 : ℝ) ^ 25 + 3⌉₊ : ℕ) :=
          mul_le_mul_of_nonneg_left h9 (Real.rpow_nonneg hx0.le _)
      _ ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * ((x : ℝ) ^ ((3 : ℝ) / 10) / 2) :=
          mul_le_mul_of_nonneg_left h8' (Real.rpow_nonneg hx0.le _)
      _ = (x : ℝ) / 2 := by
          rw [mul_div_assoc', ← Real.rpow_add hx0]
          norm_num
  have hRx : Submission.Rcut x ≤ x := by
    rw [Submission.Rcut]
    have h2 : (x : ℝ) ^ ((11 : ℝ) / 16) ≤ (x : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx1) (show (11 : ℝ) / 16 ≤ 1 by norm_num)
    have h1 : ((⌊(x : ℝ) ^ ((11 : ℝ) / 16)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
      le_trans (Nat.floor_le (Real.rpow_nonneg hx0.le _)) h2
    exact_mod_cast h1
  have hYx : Submission.Rcut x * L ^ 2 + 2 ≤ x := by
    have h6 : ((Submission.X2Y4R3.R3cut x : ℕ) : ℝ) ≤ (x : ℝ) / 2 := by
      rw [Submission.X2Y4R3.R3cut]
      exact le_trans (Nat.floor_le (by positivity)) hbig
    have h8 : ((Submission.Rcut x * L ^ 2 + 1 : ℕ) : ℝ) ≤ (x : ℝ) / 2 := by
      have h8b : ((Submission.Rcut x * L ^ 2 + 1 : ℕ) : ℝ)
          ≤ ((Submission.X2Y4R3.R3cut x : ℕ) : ℝ) := by exact_mod_cast hR3L
      linarith [h8b, h6]
    have h9 : (Submission.Rcut x * L ^ 2 + 2 : ℕ) ≤ x := by
      have h10 : ((Submission.Rcut x * L ^ 2 + 2 : ℕ) : ℝ) ≤ (x : ℝ) := by
        push_cast at h8 ⊢
        have hx64R : (64 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx64
        linarith
      exact_mod_cast h10
    exact h9
  -- the τ²-weight
  have hW : (∑ k ∈ (Finset.Icc 1 (Submission.Rcut x * L ^ 2)).filter CubefreeN,
        ((k.divisors.card : ℝ)) ^ 2 * |FIr k t|)
      ≤ CW * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0 := by
    have h1 : (∑ k ∈ (Finset.Icc 1 (Submission.Rcut x * L ^ 2)).filter CubefreeN,
          ((k.divisors.card : ℝ)) ^ 2 * |FIr k t|)
        ≤ ∑ k ∈ (Finset.Icc 1 (Submission.Rcut x * L ^ 2)).filter CubefreeN,
            ((k.divisors.card : ℝ)) ^ 2 * (Ad FIa k t + FIg k * Acount FIa (t : ℝ)) :=
      Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (FIr_abs_le_Ad k t) (by positivity))
    have h2 : (∑ k ∈ (Finset.Icc 1 (Submission.Rcut x * L ^ 2)).filter CubefreeN,
            ((k.divisors.card : ℝ)) ^ 2 * (Ad FIa k t + FIg k * Acount FIa (t : ℝ)))
        = (∑ k ∈ (Finset.Icc 1 (Submission.Rcut x * L ^ 2)).filter CubefreeN,
            ((k.divisors.card : ℝ)) ^ 2 * Ad FIa k t)
          + Acount FIa (t : ℝ) * (∑ k ∈ (Finset.Icc 1 (Submission.Rcut x * L ^ 2)).filter CubefreeN,
            ((k.divisors.card : ℝ)) ^ 2 * FIg k) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have h3a : (∑ k ∈ (Finset.Icc 1 (Submission.Rcut x * L ^ 2)).filter CubefreeN,
          ((k.divisors.card : ℝ)) ^ 2 * Ad FIa k t)
        ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun k _ _ => mul_nonneg (by positivity)
          (Finset.sum_nonneg (fun n _ => FIa_nonneg n)))) ?_
      refine le_trans (sum_tau_sq_Ad_le t (Submission.Rcut x * L ^ 2)) ?_
      refine le_trans (hcube x hxX2 t ht htx) ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hlogx1 hW0B2) (by positivity)
    have h3b : (∑ k ∈ (Finset.Icc 1 (Submission.Rcut x * L ^ 2)).filter CubefreeN,
          ((k.divisors.card : ℝ)) ^ 2 * FIg k)
        ≤ Cg * (Real.log x) ^ W0 := by
      have hY2' : 2 ≤ Submission.Rcut x * L ^ 2 := by
        have h27 : 2 ≤ Submission.Rcut x := by omega
        have hLsq : 1 ≤ L ^ 2 := by nlinarith
        calc 2 ≤ Submission.Rcut x := h27
          _ = Submission.Rcut x * 1 := (Nat.mul_one _).symm
          _ ≤ Submission.Rcut x * L ^ 2 := Nat.mul_le_mul_left _ hLsq
      refine le_trans (hg (Submission.Rcut x * L ^ 2) hY2') ?_
      have h5 : Real.log (((Submission.Rcut x * L ^ 2 : ℕ) : ℝ) + 2) ≤ Real.log x :=
        Real.log_le_log (by positivity) (by exact_mod_cast hYx)
      have hlog22 : (0 : ℝ) ≤ Real.log (((Submission.Rcut x * L ^ 2 : ℕ) : ℝ) + 2) :=
        Real.log_nonneg (by linarith)
      have h7 : (Real.log (((Submission.Rcut x * L ^ 2 : ℕ) : ℝ) + 2)) ^ (32 : ℕ)
          ≤ (Real.log x) ^ (32 : ℕ) := pow_le_pow_left₀ hlog22 h5 32
      have h9 : (Real.log x) ^ (32 : ℕ) ≤ (Real.log x) ^ W0 := by
        rw [← Real.rpow_natCast (Real.log x) 32]
        exact Real.rpow_le_rpow_of_exponent_le hlogx1
          (le_trans (by norm_num : (32 : ℝ) ≤ 33) hW0ge)
      exact mul_le_mul_of_nonneg_left (le_trans h7 h9) hCg.le
    have hAt : Acount FIa (t : ℝ) ≤ (Submission.Aseq x : ℝ) := by
      have h1 : Acount FIa (t : ℝ) ≤ Submission.Aseq t := by
        rw [FI_Acount_eq]; linarith
      exact le_trans h1 (by exact_mod_cast Aseq_mono htx)
    have hAseqx : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
    have hlx : (0 : ℝ) ≤ (Real.log x) ^ W0 := Real.rpow_nonneg hlogx0.le _
    refine le_trans (le_trans h1 (le_of_eq h2)) ?_
    have hSumFIg : (0 : ℝ) ≤ ∑ k ∈ (Finset.Icc 1 (Submission.Rcut x * L ^ 2)).filter CubefreeN,
        ((k.divisors.card : ℝ)) ^ 2 * FIg k :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (by positivity) (FIg_nonneg k))
    refine le_trans (add_le_add h3a (mul_le_mul hAt h3b hSumFIg hAseqx)) ?_
    -- `C2·Aseq·(log)^{W0} + Aseq·(Cg·(log)^{W0}) ≤ CW·Aseq·(log)^{W0}`
    have hsum : C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0
          + (Submission.Aseq x : ℝ) * (Cg * (Real.log x) ^ W0)
        = (C2 + Cg) * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0 := by ring
    rw [hsum]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hAseqx) hlx
    rw [hCW]
    linarith [hCg.le, hC2.le]
  -- assemble `E₁ ≤ √W·√R3`
  have hroot : Real.sqrt (CW * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0)
        * Real.sqrt (4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamR))
      ≤ Real.sqrt (8 * CW) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    have hA0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
    have hlx0 : (0 : ℝ) ≤ Real.log x := hlogx0.le
    generalize hP1 : (Real.log x) ^ W0 = P1
    generalize hP2 : (Real.log x) ^ (-lamR) = P2
    have hP10 : (0 : ℝ) ≤ P1 := by rw [← hP1]; positivity
    have hP20 : (0 : ℝ) ≤ P2 := by rw [← hP2]; positivity
    have hS1nn : (0 : ℝ) ≤ CW * (Submission.Aseq x : ℝ) * P1 := by positivity
    have hS2nn : (0 : ℝ) ≤ 4 * (Submission.Aseq x : ℝ) * P2 := by positivity
    have hleft : (0 : ℝ) ≤ Real.sqrt (CW * (Submission.Aseq x : ℝ) * P1)
        * Real.sqrt (4 * (Submission.Aseq x : ℝ) * P2) := by positivity
    have hright : (0 : ℝ) ≤ Real.sqrt (8 * CW) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
      have h1 : (0 : ℝ) ≤ Real.sqrt (8 * CW) := Real.sqrt_nonneg _
      exact mul_nonneg (mul_nonneg h1 hA0) (Real.rpow_nonneg hlx0 _)
    -- `P1 * P2 = (log x)^{-2λ-10}`
    have hpow : P1 * P2 = (Real.log x) ^ (-2 * lam - 10) := by
      rw [← hP1, ← hP2, ← Real.rpow_add hlogx0]
      congr 1
      rw [hlamR]
      ring
    have hsq : (Real.sqrt (CW * (Submission.Aseq x : ℝ) * P1)
          * Real.sqrt (4 * (Submission.Aseq x : ℝ) * P2)) ^ 2
        ≤ (Real.sqrt (8 * CW) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hS1nn, Real.sq_sqrt hS2nn,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 8 * CW),
        ← Real.rpow_natCast ((Real.log x) ^ (-lam)) 2, ← Real.rpow_mul hlx0]
      have hprod : CW * (Submission.Aseq x : ℝ) * P1 * (4 * (Submission.Aseq x : ℝ) * P2)
          = 4 * CW * ((Submission.Aseq x : ℝ) ^ 2 * (P1 * P2)) := by ring
      rw [hprod, hpow]
      have hfin : 4 * CW * ((Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (-2 * lam - 10))
          ≤ 8 * CW * ((Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (-lam * ((2 : ℕ) : ℝ))) := by
        have h1 : (Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (-2 * lam - 10)
            ≤ (Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (-lam * ((2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hlogx1 (by push_cast; linarith)) (by positivity)
        have h2 : 4 * CW ≤ 8 * CW := by linarith [hCW0]
        refine le_trans (mul_le_mul_of_nonneg_right h2 (by positivity)) ?_
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      calc 4 * CW * ((Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (-2 * lam - 10))
          ≤ 8 * CW * ((Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (-lam * ((2 : ℕ) : ℝ))) := hfin
        _ = 8 * CW * (Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (-lam * ((2 : ℕ) : ℝ)) := by ring
    have h5 := sq_le_sq.mp hsq
    rw [abs_of_nonneg hleft, abs_of_nonneg hright] at h5
    exact h5
  -- the two `(R₃)`-inputs
  have hE1 : Eone FIr t (Submission.Rcut x) L
      ≤ Real.sqrt (CW * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0)
        * Real.sqrt (4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamR)) :=
    E1_le FIr t (Submission.Rcut x) L (Rprime3_le_tau2 (fun k => FIr k t) (Submission.Rcut x * L ^ 2) hW hR3)
  refine le_trans hE1 (le_trans hroot ?_)
  have hA0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ (Real.log x) ^ (-lam) := by positivity
  have hs : (0 : ℝ) ≤ Real.sqrt (8 * CW) := Real.sqrt_nonneg _
  nlinarith [hA0, hl, hs, mul_nonneg hA0 hl, mul_nonneg (mul_nonneg hs hA0) hl]
end

end Submission.ASP
