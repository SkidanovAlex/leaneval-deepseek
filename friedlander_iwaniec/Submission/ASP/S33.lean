/-
  Companion paper, §9: the *(R′)* chain for the sequence `ã` — stage 1.

  This file generalises the two `ν`-range lemmas of `S29` to an *arbitrary* logarithmic
  exponent:

  * `FIr_sq_large_le_B` — the `ν > L` half, with the exponent `B` of the hypothesis
    `x^{1/3}(log x)^B ≤ L` as a *parameter* (the conclusion carries `(log x)^{(71−B)/2}`).
    `FIr_sq_large_le` is the case `B = 75`.
  * `FIr_sq_small_le_generic` — the `ν ≤ L` half at an arbitrary log exponent (from
    `S31.FIr_cubefree_sum_le_generic`, i.e. from `(R₃)`).
-/
import Mathlib
import Submission.ASP.S31
import Submission.ASP.S9i
import Submission.ASP.S9d
import Submission.Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
import Submission.Commons.Analysis.RealPow.rpow_le_rpow_of_one_le_of_exponent_nonpos
import Submission.Commons.NumberTheory.Sieve.sum_squarefree_tau_pow_density_le

set_option maxHeartbeats 3200000

namespace Submission.ASP

open Finset

noncomputable section

/-! ### Two elementary `rpow` splits -/

lemma rpow_third_split {x : ℝ} (hx : 0 < x) :
    x = x ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) := by
  rw [← Real.rpow_add hx, show (2 : ℝ) / 3 + (1 : ℝ) / 3 = (1 : ℝ) from by norm_num,
    Real.rpow_one]

lemma rpow_split_mul {y : ℝ} (hy : 0 < y) (a b : ℝ) : y ^ a = y ^ (a - b) * y ^ b := by
  rw [← Real.rpow_add hy, show a - b + b = a from by ring]


/-! ### The `ν > L` half at an arbitrary logarithmic exponent -/

/-- The `ν > L` part of `∑_{ν ≤ √x}|FIr(ν²)x|`: Cauchy–Schwarz plus `(9.2)` for the `Ad`-part
(which uses `L ≥ x^{1/3}(log x)^B`), and the convergence of `∑_ν g(ν²)` for the `g`-part.
The logarithmic exponent `B` is a parameter; the conclusion carries `(log x)^{(71−B)/2}`. -/
theorem FIr_sq_large_le_B {K B : ℝ} (hK : 0 < K)
    (hTail : ∀ N L : ℕ, 1 ≤ L →
      (∑ ν ∈ (Finset.Icc 1 N).filter (fun n => L < n), abs (FIg (ν ^ 2)))
        ≤ K / Real.sqrt (L : ℝ)) :
    ∃ X₀ : ℕ, ∃ K3 : ℝ, 0 < K3 ∧ ∀ x : ℕ, X₀ ≤ x → ∀ L : ℕ, 1 ≤ L → L ≤ x.sqrt →
      (x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ B ≤ (L : ℝ) →
      (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, abs (FIr (ν ^ 2) x))
        ≤ Acount FIa (x : ℝ) * K3 * (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2)
          + Acount FIa (x : ℝ) * K3 / Real.sqrt (L : ℝ) := by
  obtain ⟨X1a, hS92⟩ := X2Y4_S92
  obtain ⟨C2, hC2pos, hC2⟩ := sum_tau_cube_sqr_dvd_gt_le
  refine ⟨max X1a 4, max (2 * Real.sqrt C2) K + 1, by positivity,
    fun x hx L hL1 hLx hLbig => ?_⟩
  have hx1 : X1a ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
  have hxt : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hsL : (0 : ℝ) < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hL0
  -- `A(x) ≥ 1`
  have hA1 : 1 ≤ Acount FIa (x : ℝ) := by
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, hxt⟩
    have h := Finset.single_le_sum (f := FIa) (fun i _ => FIa_nonneg i) hmem
    rw [Acount, Nat.floor_natCast]
    have h2 : (1 : ℝ) ≤ FIa 1 := by
      rw [FIa]
      exact_mod_cast an_one_pos'
    linarith
  have hA0 : (0 : ℝ) ≤ Acount FIa (x : ℝ) := le_trans zero_le_one hA1
  have hAseq : (Submission.Aseq x : ℝ) ≤ 2 * Acount FIa (x : ℝ) := by
    have h4 : (Submission.Aseq x : ℝ) = Acount FIa (x : ℝ) + 1 := by rw [FI_Acount_eq]; ring
    linarith
  -- log facts
  have hlog2 : (1 : ℝ) ≤ Real.log ((x : ℝ) + 2) := by
    have h5 : (5 : ℝ) ≤ (x : ℝ) + 2 := by
      have h6 : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx4
      linarith
    have he : Real.exp 1 ≤ 5 := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans he h5)
    rwa [Real.log_exp] at h
  have hlogpos : (0 : ℝ) < Real.log ((x : ℝ) + 2) := lt_of_lt_of_le one_pos hlog2
  -- the pointwise splitting
  have hsplit : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, abs (FIr (ν ^ 2) x))
      ≤ (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, Ad FIa (ν ^ 2) x)
        + Acount FIa (x : ℝ)
            * (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, FIg (ν ^ 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun ν _ => ?_)
    have h1 : 0 ≤ Ad FIa (ν ^ 2) x := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
    have h2 : 0 ≤ FIg (ν ^ 2) := FIg_nonneg _
    have h4 : 0 ≤ FIg (ν ^ 2) * Acount FIa (x : ℝ) := mul_nonneg h2 hA0
    have heq : FIr (ν ^ 2) x = Ad FIa (ν ^ 2) x - FIg (ν ^ 2) * Acount FIa (x : ℝ) := rfl
    rw [heq]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  -- `(9.2)`: the square sum
  have hA2 : (∑ n ∈ Finset.Icc 1 x, FIa n ^ 2)
      ≤ 4 * (x : ℝ) ^ (-(2 : ℝ) / 3) * Acount FIa (x : ℝ) ^ 2 := by
    have h1 : (∑ n ∈ Finset.Icc 1 x, FIa n ^ 2) ≤ ∑ n ∈ Finset.range (x + 1), FIa n ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (by
        intro n hn
        rw [Finset.mem_Icc] at hn
        exact Finset.mem_range.mpr (by omega)) (fun n _ _ => by positivity)
    have h2 : (∑ n ∈ Finset.range (x + 1), FIa n ^ 2)
        ≤ (x : ℝ) ^ (-(2 : ℝ) / 3) * (Submission.Aseq x : ℝ) ^ 2 := by
      simpa only [FIa] using hS92 x hx1
    have h5 : (Submission.Aseq x : ℝ) ^ 2 ≤ 4 * Acount FIa (x : ℝ) ^ 2 := by
      have h4 : (Submission.Aseq x : ℝ) = Acount FIa (x : ℝ) + 1 := by rw [FI_Acount_eq]; ring
      rw [h4]; nlinarith [hA0, hA1]
    have hstep : (∑ n ∈ Finset.range (x + 1), FIa n ^ 2)
        ≤ 4 * (x : ℝ) ^ (-(2 : ℝ) / 3) * Acount FIa (x : ℝ) ^ 2 := by
      calc (∑ n ∈ Finset.range (x + 1), FIa n ^ 2)
          ≤ (x : ℝ) ^ (-(2 : ℝ) / 3) * (Submission.Aseq x : ℝ) ^ 2 := h2
        _ ≤ (x : ℝ) ^ (-(2 : ℝ) / 3) * (4 * Acount FIa (x : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hx0.le _)
        _ = 4 * (x : ℝ) ^ (-(2 : ℝ) / 3) * Acount FIa (x : ℝ) ^ 2 := by ring
    exact le_trans h1 hstep
  -- the `Ad`-part, via `EtwoA_gt_le`
  have hAd : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, Ad FIa (ν ^ 2) x)
      ≤ 2 * (x : ℝ) ^ (-(1 : ℝ) / 3) * Acount FIa (x : ℝ)
          * Real.sqrt (C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (L : ℝ)) := by
    have hEtwo : EtwoA FIa x 1 (L + 1) x
        ≤ Real.sqrt (∑ n ∈ Finset.Icc 1 x, FIa n ^ 2)
          * Real.sqrt (C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (L : ℝ)) := by
      refine EtwoA_gt_le FIa (fun n => FIa_nonneg n) x 1 L hxt ?_
      refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) (hC2 x L hL1 hxt)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hsub : sqdvCount n (L + 1) x
          ≤ ((Finset.Icc 1 x).filter (fun ν => L < ν ∧ ν ^ 2 ∣ n)).card := by
        rw [sqdvCount]
        refine Finset.card_le_card ?_
        intro ν hν
        rw [Finset.mem_filter] at hν
        obtain ⟨hν1, hν2⟩ := hν
        rw [Finset.mem_filter] at hν1
        obtain ⟨hν1a, _⟩ := hν1
        rw [Finset.mem_Icc] at hν1a
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hν1a.2⟩, by omega, hν2⟩
      exact_mod_cast hsub
    have hstep : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, Ad FIa (ν ^ 2) x)
        ≤ EtwoA FIa x 1 (L + 1) x := by
      rw [EtwoA_one_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg (by
        intro ν hν
        rw [Finset.mem_filter] at hν
        obtain ⟨hν1, hν2⟩ := hν
        rw [Finset.mem_Icc] at hν1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,
          le_trans hν1.2 (Nat.sqrt_le_self x)⟩, hν2⟩)
        (fun ν _ _ => Finset.sum_nonneg (fun n _ => FIa_nonneg n))
    refine le_trans hstep (le_trans hEtwo ?_)
    have hsA : Real.sqrt (∑ n ∈ Finset.Icc 1 x, FIa n ^ 2)
        ≤ 2 * (x : ℝ) ^ (-(1 : ℝ) / 3) * Acount FIa (x : ℝ) := by
      refine le_trans (Real.sqrt_le_sqrt hA2) ?_
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      have h2 : (2 * (x : ℝ) ^ (-(1 : ℝ) / 3) * Acount FIa (x : ℝ)) ^ 2
          = 4 * (x : ℝ) ^ (-(2 : ℝ) / 3) * Acount FIa (x : ℝ) ^ 2 := by
        rw [mul_pow, mul_pow, ← Real.rpow_natCast ((x : ℝ) ^ (-(1:ℝ)/3)) 2,
          ← Real.rpow_mul hx0.le]
        norm_num
      rw [h2]
    exact mul_le_mul_of_nonneg_right hsA (Real.sqrt_nonneg _)
  -- the `g`-part
  have hg : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, FIg (ν ^ 2))
      ≤ K / Real.sqrt (L : ℝ) := by
    have heq : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, FIg (ν ^ 2))
        = ∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, abs (FIg (ν ^ 2)) := by
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      exact (abs_of_nonneg (FIg_nonneg _)).symm
    rw [heq]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ν _ _ => abs_nonneg _))
      (hTail x L hL1)
    intro ν hν
    rw [Finset.mem_filter] at hν
    obtain ⟨hν1, hν2⟩ := hν
    rw [Finset.mem_Icc] at hν1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,
      le_trans hν1.2 (Nat.sqrt_le_self x)⟩, by omega⟩
  -- the numerical comparison
  have hLg0 : (0 : ℝ) ≤ (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2) :=
    Real.rpow_nonneg hlogpos.le _
  have hsqrt_bound :
      Real.sqrt (C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (L : ℝ))
        ≤ Real.sqrt C2 * (x : ℝ) ^ ((1 : ℝ) / 3)
            * (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2) := by
    have hmid : C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (L : ℝ)
        ≤ C2 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (71 - B) := by
      have h1 : C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (L : ℝ)
          ≤ C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71
            / ((x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ B) :=
        div_le_div_of_nonneg_left (b := (L : ℝ))
          (c := (x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ B)
          (by positivity) (by positivity) hLbig
      refine le_trans h1 (le_of_eq ?_)
      have hxd : (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 3) = (x : ℝ) ^ ((2 : ℝ) / 3) := by
        rw [div_eq_iff (by positivity : (x : ℝ) ^ ((1 : ℝ) / 3) ≠ 0)]
        exact rpow_third_split hx0
      rw [← Real.rpow_natCast (Real.log ((x : ℝ) + 2)) 71,
        ← div_mul_div_comm (C2 * (x : ℝ)) ((x : ℝ) ^ ((1 : ℝ) / 3))
          ((Real.log ((x : ℝ) + 2)) ^ ((71 : ℕ) : ℝ)) ((Real.log ((x : ℝ) + 2)) ^ B),
        ← Real.rpow_sub hlogpos ((71 : ℕ) : ℝ) B,
        show ((71 : ℕ) : ℝ) - B = (71 : ℝ) - B from by norm_num,
        mul_div_assoc, hxd]
    have hmid2 : Real.sqrt (C2 * (x : ℝ) ^ ((2 : ℝ) / 3)
          * (Real.log ((x : ℝ) + 2)) ^ (71 - B))
        = Real.sqrt C2 * (x : ℝ) ^ ((1 : ℝ) / 3)
            * (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2) := by
      rw [show C2 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (71 - B)
          = C2 * ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 2
            * ((Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2)) ^ 2 from by
        rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hx0.le,
          ← Real.rpow_natCast ((Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2)) 2,
          ← Real.rpow_mul hlogpos.le,
          show (1 : ℝ) / 3 * ((2 : ℕ) : ℝ) = (2 : ℝ) / 3 from by norm_num,
          show (71 - B) / 2 * ((2 : ℕ) : ℝ) = 71 - B from by ring]]
      rw [show C2 * ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 2
            * ((Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2)) ^ 2
          = C2 * (((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 2
            * ((Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2)) ^ 2) from by ring]
      rw [Real.sqrt_mul hC2pos.le,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 2),
        Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
      ring
    exact le_trans (Real.sqrt_le_sqrt hmid) (le_of_eq hmid2)
  have hAd' : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, Ad FIa (ν ^ 2) x)
      ≤ Acount FIa (x : ℝ) * (2 * Real.sqrt C2)
          * (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2) := by
    refine le_trans hAd (le_trans (mul_le_mul_of_nonneg_left hsqrt_bound (by positivity)) ?_)
    have h2 : (x : ℝ) ^ (-(1:ℝ)/3) * (x : ℝ) ^ ((1:ℝ)/3) = 1 := by
      rw [← Real.rpow_add hx0]; norm_num
    have h3 : 2 * (x : ℝ) ^ (-(1:ℝ)/3) * Acount FIa (x : ℝ)
          * (Real.sqrt C2 * (x : ℝ) ^ ((1:ℝ)/3)
            * (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2))
        = Acount FIa (x : ℝ) * (2 * Real.sqrt C2)
          * (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2) := by
      rw [show 2 * (x : ℝ) ^ (-(1:ℝ)/3) * Acount FIa (x : ℝ)
            * (Real.sqrt C2 * (x : ℝ) ^ ((1:ℝ)/3)
              * (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2))
          = 2 * Real.sqrt C2 * Acount FIa (x : ℝ)
            * ((x : ℝ) ^ (-(1:ℝ)/3) * (x : ℝ) ^ ((1:ℝ)/3))
            * (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2) from by ring, h2]
      ring
    rw [h3]
  have hK3 : 2 * Real.sqrt C2 ≤ max (2 * Real.sqrt C2) K + 1 := by
    linarith [le_max_left (2 * Real.sqrt C2) K]
  have hK3' : K ≤ max (2 * Real.sqrt C2) K + 1 := by
    linarith [le_max_right (2 * Real.sqrt C2) K]
  refine le_trans hsplit (le_trans (add_le_add hAd' (mul_le_mul_of_nonneg_left hg hA0)) ?_)
  have h1 : Acount FIa (x : ℝ) * (2 * Real.sqrt C2)
        * (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2)
      ≤ Acount FIa (x : ℝ) * (max (2 * Real.sqrt C2) K + 1)
        * (Real.log ((x : ℝ) + 2)) ^ ((71 - B) / 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hLg0
    exact mul_le_mul_of_nonneg_left hK3 hA0
  have h2 : Acount FIa (x : ℝ) * (K / Real.sqrt (L : ℝ))
      ≤ Acount FIa (x : ℝ) * (max (2 * Real.sqrt C2) K + 1) / Real.sqrt (L : ℝ) := by
    calc Acount FIa (x : ℝ) * (K / Real.sqrt (L : ℝ))
        = Acount FIa (x : ℝ) * K / Real.sqrt (L : ℝ) := by ring
      _ ≤ Acount FIa (x : ℝ) * (max (2 * Real.sqrt C2) K + 1) / Real.sqrt (L : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hsL.le
          exact mul_le_mul_of_nonneg_left hK3' hA0
  exact add_le_add h1 h2

/-! ### The `ν ≤ L` half at an arbitrary logarithmic exponent -/

/-- The contribution of the squarefree `ν ≤ L` to `∑_{ν ≤ √x}|FIr(ν²)x|`: map `ν ↦ ν²` (injective,
into the cubefree moduli) and apply `(R₃)` at the exponent `lamm`. -/
theorem FIr_sq_small_le_generic (lamm : ℝ) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ L : ℕ, 1 ≤ L →
      L ^ 2 < Submission.X2Y4R3.R3cut x →
      (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree, |FIr (ν ^ 2) x|)
        ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
  obtain ⟨X1, h1⟩ := FIr_cubefree_sum_le_generic lamm
  refine ⟨max X1 2, fun x hx L hL1 hL2 => ?_⟩
  have hx1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  set S : Finset ℕ := (Finset.Icc 1 L).filter Squarefree with hS
  have hinj : ∀ a ∈ S, ∀ b ∈ S, a ^ 2 = b ^ 2 → a = b :=
    fun a _ b _ hab => Nat.pow_left_injective (n := 2) (by norm_num) hab
  have hsub : S.image (fun ν => ν ^ 2)
      ⊆ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨ν, hνS, rfl⟩ := hk
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hνS
    obtain ⟨⟨hν1, hνL⟩, hνsf⟩ := hνS
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · exact lt_of_le_of_lt (Nat.pow_le_pow_left hνL 2) hL2
    · rw [← Nat.lcm_one_right (ν ^ 2)]
      exact cubefreeN_lcm_sq hνsf squarefree_one
  have heq := (Finset.sum_image (s := S) (f := fun k : ℕ => abs (FIr k x))
    (g := fun ν : ℕ => ν ^ 2) hinj).symm
  rw [heq]
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg _))
    (h1 x hx1 x hx2 le_rfl)

/-! ### The signed `ν`-sum `∑_{ν ≤ t} μ(ν)·FIr(ν²)t` -/

/-- The symmetric splitting of an `Icc`-sum. -/
lemma sum_Icc_split' {m k n : ℕ} (hmk : m ≤ k) (hkn : k ≤ n) (f : ℕ → ℝ) :
    (∑ ν ∈ Finset.Icc m n, f ν)
      = (∑ ν ∈ Finset.Icc m k, f ν) + (∑ ν ∈ Finset.Icc (k + 1) n, f ν) := by
  have h1 : (Finset.Icc m n).filter (fun ν => ν ≤ k) = Finset.Icc m k := by
    ext ν
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 hkn⟩, h3⟩
  have h2 : (Finset.Icc m n).filter (fun ν => ¬ ν ≤ k) = Finset.Icc (k + 1) n := by
    ext ν
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, by omega⟩
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc m n) (fun ν => ν ≤ k), h1, h2]

/-- `Acount FIa` is monotone. -/
lemma Acount_FIa_mono {m n : ℕ} (h : m ≤ n) :
    Acount FIa (m : ℝ) ≤ Acount FIa (n : ℝ) := by
  rw [Acount, Acount, Nat.floor_natCast, Nat.floor_natCast]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
    (fun i _ _ => FIa_nonneg i)

/-- `4 ≤ ⌊x^{11/16}⌋₊ = Rcut x` for `x ≥ 64`. -/
lemma four_le_Rcut {x : ℕ} (hx : 64 ≤ x) : 4 ≤ Submission.Rcut x := by
  rw [Submission.Rcut]
  refine Nat.le_floor ?_
  have hx' : (64 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h1 : (64 : ℝ) ^ ((11 : ℝ) / 16) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) :=
    Real.rpow_le_rpow (by norm_num) hx' (by norm_num)
  refine le_trans ?_ h1
  have h2 : (64 : ℝ) ^ ((11 : ℝ) / 16) = (2 : ℝ) ^ ((33 : ℝ) / 8) := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 6,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [h2]
  have h3 : (2 : ℝ) ^ (4 : ℕ) ≤ (2 : ℝ) ^ ((33 : ℝ) / 8) := by
    rw [← Real.rpow_natCast (2 : ℝ) 4]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (4 : ℕ) := by norm_num
  linarith

/-- `x^{11/16}/2 ≤ Rcut x` for `x ≥ 64`. -/
lemma half_rpow_le_Rcut {x : ℕ} (hx : 64 ≤ x) :
    (x : ℝ) ^ ((11 : ℝ) / 16) / 2 ≤ (Submission.Rcut x : ℝ) := by
  have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have h2 : (2 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) := by
    have h1 : (64 : ℝ) ^ ((11 : ℝ) / 16) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx) (by norm_num)
    have h3 : (2 : ℝ) ≤ (64 : ℝ) ^ ((11 : ℝ) / 16) := by
      have : (64 : ℝ) ^ ((11 : ℝ) / 16) = (2 : ℝ) ^ ((33 : ℝ) / 8) := by
        rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 6,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [this]
      have h4 : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ ((33 : ℝ) / 8) := by
        rw [← Real.rpow_natCast (2 : ℝ) 1]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      simpa using h4
    linarith
  have h3 : (x : ℝ) ^ ((11 : ℝ) / 16) - 1 ≤ (Submission.Rcut x : ℝ) := by
    rw [Submission.Rcut]
    have h := Nat.lt_floor_add_one ((x : ℝ) ^ ((11 : ℝ) / 16))
    linarith
  linarith

/-- The `ν ≤ L` half at an arbitrary log exponent, with separate outer parameter `x ≥ t`. -/
theorem FIr_sq_small_le_generic' (lamm : ℝ) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x → ∀ L : ℕ, 1 ≤ L →
      L ^ 2 < Submission.X2Y4R3.R3cut x →
      (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree, |FIr (ν ^ 2) t|)
        ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
  obtain ⟨X1, h1⟩ := FIr_cubefree_sum_le_generic lamm
  refine ⟨max X1 2, fun x hx t ht2 htx L hL1 hL2 => ?_⟩
  have hx1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  set S : Finset ℕ := (Finset.Icc 1 L).filter Squarefree with hS
  have hinj : ∀ a ∈ S, ∀ b ∈ S, a ^ 2 = b ^ 2 → a = b :=
    fun a _ b _ hab => Nat.pow_left_injective (n := 2) (by norm_num) hab
  have hsub : S.image (fun ν => ν ^ 2)
      ⊆ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨ν, hνS, rfl⟩ := hk
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hνS
    obtain ⟨⟨hν1, hνL⟩, hνsf⟩ := hνS
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · exact lt_of_le_of_lt (Nat.pow_le_pow_left hνL 2) hL2
    · rw [← Nat.lcm_one_right (ν ^ 2)]
      exact cubefreeN_lcm_sq hνsf squarefree_one
  have heq := (Finset.sum_image (s := S) (f := fun k : ℕ => abs (FIr k t))
    (g := fun ν : ℕ => ν ^ 2) hinj).symm
  rw [heq]
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg _))
    (h1 x hx1 t ht2 htx)

/-- The `ν > L` half at an arbitrary exponent, wrapper of `FIr_sq_large_le_B` with the
summand parameter `t` separated from the outer parameter `x`. -/
theorem FIr_sq_large_le_B2 {K B : ℝ} (hK : 0 < K)
    (hTail : ∀ N L : ℕ, 1 ≤ L →
      (∑ ν ∈ (Finset.Icc 1 N).filter (fun n => L < n), abs (FIg (ν ^ 2)))
        ≤ K / Real.sqrt (L : ℝ)) :
    ∃ X₀ : ℕ, ∃ K3 : ℝ, 0 < K3 ∧ ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, X₀ ≤ t → t ≤ x →
      ∀ L : ℕ, 1 ≤ L → L ≤ t.sqrt →
      (t : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((t : ℝ) + 2)) ^ B ≤ (L : ℝ) →
      (∑ ν ∈ (Finset.Icc (L + 1) t.sqrt).filter Squarefree, abs (FIr (ν ^ 2) t))
        ≤ Acount FIa (t : ℝ) * K3 * (Real.log ((t : ℝ) + 2)) ^ ((71 - B) / 2)
          + Acount FIa (t : ℝ) * K3 / Real.sqrt (L : ℝ) := by
  obtain ⟨X₀, K3, hK3, h⟩ := FIr_sq_large_le_B (K := K) (B := B) hK hTail
  exact ⟨X₀, K3, hK3, fun x hx t ht htx L hL1 hLt hLbig => h t ht L hL1 hLt hLbig⟩

/-! ### Elementary `rpow` identities -/

lemma rpow_sq_div_three (u : ℝ) (hu : 0 ≤ u) : (u ^ ((1 : ℝ) / 3)) ^ 2 = u ^ ((2 : ℝ) / 3) := by
  rw [← Real.rpow_natCast (u ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hu]
  congr 1
  norm_num

lemma rpow_sq' (y : ℝ) (b : ℝ) (hy : 0 ≤ y) : (y ^ b) ^ 2 = y ^ (2 * b) := by
  rw [← Real.rpow_natCast (y ^ b) 2, ← Real.rpow_mul hy]
  congr 1
  ring

lemma sqrt_rpow_mul (u y : ℝ) (b : ℝ) (hu : 0 ≤ u) (hy : 0 ≤ y) :
    Real.sqrt (u ^ ((1 : ℝ) / 3) * y ^ b) = u ^ ((1 : ℝ) / 6) * y ^ (b / 2) := by
  rw [Real.sqrt_eq_rpow, Real.mul_rpow (Real.rpow_nonneg hu _) (Real.rpow_nonneg hy _),
    ← Real.rpow_mul hu, ← Real.rpow_mul hy]
  congr 1
  · rw [show ((1 : ℝ) / 3) * ((1 : ℝ) / 2) = (1 : ℝ) / 6 from by norm_num]
  · ring_nf

lemma sqrt_sqrt_div_two (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (Real.sqrt t / 2) = t ^ ((1 : ℝ) / 4) / Real.sqrt 2 := by
  rw [Real.sqrt_div' (Real.sqrt t) (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow,
    Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
  rw [show ((1 : ℝ) / 2) * ((1 : ℝ) / 2) = (1 : ℝ) / 4 from by norm_num]

lemma div_two_rpow (a : ℝ) (ha : 0 < a) (e : ℝ) : (a / 2) ^ e = (2 : ℝ) ^ (-e) * a ^ e := by
  rw [Real.div_rpow ha.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- `2 ≤ x^{7/10}` for `x ≥ 64`. -/
lemma two_le_rpow_seven_tenths {x : ℕ} (hx : 64 ≤ x) : (2 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
  have h1 : (64 : ℝ) ^ ((7 : ℝ) / 10) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx) (by norm_num)
  have h2 : (2 : ℝ) ≤ (64 : ℝ) ^ ((7 : ℝ) / 10) := by
    have h64 : (64 : ℝ) ^ ((7 : ℝ) / 10) = (2 : ℝ) ^ ((21 : ℝ) / 5) := by
      rw [show (64 : ℝ) = (2 : ℝ) ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 6,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [h64]
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (1 : ℝ) ≤ (21 : ℝ) / 5 by norm_num)
    rwa [Real.rpow_one] at h
  linarith

/-- **The signed `ν`-sum of `FIr` at the squares**: for `t` above the modulus cut-off `Rcut x`,
`|∑_{ν ≤ t} μ(ν)·FIr(ν²)t| ≪ A(x)(log x)^{−λ}` for an arbitrary `λ`. -/
theorem FIr_T_le (lamm : ℝ) (hlamm : 0 ≤ lamm) :
    ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ,
      Submission.Rcut x ≤ t → t ≤ x →
      |∑ ν ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius ν : ℝ) * FIr (ν ^ 2) t|
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
  obtain ⟨X1, hsmall⟩ := FIr_sq_small_le_generic' (lamm + 2)
  obtain ⟨K, hKpos, hTail⟩ := FI_sq_rates.2
  obtain ⟨X2, K3, hK3pos, hlarge⟩ :=
    FIr_sq_large_le_B2 (K := K) (B := 2 * lamm + 100) hKpos hTail
  obtain ⟨CA, hCA, hAup⟩ := Submission.X2Y4R.Aseq_le_const_mul_rpow
  obtain ⟨cA, hcA, X3, hAlow⟩ := Submission.X2Y4R.exists_const_mul_rpow_le_Aseq
  obtain ⟨Y1, -, hY1⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 8) (by norm_num) (n := ⌈2 * (2 * lamm + 100)⌉₊) (r := (1 : ℝ) / 30) (by norm_num)
  obtain ⟨Y2, -, hY2⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 2 * (X2 : ℝ)) (by positivity) (n := 0) (r := (11 : ℝ) / 16) (by norm_num)
  obtain ⟨Y3, -, hY3⟩ := Submission.X2Y4R3.poly_tail_gen
    (CA * K * Real.sqrt 2) ((1 : ℝ) / 2) 0 cA lamm (by positivity) (by norm_num) hcA
  refine ⟨max (max (max X1 X2) (max X3 (max Y1 (max Y2 Y3)))) 64 + 1,
    5 + (CA * K3 / cA) * ((2 : ℝ) ^ (lamm + 14.5) + (2 : ℝ) ^ ((1 : ℝ) / 6)),
    by positivity, fun x hx t hDt htx => ?_⟩
  have hxX1 : X1 ≤ x := by omega
  have hxX2 : X2 ≤ x := by omega
  have hxX3 : X3 ≤ x := by omega
  have hxY1 : Y1 ≤ x := by omega
  have hxY2 : Y2 ≤ x := by omega
  have hxY3 : Y3 ≤ x := by omega
  have hx64 : 64 ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 3 ≤ x from by omega)
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have ht4 : 4 ≤ t := le_trans (four_le_Rcut hx64) hDt
  have ht1 : 1 ≤ t := by omega
  have htRpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have htle : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
  have hts1 : 1 ≤ t.sqrt := by rw [Nat.le_sqrt]; omega
  have htst : t.sqrt ≤ t := Nat.sqrt_le_self t
  -- logarithms
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have he : Real.exp 1 ≤ (x : ℝ) := by
      linarith [Real.exp_one_lt_three, hx3R]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlogpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hlogadd1 : (1 : ℝ) ≤ Real.log ((x : ℝ) + 2) := by
    have h5 : Real.exp 1 ≤ (x : ℝ) + 2 := by linarith [Real.exp_one_lt_three, hx3R]
    have h := Real.log_le_log (Real.exp_pos 1) h5
    rwa [Real.log_exp] at h
  have hlogaddpos : (0 : ℝ) < Real.log ((x : ℝ) + 2) := lt_of_lt_of_le zero_lt_one hlogadd1
  have hlog4 : (4 : ℝ) ≤ Real.log x := by
    have h1 : Real.exp 4 = ((Real.exp 1) ^ 2) ^ 2 := by
      rw [show (4 : ℝ) = (1 + 1) + (1 + 1) from by norm_num, Real.exp_add, Real.exp_add]
      ring
    have h2 : Real.exp 4 < 64 := by
      rw [h1]
      have h3 : (Real.exp 1) ^ 2 < (2.7182818286 : ℝ) ^ 2 := by
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
      nlinarith [h3, Real.exp_pos 1]
    have he : Real.exp 4 ≤ (x : ℝ) := by
      have hx64' : (64 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx64
      linarith
    have h := Real.log_le_log (Real.exp_pos 4) he
    rwa [Real.log_exp] at h
  have hlogt : Real.log x / 2 ≤ Real.log ((t : ℝ) + 2) := by
    have ht_ge : (x : ℝ) ^ ((11 : ℝ) / 16) / 2 ≤ (t : ℝ) :=
      le_trans (half_rpow_le_Rcut hx64) (by exact_mod_cast hDt)
    have h1 : Real.log ((x : ℝ) ^ ((11 : ℝ) / 16) / 2) ≤ Real.log ((t : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hx0] at h1
    have h2 : Real.log 2 ≤ (3 / 16 : ℝ) * Real.log x := by
      have h3 := Real.log_two_lt_d9
      nlinarith [hlog4]
    linarith
  have hlogtpos : (0 : ℝ) < Real.log ((t : ℝ) + 2) := by linarith [hlogt, hlog4]
  have hAc0 : (0 : ℝ) ≤ Acount FIa (t : ℝ) := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
  -- the split point `L` (built from `x^{1/3}` and `log (x+2)`)
  set v : ℝ := (x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (2 * lamm + 100) with hvdef
  set L : ℕ := ⌈v⌉₊ with hLdef
  have hv0 : 0 ≤ v := mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hlogaddpos.le _)
  have hLpos : 0 < L := by
    rw [hLdef]
    exact Nat.ceil_pos.mpr (mul_pos (Real.rpow_pos_of_pos hx0 _)
      (Real.rpow_pos_of_pos hlogaddpos _))
  have hL1 : 1 ≤ L := hLpos
  have hLlow : v ≤ (L : ℝ) := Nat.le_ceil _
  have hLup : (L : ℝ) < v + 1 := Nat.ceil_lt_add_one hv0
  have hv2 : v ^ 2 ≤ (x : ℝ) ^ ((7 : ℝ) / 10) / 8 := by
    have h1 : v ^ 2 = (x : ℝ) ^ ((2 : ℝ) / 3)
        * (Real.log ((x : ℝ) + 2)) ^ (2 * (2 * lamm + 100)) := by
      rw [hvdef, mul_pow, rpow_sq_div_three _ hx0.le, rpow_sq' _ _ hlogaddpos.le]
    rw [h1]
    have hY := hY1 x hxY1
    have hle1 : Real.log ((x : ℝ) + 2) ^ (2 * (2 * lamm + 100))
        ≤ Real.log ((x : ℝ) + 2) ^ ((⌈2 * (2 * lamm + 100)⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlogadd1 (Nat.le_ceil _)
    rw [Real.rpow_natCast] at hle1
    have h4 : Real.log ((x : ℝ) + 2) ^ (2 * (2 * lamm + 100)) ≤ (x : ℝ) ^ ((1 : ℝ) / 30) / 8 := by
      linarith
    calc (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log ((x : ℝ) + 2) ^ (2 * (2 * lamm + 100))
        ≤ (x : ℝ) ^ ((2 : ℝ) / 3) * ((x : ℝ) ^ ((1 : ℝ) / 30) / 8) :=
          mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hx0.le _)
      _ = (x : ℝ) ^ ((7 : ℝ) / 10) / 8 := by
          rw [mul_div_assoc', ← Real.rpow_add hx0]
          norm_num
  have hL2 : ((L : ℝ)) ^ 2 ≤ 2 * v ^ 2 + 2 := by
    nlinarith [hLup, hv0, sq_nonneg (v - 1), (by positivity : (0 : ℝ) ≤ (L : ℝ))]
  have hLsq_lt : L ^ 2 < Submission.X2Y4R3.R3cut x := by
    rw [Submission.X2Y4R3.R3cut]
    refine lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_floor ?_)
    have hx710nn : (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := Real.rpow_nonneg hx0.le _
    have hx710_2 : (2 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := two_le_rpow_seven_tenths hx64
    have hlogpow2 : (2 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) := by
      have h := Real.rpow_le_rpow_of_exponent_le hlog1 (show (1 : ℝ) ≤ (2 : ℝ) ^ 25 by norm_num)
      rw [Real.rpow_one] at h
      linarith
    push_cast
    calc ((L : ℝ)) ^ 2 + 1 ≤ 2 * v ^ 2 + 3 := by linarith
      _ ≤ 2 * ((x : ℝ) ^ ((7 : ℝ) / 10) / 8) + 3 := by linarith [hv2]
      _ = (x : ℝ) ^ ((7 : ℝ) / 10) / 4 + 3 := by ring
      _ ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * 2 := by linarith [hx710_2]
      _ ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) :=
          mul_le_mul_of_nonneg_left hlogpow2 hx710nn
  have hX2t : X2 ≤ t := by
    have hY := hY2 x hxY2
    simp only [pow_zero, mul_one] at hY
    have h2 : (x : ℝ) ^ ((11 : ℝ) / 16) / 2 ≤ (t : ℝ) :=
      le_trans (half_rpow_le_Rcut hx64) (by exact_mod_cast hDt)
    have h3 : (X2 : ℝ) ≤ (t : ℝ) := by linarith
    exact_mod_cast h3
  -- ### the sum splitting
  set g : ℕ → ℝ := fun ν => (ArithmeticFunction.moebius ν : ℝ) * FIr (ν ^ 2) t with hgdef
  have hsplit : (∑ ν ∈ Finset.Icc 1 t, g ν)
      = (∑ ν ∈ Finset.Icc 1 t.sqrt, g ν) + (∑ ν ∈ Finset.Icc (t.sqrt + 1) t, g ν) :=
    sum_Icc_split' hts1 htst g
  -- ### the tail part (ν > √t)
  have htail_eq : (∑ ν ∈ Finset.Icc (t.sqrt + 1) t, g ν)
      = -(Acount FIa (t : ℝ)
          * ∑ ν ∈ Finset.Icc (t.sqrt + 1) t,
              (ArithmeticFunction.moebius ν : ℝ) * FIg (ν ^ 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun ν hν => ?_)
    have hνmem : t.sqrt + 1 ≤ ν := (Finset.mem_Icc.mp hν).1
    have hlt : t < ν ^ 2 := by
      calc t < t.sqrt.succ * t.sqrt.succ := Nat.lt_succ_sqrt t
        _ = (t.sqrt + 1) ^ 2 := by rw [Nat.succ_eq_add_one]; ring
        _ ≤ ν ^ 2 := Nat.pow_le_pow_left hνmem 2
    have hAd : Ad FIa (ν ^ 2) t = 0 := Ad_eq_zero_of_lt_s29 FIa hlt
    simp only [hgdef]
    rw [FIr, hAd]
    ring
  have hfilt : Finset.Icc (t.sqrt + 1) t = (Finset.Icc 1 t).filter (fun n => t.sqrt < n) := by
    ext ν
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h2⟩
  have htail_le : |(∑ ν ∈ Finset.Icc (t.sqrt + 1) t, g ν)|
      ≤ Acount FIa (t : ℝ) * (K / Real.sqrt ((t.sqrt : ℕ) : ℝ)) := by
    rw [htail_eq, abs_neg, abs_mul]
    have hA0 : 0 ≤ Acount FIa (t : ℝ) := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
    rw [abs_of_nonneg hA0]
    refine mul_le_mul_of_nonneg_left ?_ hA0
    calc |∑ ν ∈ Finset.Icc (t.sqrt + 1) t, (ArithmeticFunction.moebius ν : ℝ) * FIg (ν ^ 2)|
        ≤ ∑ ν ∈ Finset.Icc (t.sqrt + 1) t,
            |(ArithmeticFunction.moebius ν : ℝ) * FIg (ν ^ 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ν ∈ Finset.Icc (t.sqrt + 1) t, |FIg (ν ^ 2)| := by
          refine Finset.sum_le_sum (fun ν _ => ?_)
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one ν)
      _ ≤ K / Real.sqrt ((t.sqrt : ℕ) : ℝ) := by
          rw [hfilt]
          exact hTail t t.sqrt hts1
  -- ### the `ν ≤ √t` part
  have hnu_le : |(∑ ν ∈ Finset.Icc 1 t.sqrt, g ν)|
      ≤ (∑ ν ∈ (Finset.Icc 1 t.sqrt).filter Squarefree, |FIr (ν ^ 2) t|) := by
    have hsf : (∑ ν ∈ Finset.Icc 1 t.sqrt, g ν)
        = ∑ ν ∈ (Finset.Icc 1 t.sqrt).filter Squarefree, g ν := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      by_cases h : Squarefree ν
      · simp [h]
      · simp [h, hgdef, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    rw [hsf]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun ν _ => ?_)
    simp only [hgdef]
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one ν)
  -- the two cases for the `ν ≤ √t` part
  have hnu_bound : (∑ ν ∈ (Finset.Icc 1 t.sqrt).filter Squarefree, |FIr (ν ^ 2) t|)
      ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-(lamm + 2))
        + (Acount FIa (t : ℝ) * K3 * (Real.log ((t : ℝ) + 2)) ^ ((71 - (2 * lamm + 100)) / 2)
          + Acount FIa (t : ℝ) * K3 / Real.sqrt (L : ℝ)) := by
    by_cases hcase : (t.sqrt) ^ 2 < Submission.X2Y4R3.R3cut x
    · have h1 : (∑ ν ∈ (Finset.Icc 1 t.sqrt).filter Squarefree, |FIr (ν ^ 2) t|)
          ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-(lamm + 2)) :=
        hsmall x hxX1 t (by omega) htx t.sqrt hts1 hcase
      have h2 : (0 : ℝ) ≤ Acount FIa (t : ℝ) * K3
          * (Real.log ((t : ℝ) + 2)) ^ ((71 - (2 * lamm + 100)) / 2) :=
        mul_nonneg (mul_nonneg hAc0 hK3pos.le) (Real.rpow_nonneg hlogtpos.le _)
      have h3 : (0 : ℝ) ≤ Acount FIa (t : ℝ) * K3 / Real.sqrt (L : ℝ) :=
        div_nonneg (mul_nonneg hAc0 hK3pos.le) (by positivity)
      linarith
    · push_neg at hcase
      have hRs : Submission.X2Y4R3.R3cut x ≤ t := by
        have h1 : Submission.X2Y4R3.R3cut x ≤ t.sqrt * t.sqrt := by simpa [pow_two] using hcase
        have h2 : t.sqrt * t.sqrt ≤ t := by
          have := Nat.le_sqrt.mp (le_refl t.sqrt)
          simpa [pow_two] using this
        omega
      have hLt : L ≤ t.sqrt := by
        rw [Nat.le_sqrt]
        exact le_of_lt (lt_of_lt_of_le (by simpa [pow_two] using hLsq_lt) hRs)
      have h1 : ((Finset.Icc 1 t.sqrt).filter Squarefree).filter (fun ν => ν ≤ L)
          = (Finset.Icc 1 L).filter Squarefree := by
        ext ν
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨⟨h1, -⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
        · rintro ⟨⟨h1, h4⟩, h3⟩; exact ⟨⟨⟨h1, le_trans h4 hLt⟩, h3⟩, h4⟩
      have h2 : ((Finset.Icc 1 t.sqrt).filter Squarefree).filter (fun ν => ¬ ν ≤ L)
          = (Finset.Icc (L + 1) t.sqrt).filter Squarefree := by
        ext ν
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨⟨-, h2⟩, h3⟩, h4⟩; exact ⟨⟨by omega, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨by omega, h2⟩, h3⟩, by omega⟩
      rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 t.sqrt).filter Squarefree)
        (fun ν => ν ≤ L), h1, h2]
      refine add_le_add (hsmall x hxX1 t (by omega) htx L hL1 hLsq_lt) ?_
      have hbig : (t : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((t : ℝ) + 2)) ^ (2 * lamm + 100)
          ≤ (L : ℝ) := by
        refine le_trans ?_ hLlow
        rw [hvdef]
        exact mul_le_mul (Real.rpow_le_rpow htRpos.le htle (by norm_num))
          (Real.rpow_le_rpow hlogtpos.le
            (Real.log_le_log (by linarith) (by linarith)) (by linarith))
          (Real.rpow_nonneg hlogtpos.le _) (Real.rpow_nonneg hx0.le _)
      exact hlarge x hxX2 t hX2t htx L hL1 hLt hbig
  -- ### the first large term
  have hAseq_t : Acount FIa (t : ℝ) ≤ CA * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    have h1 : Acount FIa (t : ℝ) ≤ Submission.Aseq t := by
      rw [FI_Acount_eq]
      have := Finset.single_le_sum (f := FIa) (s := Finset.range (t + 1))
        (fun i _ => FIa_nonneg i) (Finset.mem_range.mpr (Nat.succ_pos t))
      linarith
    refine le_trans h1 (le_trans (hAup t ht1) ?_)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num)) hCA.le
  have hx34 : (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) / cA := by
    rw [le_div_iff₀ hcA]; linarith [hAlow x hxX3]
  have hlogE : (Real.log ((t : ℝ) + 2)) ^ ((71 - (2 * lamm + 100)) / 2)
      ≤ (2 : ℝ) ^ (lamm + 14.5) * (Real.log x) ^ (-(lamm + 14.5)) := by
    have h2 : (71 - (2 * lamm + 100)) / 2 = -(lamm + 14.5) := by ring
    rw [h2]
    have h3 : Real.log ((t : ℝ) + 2) ^ (-(lamm + 14.5))
        ≤ (Real.log x / 2) ^ (-(lamm + 14.5)) :=
      Commons.Analysis.RealPow.rpow_le_rpow_of_one_le_of_exponent_nonpos (by linarith) hlogt
        (by linarith)
    refine le_trans h3 (le_of_eq ?_)
    rw [div_two_rpow _ hlogpos (-(lamm + 14.5)),
      show -(-(lamm + 14.5)) = lamm + 14.5 from by ring]
  have hlarge1 : Acount FIa (t : ℝ) * K3 * (Real.log ((t : ℝ) + 2)) ^ ((71 - (2 * lamm + 100)) / 2)
      ≤ (CA * K3 / cA * (2 : ℝ) ^ (lamm + 14.5))
          * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) := by
    have hlogpow_nn : (0 : ℝ) ≤ (Real.log x) ^ (-(lamm + 14.5)) := Real.rpow_nonneg hlogpos.le _
    have hl14 : (Real.log x) ^ (-(lamm + 14.5)) ≤ (Real.log x) ^ (-lamm) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ (lamm + 14.5) := Real.rpow_nonneg (by norm_num) _
    have hFpos : (0 : ℝ) ≤ Real.log ((t : ℝ) + 2) ^ ((71 - (2 * lamm + 100)) / 2) :=
      Real.rpow_nonneg hlogtpos.le _
    have hApos : (0 : ℝ) ≤ Acount FIa (t : ℝ) * K3 := mul_nonneg hAc0 hK3pos.le
    have hstep1 : Acount FIa (t : ℝ) * K3 * (Real.log ((t : ℝ) + 2)) ^ ((71 - (2 * lamm + 100)) / 2)
        ≤ (CA * (x : ℝ) ^ ((3 : ℝ) / 4) * K3)
          * ((2 : ℝ) ^ (lamm + 14.5) * (Real.log x) ^ (-(lamm + 14.5))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hAseq_t hK3pos.le) hlogE hFpos (by positivity)
    have hstep2 : (CA * (x : ℝ) ^ ((3 : ℝ) / 4) * K3)
          * ((2 : ℝ) ^ (lamm + 14.5) * (Real.log x) ^ (-(lamm + 14.5)))
        ≤ (CA * K3 * (2 : ℝ) ^ (lamm + 14.5))
          * ((Submission.Aseq x : ℝ) / cA * (Real.log x) ^ (-(lamm + 14.5))) := by
      rw [show (CA * (x : ℝ) ^ ((3 : ℝ) / 4) * K3)
            * ((2 : ℝ) ^ (lamm + 14.5) * (Real.log x) ^ (-(lamm + 14.5)))
          = (CA * K3 * (2 : ℝ) ^ (lamm + 14.5))
            * ((x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-(lamm + 14.5))) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx34 hlogpow_nn) (by positivity)
    have hstep3 : (CA * K3 * (2 : ℝ) ^ (lamm + 14.5))
          * ((Submission.Aseq x : ℝ) / cA * (Real.log x) ^ (-(lamm + 14.5)))
        ≤ (CA * K3 * (2 : ℝ) ^ (lamm + 14.5))
          * ((Submission.Aseq x : ℝ) / cA * (Real.log x) ^ (-lamm)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl14 (by positivity)) (by positivity)
    refine le_trans hstep1 (le_trans hstep2 (le_trans hstep3 (le_of_eq ?_)))
    ring
  have hlarge2 : Acount FIa (t : ℝ) * K3 / Real.sqrt (L : ℝ)
      ≤ (CA * K3 / cA * (2 : ℝ) ^ ((1 : ℝ) / 6))
          * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) := by
    have hsqv : Real.sqrt v = (x : ℝ) ^ ((1 : ℝ) / 6)
        * (Real.log ((x : ℝ) + 2)) ^ (lamm + 50) := by
      rw [hvdef]
      have h := sqrt_rpow_mul (x : ℝ) (Real.log ((x : ℝ) + 2)) (2 * lamm + 100) hx0.le hlogaddpos.le
      rw [show (2 * lamm + 100) / 2 = lamm + 50 from by ring] at h
      exact h
    have hg50 : (Real.log x) ^ (lamm + 50) ≤ (Real.log ((x : ℝ) + 2)) ^ (lamm + 50) :=
      Real.rpow_le_rpow hlogpos.le (Real.log_le_log (by linarith) (by linarith)) (by linarith)
    have hden : (x : ℝ) ^ ((1 : ℝ) / 6) * (Real.log x) ^ (lamm + 50) ≤ Real.sqrt (L : ℝ) :=
      calc (x : ℝ) ^ ((1 : ℝ) / 6) * (Real.log x) ^ (lamm + 50)
          ≤ (x : ℝ) ^ ((1 : ℝ) / 6) * (Real.log ((x : ℝ) + 2)) ^ (lamm + 50) :=
            mul_le_mul_of_nonneg_left hg50 (Real.rpow_nonneg hx0.le _)
        _ = Real.sqrt v := hsqv.symm
        _ ≤ Real.sqrt (L : ℝ) := Real.sqrt_le_sqrt hLlow
    have hmul1 : (x : ℝ) ^ (-(1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 6) = 1 := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hmul2 : (Real.log x) ^ (-(lamm + 50)) * (Real.log x) ^ (lamm + 50) = 1 := by
      rw [← Real.rpow_add hlogpos, show -(lamm + 50) + (lamm + 50) = (0 : ℝ) from by ring,
        Real.rpow_zero]
    have hle : 1 / Real.sqrt (L : ℝ)
        ≤ (x : ℝ) ^ (-(1 : ℝ) / 6) * (Real.log x) ^ (-(lamm + 50)) := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (L : ℝ)))]
      calc (1 : ℝ) = (x : ℝ) ^ (-(1 : ℝ) / 6) * (Real.log x) ^ (-(lamm + 50))
              * ((x : ℝ) ^ ((1 : ℝ) / 6) * (Real.log x) ^ (lamm + 50)) := by
            rw [show (x : ℝ) ^ (-(1 : ℝ) / 6) * (Real.log x) ^ (-(lamm + 50))
                  * ((x : ℝ) ^ ((1 : ℝ) / 6) * (Real.log x) ^ (lamm + 50))
                = ((x : ℝ) ^ (-(1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 6))
                  * ((Real.log x) ^ (-(lamm + 50)) * (Real.log x) ^ (lamm + 50)) from by ring,
              hmul1, hmul2, one_mul]
        _ ≤ (x : ℝ) ^ (-(1 : ℝ) / 6) * (Real.log x) ^ (-(lamm + 50)) * Real.sqrt (L : ℝ) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
    have hx16 : (x : ℝ) ^ (-(1 : ℝ) / 6) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hxR (by norm_num)
    have hl50 : (Real.log x) ^ (-(lamm + 50)) ≤ (Real.log x) ^ (-lamm) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    have hpow : (x : ℝ) ^ (-(1 : ℝ) / 6) * (Real.log x) ^ (-(lamm + 50))
        ≤ (Real.log x) ^ (-lamm) := by
      calc (x : ℝ) ^ (-(1 : ℝ) / 6) * (Real.log x) ^ (-(lamm + 50))
          ≤ 1 * (Real.log x) ^ (-lamm) :=
            mul_le_mul hx16 hl50 (Real.rpow_nonneg hlogpos.le _) (by norm_num)
        _ = (Real.log x) ^ (-lamm) := by ring
    have hlogpow_nn : (0 : ℝ) ≤ (Real.log x) ^ (-lamm) := Real.rpow_nonneg hlogpos.le _
    have hstep1 : Acount FIa (t : ℝ) * K3 / Real.sqrt (L : ℝ)
        ≤ (CA * (x : ℝ) ^ ((3 : ℝ) / 4) * K3) * ((Real.log x) ^ (-lamm)) := by
      rw [show Acount FIa (t : ℝ) * K3 / Real.sqrt (L : ℝ)
          = Acount FIa (t : ℝ) * K3 * (1 / Real.sqrt (L : ℝ)) from by ring]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hAseq_t hK3pos.le)
        (le_trans hle hpow) (by positivity) (by positivity)
    have hstep2a : (CA * (x : ℝ) ^ ((3 : ℝ) / 4) * K3) * ((Real.log x) ^ (-lamm))
        ≤ (CA * K3) * ((Submission.Aseq x : ℝ) / cA * (Real.log x) ^ (-lamm)) := by
      rw [show (CA * (x : ℝ) ^ ((3 : ℝ) / 4) * K3) * ((Real.log x) ^ (-lamm))
          = (CA * K3) * ((x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx34 hlogpow_nn) (by positivity)
    have hstep2b : (CA * K3) * ((Submission.Aseq x : ℝ) / cA * (Real.log x) ^ (-lamm))
        ≤ (CA * K3 * (2 : ℝ) ^ ((1 : ℝ) / 6))
          * ((Submission.Aseq x : ℝ) / cA * (Real.log x) ^ (-lamm)) := by
      have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 6) := Real.one_le_rpow (by norm_num) (by norm_num)
      have hnn : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) / cA * (Real.log x) ^ (-lamm) := by positivity
      refine mul_le_mul_of_nonneg_right ?_ hnn
      calc (CA * K3) = (CA * K3) * 1 := by ring
        _ ≤ (CA * K3) * (2 : ℝ) ^ ((1 : ℝ) / 6) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    have hstep3 : (CA * K3 * (2 : ℝ) ^ ((1 : ℝ) / 6))
          * ((Submission.Aseq x : ℝ) / cA * (Real.log x) ^ (-lamm))
        = (CA * K3 / cA * (2 : ℝ) ^ ((1 : ℝ) / 6))
          * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) := by ring
    exact le_trans hstep1 (le_trans hstep2a (le_trans hstep2b (le_of_eq hstep3)))
  -- ### the `ν ≤ √t`-part is small
  have hnu_bound' : (∑ ν ∈ (Finset.Icc 1 t.sqrt).filter Squarefree, |FIr (ν ^ 2) t|)
      ≤ (4 + CA * K3 / cA * (2 : ℝ) ^ (lamm + 14.5)
          + CA * K3 / cA * (2 : ℝ) ^ ((1 : ℝ) / 6))
        * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) := by
    refine le_trans hnu_bound ?_
    have hl1 : (Real.log x) ^ (-(lamm + 2)) ≤ (Real.log x) ^ (-lamm) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    have h4 : 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-(lamm + 2))
        ≤ 4 * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) := by
      calc 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-(lamm + 2))
          = 4 * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-(lamm + 2))) := by ring
        _ ≤ 4 * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hl1 (by positivity)) (by norm_num)
    have hA0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := by positivity
    have hl : (0 : ℝ) ≤ (Real.log x) ^ (-lamm) := Real.rpow_nonneg hlogpos.le _
    nlinarith [h4, hlarge1, hlarge2, hA0, hl, hK3pos]
  -- ### the tail
  have htail_bound : Acount FIa (t : ℝ) * (K / Real.sqrt ((t.sqrt : ℕ) : ℝ))
      ≤ CA * K * Real.sqrt 2 * ((x : ℝ) ^ ((1 : ℝ) / 2)) := by
    have hAle : Acount FIa (t : ℝ) ≤ CA * (t : ℝ) ^ ((3 : ℝ) / 4) := by
      have h1 : Acount FIa (t : ℝ) ≤ Submission.Aseq t := by
        rw [FI_Acount_eq]
        have := Finset.single_le_sum (f := FIa) (s := Finset.range (t + 1))
          (fun i _ => FIa_nonneg i) (Finset.mem_range.mpr (Nat.succ_pos t))
        linarith
      exact le_trans h1 (hAup t ht1)
    have hsq : K / Real.sqrt ((t.sqrt : ℕ) : ℝ) ≤ K * Real.sqrt 2 * (t : ℝ) ^ (-(1 : ℝ) / 4) := by
      have h1 : (t : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt 2 ≤ Real.sqrt ((t.sqrt : ℕ) : ℝ) := by
        rw [← sqrt_sqrt_div_two (t : ℝ) htRpos.le]
        refine Real.sqrt_le_sqrt ?_
        exact sqrt_half_le_natSqrt ht4
      have h2 : K / Real.sqrt ((t.sqrt : ℕ) : ℝ)
          ≤ K / ((t : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt 2) :=
        div_le_div_of_nonneg_left hKpos.le (by positivity) h1
      have h3 : K / ((t : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt 2)
          = K * Real.sqrt 2 * (t : ℝ) ^ (-(1 : ℝ) / 4) := by
        rw [div_div_eq_mul_div, div_eq_mul_inv, ← Real.rpow_neg htRpos.le]
        ring
      linarith
    have hprod := mul_le_mul hAle hsq (by positivity) (by positivity)
    have hsimp : (CA * (t : ℝ) ^ ((3 : ℝ) / 4)) * (K * Real.sqrt 2 * (t : ℝ) ^ (-(1 : ℝ) / 4))
        = CA * K * Real.sqrt 2 * (t : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [show (CA * (t : ℝ) ^ ((3 : ℝ) / 4)) * (K * Real.sqrt 2 * (t : ℝ) ^ (-(1 : ℝ) / 4))
          = CA * K * Real.sqrt 2 * ((t : ℝ) ^ ((3 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 4)) from by
        ring,
        ← Real.rpow_add htRpos]
      norm_num
    rw [hsimp] at hprod
    refine le_trans hprod ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num))
      (by positivity)
  have htail_small : |(∑ ν ∈ Finset.Icc (t.sqrt + 1) t, g ν)|
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    have hY := hY3 x hxY3
    simp only [Real.rpow_zero, mul_one] at hY
    refine le_trans (le_trans htail_le htail_bound) ?_
    calc CA * K * Real.sqrt 2 * (x : ℝ) ^ ((1 : ℝ) / 2)
        ≤ cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := hY
      _ ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
          mul_le_mul_of_nonneg_right (hAlow x hxX3) (Real.rpow_nonneg hlogpos.le _)
  -- ### final assembly
  calc |∑ ν ∈ Finset.Icc 1 t, g ν|
      = |(∑ ν ∈ Finset.Icc 1 t.sqrt, g ν) + (∑ ν ∈ Finset.Icc (t.sqrt + 1) t, g ν)| := by
        rw [hsplit]
    _ ≤ |(∑ ν ∈ Finset.Icc 1 t.sqrt, g ν)| + |(∑ ν ∈ Finset.Icc (t.sqrt + 1) t, g ν)| :=
        abs_add_le _ _
    _ ≤ (4 + CA * K3 / cA * (2 : ℝ) ^ (lamm + 14.5)
          + CA * K3 / cA * (2 : ℝ) ^ ((1 : ℝ) / 6))
          * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm))
        + (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
        add_le_add (le_trans hnu_le hnu_bound') htail_small
    _ ≤ (5 + (CA * K3 / cA) * ((2 : ℝ) ^ (lamm + 14.5)
          + (2 : ℝ) ^ ((1 : ℝ) / 6)))
        * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) := by
        have h0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
          mul_nonneg (by positivity) (Real.rpow_nonneg hlogpos.le _)
        nlinarith [h0]
    _ = (5 + (CA * K3 / cA) * ((2 : ℝ) ^ (lamm + 14.5)
          + (2 : ℝ) ^ ((1 : ℝ) / 6)))
        * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by ring

/-! ### `∑♭_{d ≤ x} g̃(d) ≪ (log x)^K` -/

/-- The squarefree sum of the density `g̃` of `ã` is `≪ (log x)^K`. -/
theorem sum_FIgtil_le : ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ x : ℕ, 2 ≤ x →
    (∑ d ∈ (Finset.Icc 1 x).filter Squarefree, FIgtil d) ≤ C * (Real.log x) ^ K := by
  obtain ⟨C, hC, K, hK, h⟩ := Commons.NumberTheory.Sieve.sum_squarefree_tau_pow_density_le
    (K := 0) (by norm_num) (fun p hp => FIgtil_nonneg p) (fun m n hmn => FIgtil_mul hmn)
    FIgtil_bound
  refine ⟨C, K, hC, hK, fun x hx => ?_⟩
  have h1 := h x hx
  simpa using h1

end

end Submission.ASP
