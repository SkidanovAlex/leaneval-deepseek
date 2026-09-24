import Mathlib
import Submission.Work.Chen.SwitchDefs
import Submission.Commons.NumberTheory.Mertens.primeProduct_twoSided_sharp

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.NumberTheory.Chen

open Finset
open scoped BigOperators

noncomputable section

/-! ### The two products

`MP n = ∏_{p ≤ n} (1 - 1/p)` is the Mertens product (controlled by
`Mertens.primeProduct_twoSided_sharp`), and `TP n = ∏_{3 ≤ p ≤ n} (1 - 1/(p-1)²)` is the
odd "twin" product, whose limit is the twin-prime constant `0.6601618…`.  The identity
`(1 - 1/(p-1)) = (1 - 1/p)·(1 - 1/(p-1)²)` turns the odd `(p-1)`-product `VsieveOdd` into
`2·MP·TP`, separating the two. -/

/-- The Mertens product `∏_{p ≤ n} (1 - 1/p)`. -/
def MP (n : ℕ) : ℝ := ∏ p ∈ Nat.primesLE n, (1 - (p : ℝ)⁻¹)

/-- The odd twin product `∏_{3 ≤ p ≤ n} (1 - 1/(p-1)²)`. -/
def TP (n : ℕ) : ℝ :=
  ∏ p ∈ (Nat.primesLE n).filter (fun p : ℕ => p ≠ 2), (1 - (((p : ℝ) - 1)^2)⁻¹)

lemma MP_nonneg (n : ℕ) : 0 ≤ MP n := by
  rw [MP]
  refine Finset.prod_nonneg (fun p hp => ?_)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  linarith

lemma MP_le_one (n : ℕ) : MP n ≤ 1 := by
  rw [MP]
  refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have h1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  · have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      positivity
    linarith

/-- The factor `1 - 1/(p-1)²` of the twin product, for an odd prime `p`, lies in `[0,1]`. -/
lemma twin_factor_mem_Icc {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    0 ≤ (1 - (((p : ℝ) - 1)^2)⁻¹) ∧ (1 - (((p : ℝ) - 1)^2)⁻¹) ≤ 1 := by
  have h3 : 3 ≤ p := Commons.NumberTheory.Chen.prime_three_le hp hp2
  have h3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  have hpos : (0 : ℝ) < ((p : ℝ) - 1)^2 := by nlinarith
  have h1 : (1 : ℝ) ≤ ((p : ℝ) - 1)^2 := by nlinarith
  have hle : (((p : ℝ) - 1)^2)⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr h1
  have hnn : 0 ≤ (((p : ℝ) - 1)^2)⁻¹ := by positivity
  exact ⟨by linarith, by linarith⟩

lemma TP_nonneg (n : ℕ) : 0 ≤ TP n := by
  rw [TP]
  refine Finset.prod_nonneg (fun p hp => ?_)
  exact (twin_factor_mem_Icc (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    (Finset.mem_filter.mp hp).2).1

lemma TP_le_one (n : ℕ) : TP n ≤ 1 := by
  rw [TP]
  refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
  · exact (twin_factor_mem_Icc (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      (Finset.mem_filter.mp hp).2).1
  · exact (twin_factor_mem_Icc (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      (Finset.mem_filter.mp hp).2).2

lemma TP_mono {m n : ℕ} (h : m ≤ n) : TP n ≤ TP m := by
  rw [TP, TP]
  refine Finset.prod_le_prod_of_subset_of_le_one₀ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Nat.mem_primesLE.mpr ⟨le_trans (Nat.mem_primesLE.mp hp.1).1 h,
      (Nat.mem_primesLE.mp hp.1).2⟩, hp.2⟩
  · intro p hp
    exact (twin_factor_mem_Icc (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      (Finset.mem_filter.mp hp).2).1
  · intro p hp _
    exact (twin_factor_mem_Icc (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      (Finset.mem_filter.mp hp).2).2

/-- The factorisation identity `(1 - 1/(p-1)) = (1 - 1/p)·(1 - 1/(p-1)²)` for `p ≥ 2`. -/
lemma one_sub_inv_pred_eq (p : ℕ) (hp : 2 ≤ p) :
    1 - 1/((p:ℝ)-1) = (1 - (p:ℝ)⁻¹) * (1 - (((p:ℝ)-1)^2)⁻¹) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have h1 : ((p : ℝ) - 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **The factorisation of `VsieveOdd`** for `z ≥ 3`:
`∏_{3 ≤ p < z} (1 - 1/(p-1)) = 2·(∏_{p ≤ z-1} (1-1/p))·(∏_{3 ≤ p ≤ z-1} (1-1/(p-1)²))`. -/
lemma VsieveOdd_succ_eq_two_MP_TP (n : ℕ) (hn : 2 ≤ n) :
    Commons.NumberTheory.Chen.ChenEight.VsieveOdd (n + 1) = 2 * MP n * TP n := by
  rw [Commons.NumberTheory.Chen.ChenEight.VsieveOdd_primesLE]
  have hpoint : ∀ p ∈ (Nat.primesLE n).filter (fun p : ℕ => p ≠ 2),
      1 - 1/((p:ℝ)-1) = (1 - (p:ℝ)⁻¹) * (1 - (((p:ℝ)-1)^2)⁻¹) := by
    intro p hp
    exact one_sub_inv_pred_eq p
      (Nat.Prime.two_le (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2)
  rw [Finset.prod_congr rfl hpoint, Finset.prod_mul_distrib]
  have hTP : (∏ p ∈ (Nat.primesLE n).filter (fun p : ℕ => p ≠ 2),
      (1 - (((p : ℝ) - 1)^2)⁻¹)) = TP n := rfl
  rw [hTP]
  have h2mem : (2 : ℕ) ∈ Nat.primesLE n :=
    Nat.mem_primesLE.mpr ⟨hn, Nat.prime_two⟩
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s := Nat.primesLE n)
    (p := fun x : ℕ => x = 2) (f := fun p : ℕ => (1 - (p:ℝ)⁻¹))
  have hfilt : (Nat.primesLE n).filter (fun x : ℕ => x = 2) = {2} := by
    rw [Finset.filter_eq', if_pos h2mem]
  rw [hfilt, Finset.prod_singleton] at hsplit
  have hsplit2 : (1 - (2:ℝ)⁻¹) *
      (∏ p ∈ (Nat.primesLE n).filter (fun p : ℕ => p ≠ 2), (1 - (p:ℝ)⁻¹)) = MP n := by
    rw [MP]
    simpa only [ne_eq, Nat.cast_ofNat] using hsplit
  have htwo : 2 * MP n =
      ∏ p ∈ (Nat.primesLE n).filter (fun p : ℕ => p ≠ 2), (1 - (p:ℝ)⁻¹) := by
    calc 2 * MP n = 2 * ((1 - (2:ℝ)⁻¹) *
            (∏ p ∈ (Nat.primesLE n).filter (fun p : ℕ => p ≠ 2), (1 - (p:ℝ)⁻¹))) := by
          rw [hsplit2]
      _ = (2 * (1 - (2:ℝ)⁻¹)) *
            (∏ p ∈ (Nat.primesLE n).filter (fun p : ℕ => p ≠ 2), (1 - (p:ℝ)⁻¹)) := by ring
      _ = ∏ p ∈ (Nat.primesLE n).filter (fun p : ℕ => p ≠ 2), (1 - (p:ℝ)⁻¹) := by
          rw [show (2:ℝ) * (1 - (2:ℝ)⁻¹) = 1 by norm_num, one_mul]
  rw [htwo]

lemma VsieveOdd_eq_two_MP_TP (z : ℕ) (hz : 3 ≤ z) :
    Commons.NumberTheory.Chen.ChenEight.VsieveOdd z = 2 * MP (z - 1) * TP (z - 1) := by
  conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ z)]
  exact VsieveOdd_succ_eq_two_MP_TP (z - 1) (by omega)

/-- The numeric value of the twin product up to `199`: `∏_{3 ≤ p ≤ 199}(1-1/(p-1)²) ≤ 0.66066`.
The true value is `0.6606582…`; the product is evaluated by `decide` (the prime list) plus
`norm_num` (the rational product). -/
lemma TP_199_le : TP 199 ≤ (33033/50000 : ℝ) := by
  rw [TP]
  rw [show (Nat.primesLE 199).filter (fun p : ℕ => p ≠ 2) =
    ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,
      127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199} : Finset ℕ) from by decide]
  simp [Finset.prod_insert]
  norm_num

/-! ### The Euler–Mascheroni bounds

`γ > harmonic 200 - log 201 > 0.5735`, hence `e^{-γ} ≤ 0.5637`. -/

lemma harmonic_200_gt : (5.878 : ℝ) < (harmonic 200 : ℝ) := by norm_num

lemma log_201_lt : Real.log (201:ℝ) < (5.3045 : ℝ) := by
  have hmul : Real.log (201:ℝ) = Real.log (200:ℝ) + Real.log (201/200 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (200:ℝ) ≠ 0) (by norm_num : (201/200 : ℝ) ≠ 0)]
    norm_num
  have h200 : Real.log (200:ℝ) ≤ 3*0.6931471808 + 2*1.6094379126 := by
    rw [show (200:ℝ) = 2^3 * 5^2 by norm_num, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have htail : Real.log (201/200 : ℝ) ≤ 1/200 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 201/200 by norm_num)
    linarith
  linarith

lemma exp_neg_5735_le : Real.exp (-(5735/10000 : ℝ)) ≤ (5637/10000 : ℝ) := by
  have hlow : (1774000/1000000 : ℝ) ≤ Real.exp (5735/10000 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ (5735/10000 : ℝ)) 7
    have hs : (1774000/1000000 : ℝ) ≤
        ∑ i ∈ Finset.range 7, (5735/10000 : ℝ)^i / (Nat.factorial i : ℝ) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    linarith
  have hdiv : Real.exp (-(5735/10000 : ℝ)) = 1/Real.exp (5735/10000 : ℝ) := by
    rw [Real.exp_neg, one_div]
  rw [hdiv, div_le_iff₀ (Real.exp_pos _)]
  nlinarith [hlow]

lemma exp_neg_eulerMascheroni_le : Real.exp (-Real.eulerMascheroniConstant) ≤ (5637/10000 : ℝ) := by
  have hγ : (5735/10000 : ℝ) < Real.eulerMascheroniConstant := by
    have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 200
    rw [Real.eulerMascheroniSeq] at h1
    have h2 : Real.log (((200 : ℕ) : ℝ) + 1) = Real.log 201 := by norm_num
    rw [h2] at h1
    linarith [harmonic_200_gt, log_201_lt]
  calc Real.exp (-Real.eulerMascheroniConstant) ≤ Real.exp (-(5735/10000 : ℝ)) :=
        le_of_lt (Real.exp_lt_exp.mpr (by linarith))
    _ ≤ (5637/10000 : ℝ) := exp_neg_5735_le

/-! ### The target -/

theorem VsieveOdd_mul_log_le :
    ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
      Commons.NumberTheory.Chen.ChenEight.VsieveOdd z * Real.log (z : ℝ) ≤ (149 / 200 : ℝ) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.Mertens.primeProduct_twoSided_sharp
  refine ⟨max (⌈Real.exp (100000 * C)⌉₊ + 2) 200002, ?_⟩
  intro z hz
  have hxz : ⌈Real.exp (100000 * C)⌉₊ + 2 ≤ z := le_trans (le_max_left _ _) hz
  have hz2 : 200002 ≤ z := le_trans (le_max_right _ _) hz
  have hNge : 200001 ≤ z - 1 := by omega
  have hz3 : 3 ≤ z := by omega
  set N : ℕ := z - 1 with hNdef
  have hzN : z = N + 1 := by omega
  have hN100 : 100 ≤ N := by omega
  have hzcast : (z : ℝ) = (N : ℝ) + 1 := by
    rw [hzN]; push_cast; ring
  -- `log N ≥ 100000·C`
  have hceil : Real.exp (100000 * C) ≤ ((⌈Real.exp (100000 * C)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hNreal : Real.exp (100000 * C) < (N : ℝ) := by
    have h1 : ⌈Real.exp (100000 * C)⌉₊ + 1 ≤ N := by omega
    have h2 : ((⌈Real.exp (100000 * C)⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hlogN : 100000 * C ≤ Real.log (N : ℝ) := by
    rw [← Real.log_exp (100000 * C)]
    exact Real.log_le_log (Real.exp_pos _) (le_of_lt hNreal)
  have hlogNpos : 0 < Real.log (N : ℝ) := by linarith
  have hNC : C / Real.log (N : ℝ) ≤ 1/100000 := by
    rw [div_le_iff₀ hlogNpos]
    calc C = (1/100000 : ℝ) * (100000 * C) := by ring
      _ ≤ (1/100000 : ℝ) * Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_left hlogN (by norm_num)
  have hNinv : 1/(N : ℝ) ≤ 1/100000 := by
    rw [div_le_iff₀ (by positivity)]
    have : (100000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 100000 ≤ N)
    linarith
  -- the Mertens upper bound at `N`
  have hMup : MP N * Real.log (N : ℝ) ≤
      Real.exp (-Real.eulerMascheroniConstant) + C/Real.log (N : ℝ) := by
    have h := (abs_le.mp (hC N hN100)).2
    rw [MP]
    linarith
  -- the factorisation, the twin-product bound and the log shift
  have hfac := VsieveOdd_eq_two_MP_TP z hz3
  have hTPN : TP N ≤ (33033/50000 : ℝ) :=
    le_trans (TP_mono (show 199 ≤ N by omega)) TP_199_le
  have hMPnn : (0 : ℝ) ≤ MP N := MP_nonneg N
  have hTPnn : (0 : ℝ) ≤ TP N := TP_nonneg N
  have hMP1 : MP N ≤ 1 := MP_le_one N
  have hzlog : Real.log (z : ℝ) ≤ Real.log (N : ℝ) + 1/(N : ℝ) := by
    have h1 : Real.log ((N : ℝ) + 1) =
        Real.log (N : ℝ) + Real.log (((N : ℝ) + 1)/(N : ℝ)) := by
      rw [← Real.log_mul (by positivity : ((N : ℝ)) ≠ 0) (by positivity : (((N : ℝ)+1)/(N:ℝ)) ≠ 0)]
      field_simp
    rw [hzcast, h1]
    have h2 : Real.log (((N : ℝ) + 1)/(N : ℝ)) ≤ ((N : ℝ) + 1)/(N : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : ((N : ℝ) + 1)/(N : ℝ) - 1 = 1/(N : ℝ) := by
      field_simp
      ring
    linarith
  have hL0 : (0 : ℝ) ≤ Real.log (N : ℝ) + 1/(N : ℝ) := by
    have : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    positivity
  have hMD : MP N * (1/(N : ℝ)) ≤ 1/(N : ℝ) := by
    have h := mul_le_of_le_one_left (show (0:ℝ) ≤ 1/(N:ℝ) by positivity) hMP1
    simpa using h
  have hmain : Commons.NumberTheory.Chen.ChenEight.VsieveOdd z * Real.log (z : ℝ)
      ≤ 2 * (33033/50000) *
        ((Real.exp (-Real.eulerMascheroniConstant) + C/Real.log (N : ℝ)) + 1/(N : ℝ)) := by
    rw [hfac]
    calc 2 * MP N * TP N * Real.log (z : ℝ)
        ≤ 2 * MP N * TP N * (Real.log (N : ℝ) + 1/(N : ℝ)) :=
          mul_le_mul_of_nonneg_left hzlog (by positivity)
      _ ≤ 2 * MP N * (33033/50000) * (Real.log (N : ℝ) + 1/(N : ℝ)) := by
          have h2 : (0 : ℝ) ≤ 2 * MP N * (Real.log (N : ℝ) + 1/(N : ℝ)) :=
            mul_nonneg (mul_nonneg (by norm_num) hMPnn) hL0
          calc 2 * MP N * TP N * (Real.log (N : ℝ) + 1/(N : ℝ))
              = (2 * MP N * (Real.log (N : ℝ) + 1/(N : ℝ))) * TP N := by ring
            _ ≤ (2 * MP N * (Real.log (N : ℝ) + 1/(N : ℝ))) * (33033/50000) :=
                mul_le_mul_of_nonneg_left hTPN h2
            _ = 2 * MP N * (33033/50000) * (Real.log (N : ℝ) + 1/(N : ℝ)) := by ring
      _ = 2 * (33033/50000) *
            (MP N * (Real.log (N : ℝ) + 1/(N : ℝ))) := by ring
      _ = 2 * (33033/50000) *
            (MP N * Real.log (N : ℝ) + MP N * (1/(N : ℝ))) := by ring
      _ ≤ 2 * (33033/50000) *
            ((Real.exp (-Real.eulerMascheroniConstant) + C/Real.log (N : ℝ)) + 1/(N : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          linarith [hMup, hMD]
  refine le_trans hmain ?_
  have hb : Real.exp (-Real.eulerMascheroniConstant) + C/Real.log (N : ℝ) + 1/(N : ℝ)
      ≤ (5637/10000 : ℝ) + 1/100000 + 1/100000 := by
    linarith [exp_neg_eulerMascheroni_le, hNC, hNinv]
  calc 2 * (33033/50000) *
        ((Real.exp (-Real.eulerMascheroniConstant) + C/Real.log (N : ℝ)) + 1/(N : ℝ))
      = 2 * (33033/50000) *
        (Real.exp (-Real.eulerMascheroniConstant) + C/Real.log (N : ℝ) + 1/(N : ℝ)) := by ring
    _ ≤ 2 * (33033/50000) * ((5637/10000 : ℝ) + 1/100000 + 1/100000) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ (149/200 : ℝ) := by norm_num

end

end Work.NumberTheory.Chen
