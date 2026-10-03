/-
  Companion paper, §9: the assembly of **(9.12)** for the Friedlander–Iwaniec sequence.

  The objects: `FI_S m = ∑_{ν ≤ m} μ(ν)g(ν²)` and `FI_T x m = ∑_{ν ≤ m} μ(ν)r_{ν²}(x)`, so that
  `Ã(x) = A(x)·FI_S(√x) + FI_T(x;√x)` (this is (9.10), `Acount_atil_FI_eq`).

  Given the two convergence *rates* of §9 for `g(ν²)` (which are `FI_sq_rates`), and the two halves
  of the `ν`-split (the `ν ≤ L` half = (R₃) applied to the squares `ν²`,
  `FIr_sq_small_le`, and the `ν > L` half = Cauchy–Schwarz + (9.2) + the convergence of
  `∑|g(ν²)|`, `FIr_sq_large_le`), we get

    `|Ã(x) − G·A(x)| ≤ Cg·A(x)/log x`,  `G = Gprod FIg`,

  which is (9.12) (in particular it gives both the upper and the lower bound for `Ã`).
  The split point `L` is a *parameter* — `x^{1/3}(log x)^{75} ≤ L`, `L² < R3cut x`, `L ≤ √x`
  (its existence is the separate arithmetic lemma `exists_split_point`).
-/
import Mathlib
import Submission.ASP.S29
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

set_option maxHeartbeats 3200000

namespace Submission.ASP

open Finset

noncomputable section

/-! ### The elementary square-root comparison -/

/-- `√n / 2 ≤ ⌊√n⌋₊` for `n ≥ 4`. -/
lemma sqrt_half_le_natSqrt {x : ℕ} (hx : 4 ≤ x) :
    Real.sqrt (x : ℝ) / 2 ≤ (x.sqrt : ℝ) := by
  have hn0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hx4 : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlt : Real.sqrt (x : ℝ) < (x.sqrt : ℝ) + 1 := by
    rw [Real.sqrt_lt hn0 (by positivity)]
    calc (x : ℝ) < ((x.sqrt + 1 : ℕ) : ℝ) ^ 2 := by
          exact_mod_cast (by
            have := Nat.sqrt_lt.mp (Nat.lt_succ_self x.sqrt); simpa [pow_two] using this)
      _ = ((x.sqrt : ℝ) + 1) ^ 2 := by push_cast; ring
  have h2 : (2 : ℝ) ≤ Real.sqrt (x : ℝ) := by
    have hs : Real.sqrt (4 : ℝ) ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt hx4
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h4] at hs
  linarith

/-! ### (9.10) decomposed -/

/-- `S(m) = ∑_{ν ≤ m} μ(ν)·g(ν²)`. -/
noncomputable def FI_S (m : ℕ) : ℝ :=
  ∑ ν ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius ν : ℝ) * FIg (ν ^ 2)

/-- `T(x;m) = ∑_{ν ≤ m} μ(ν)·r_{ν²}(x)`. -/
noncomputable def FI_T (x m : ℕ) : ℝ :=
  ∑ ν ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius ν : ℝ) * FIr (ν ^ 2) x

/-- **(9.10)**, decomposed: `Ã(x) = A(x)·S(√x) + T(x;√x)`. -/
lemma FI_decomp (x : ℕ) :
    Acount (atil FIa) (x : ℝ)
      = Acount FIa (x : ℝ) * FI_S x.sqrt + FI_T x x.sqrt := by
  rw [Acount_atil_FI_eq x, FI_S, FI_T, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ν _ => by ring)

/-! ### (9.12) -/

/-- **(9.12)**, in the form in which it is used: the asymptotic `Ã(x) = G·A(x)(1 + O(1/log x))`.

All the inputs are the two rates of §9 for `g(ν²)`, together with the split point `L`. -/
theorem FI_912_of_rates {K1 K2 : ℝ} (hK1 : 0 < K1) (hK2 : 0 < K2)
    (hRate : ∀ m : ℕ, 1 ≤ m → |FI_S m - Gprod FIg| ≤ K1 / Real.sqrt (m : ℝ))
    (hTail : ∀ N L : ℕ, 1 ≤ L →
      (∑ ν ∈ (Finset.Icc 1 N).filter (fun n => L < n), abs (FIg (ν ^ 2)))
        ≤ K2 / Real.sqrt (L : ℝ)) :
    ∃ X₀ : ℕ, ∃ Cg : ℝ, 0 < Cg ∧ ∀ x : ℕ, X₀ ≤ x → ∀ L : ℕ, 1 ≤ L → L ≤ x.sqrt →
      L ^ 2 < Submission.X2Y4R3.R3cut x →
      (x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) ≤ (L : ℝ) →
      |Acount (atil FIa) (x : ℝ) - Gprod FIg * Acount FIa (x : ℝ)|
        ≤ Cg * Acount FIa (x : ℝ) / Real.log x := by
  obtain ⟨X1, hX1le, hthr⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := 8 * K1 ^ 2)
      (by positivity) (n := 2) (r := (1 : ℝ) / 2) (by norm_num)
  obtain ⟨Xa, hsmall⟩ := FIr_sq_small_le
  obtain ⟨Xb, K3, hK3pos, hlarge⟩ := FIr_sq_large_le hK2 hTail
  refine ⟨max (Nat.ceil X1) (max (max Xa Xb) 16), 18 + 2 * K3, by positivity,
    fun x hx L hL1 hLx hLsq hLbig => ?_⟩
  have hxX1 : X1 ≤ (x : ℝ) := by
    have h1 : ((max (Nat.ceil X1) (max (max Xa Xb) 16) : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have h2 : ((Nat.ceil X1 : ℕ) : ℝ) ≤ ((max (Nat.ceil X1) (max (max Xa Xb) 16) : ℕ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    have h3 : X1 ≤ ((Nat.ceil X1 : ℕ) : ℝ) := Nat.le_ceil X1
    linarith
  have hxXa : Xa ≤ x :=
    le_trans (le_trans (le_trans (le_max_left Xa Xb) (le_max_left (max Xa Xb) 16))
      (le_max_right (Nat.ceil X1) (max (max Xa Xb) 16))) hx
  have hxXb : Xb ≤ x :=
    le_trans (le_trans (le_trans (le_max_right Xa Xb) (le_max_left (max Xa Xb) 16))
      (le_max_right (Nat.ceil X1) (max (max Xa Xb) 16))) hx
  have hx16 : 16 ≤ x :=
    le_trans (le_trans (le_max_right (max Xa Xb) 16)
      (le_max_right (Nat.ceil X1) (max (max Xa Xb) 16))) hx
  have hx4 : 4 ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < (x : ℝ) := by positivity
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
    have he : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans he h3)
    rwa [Real.log_exp] at h
  have hlogpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hlog2 : (1 : ℝ) ≤ Real.log ((x : ℝ) + 2) := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) + 2 := by
      have : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
      linarith
    have he : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans he h3)
    rwa [Real.log_exp] at h
  -- `A(x) ≥ 1` and `Aseq x ≤ 2A(x)`
  have hA1 : 1 ≤ Acount FIa (x : ℝ) := by
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, hx1⟩
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
  -- the `S`-part
  have hS : |FI_S x.sqrt - Gprod FIg| ≤ 1 / (2 * Real.log x) := by
    refine le_trans (hRate x.sqrt (by rw [Nat.le_sqrt]; omega)) ?_
    have hsqrtx : (2 : ℝ) ≤ Real.sqrt (x : ℝ) := by
      have hs : Real.sqrt (4 : ℝ) ≤ Real.sqrt (x : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hx4)
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h4] at hs
    have hlt : Real.sqrt (x : ℝ) < (x.sqrt : ℝ) + 1 := by
      rw [Real.sqrt_lt (by positivity) (by positivity)]
      calc (x : ℝ) < ((x.sqrt + 1 : ℕ) : ℝ) ^ 2 := by
            exact_mod_cast (by
              have := Nat.sqrt_lt.mp (Nat.lt_succ_self x.sqrt); simpa [pow_two] using this)
        _ = ((x.sqrt : ℝ) + 1) ^ 2 := by push_cast; ring
    have hnatsqrt : 4 * K1 ^ 2 * (Real.log x) ^ 2 ≤ ((x.sqrt : ℕ) : ℝ) := by
      have hth := hthr (x : ℝ) hxX1
      have heq : (x : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (x : ℝ) := (Real.sqrt_eq_rpow x).symm
      rw [heq] at hth
      linarith
    have hsqrt2 : 2 * K1 * Real.log x ≤ Real.sqrt (((x.sqrt : ℕ) : ℝ)) := by
      have h2 : (4 * K1 ^ 2 * (Real.log x) ^ 2 : ℝ) = (2 * K1 * Real.log x) ^ 2 := by ring
      calc 2 * K1 * Real.log x = Real.sqrt ((2 * K1 * Real.log x) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ = Real.sqrt (4 * K1 ^ 2 * (Real.log x) ^ 2) := by rw [h2]
        _ ≤ Real.sqrt (((x.sqrt : ℕ) : ℝ)) := Real.sqrt_le_sqrt hnatsqrt
    have hpos : (0 : ℝ) < ((x.sqrt : ℕ) : ℝ) := by
      have h1 : (2 : ℝ) ≤ Real.sqrt (x : ℝ) := hsqrtx
      have h2 := sqrt_half_le_natSqrt hx4
      linarith
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hpos) (by positivity)]
    linarith
  -- the `T`-part
  have hsf : FI_T x x.sqrt
      = ∑ ν ∈ (Finset.Icc 1 x.sqrt).filter Squarefree,
          (ArithmeticFunction.moebius ν : ℝ) * FIr (ν ^ 2) x := by
    rw [FI_T]
    exact (Finset.sum_subset (Finset.filter_subset Squarefree (Finset.Icc 1 x.sqrt))
      (fun ν hmem hν => by
        have hns : ¬ Squarefree ν := fun hs => hν (Finset.mem_filter.mpr ⟨hmem, hs⟩)
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
        norm_num)).symm
  have hsplit : (∑ ν ∈ (Finset.Icc 1 x.sqrt).filter Squarefree, |FIr (ν ^ 2) x|)
      = (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree, |FIr (ν ^ 2) x|)
        + (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, |FIr (ν ^ 2) x|) := by
    have h1 : ((Finset.Icc 1 x.sqrt).filter Squarefree).filter (fun ν => ν ≤ L)
        = (Finset.Icc 1 L).filter Squarefree := by
      ext ν
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, le_trans h2 hLx⟩, h3⟩, h2⟩
    have h2 : ((Finset.Icc 1 x.sqrt).filter Squarefree).filter (fun ν => ¬ ν ≤ L)
        = (Finset.Icc (L + 1) x.sqrt).filter Squarefree := by
      ext ν
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨by omega, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨by omega, h2⟩, h3⟩, by omega⟩
    rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 x.sqrt).filter Squarefree)
      (fun ν => ν ≤ L), h1, h2]
  have hT : |FI_T x x.sqrt|
      ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25))
        + (Acount FIa (x : ℝ) * K3 / (Real.log ((x : ℝ) + 2)) ^ 2
            + Acount FIa (x : ℝ) * K3 / Real.sqrt (L : ℝ)) := by
    rw [hsf]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h1 : (∑ ν ∈ (Finset.Icc 1 x.sqrt).filter Squarefree,
          |(ArithmeticFunction.moebius ν : ℝ) * FIr (ν ^ 2) x|)
        ≤ ∑ ν ∈ (Finset.Icc 1 x.sqrt).filter Squarefree, |FIr (ν ^ 2) x| :=
      Finset.sum_le_sum (fun ν _ => by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one ν))
    refine le_trans h1 ?_
    rw [hsplit]
    exact add_le_add (hsmall x hxXa L hL1 hLsq) (hlarge x hxXb L hL1 hLx hLbig)
  -- the final assembly
  have hdec : Acount (atil FIa) (x : ℝ) - Gprod FIg * Acount FIa (x : ℝ)
      = Acount FIa (x : ℝ) * (FI_S x.sqrt - Gprod FIg) + FI_T x x.sqrt := by
    rw [FI_decomp x]; ring
  have hp1 : (Real.log x) ^ (-((2 : ℝ) ^ 25)) ≤ 1 / Real.log x := by
    have h := Real.rpow_le_rpow_of_exponent_le hlog1 (show -((2 : ℝ) ^ 25) ≤ (-(1 : ℝ)) by norm_num)
    have h2 : (Real.log x) ^ (-(1 : ℝ)) = 1 / Real.log x := by
      rw [Real.rpow_neg hlogpos.le, Real.rpow_one, one_div]
    rwa [h2] at h
  have hl2le : Real.log x ≤ Real.log ((x : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogx_le_sq : Real.log x ≤ (Real.log ((x : ℝ) + 2)) ^ 2 := by
    nlinarith [hlog2, hl2le]
  have hLbig2 : (Real.log x) ^ 2 ≤ (L : ℝ) := by
    have h1 : (Real.log x) ^ (2 : ℝ) ≤ (Real.log x) ^ (75 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
    have h2 : (Real.log x) ^ (2 : ℝ) = (Real.log x) ^ 2 := Real.rpow_natCast _ 2
    have h3 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    have h4 : (Real.log x) ^ (75 : ℝ) ≤ (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) :=
      Real.rpow_le_rpow hlogpos.le hl2le (by norm_num)
    have h5 : (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) ≤ (L : ℝ) := by
      refine le_trans ?_ hLbig
      exact le_mul_of_one_le_left (Real.rpow_nonneg (le_trans zero_le_one hlog2) 75) h3
    rw [h2] at h1
    linarith
  have hsqrtL : Real.log x ≤ Real.sqrt (L : ℝ) := by
    calc Real.log x = Real.sqrt ((Real.log x) ^ 2) := (Real.sqrt_sq hlogpos.le).symm
      _ ≤ Real.sqrt (L : ℝ) := Real.sqrt_le_sqrt hLbig2
  rw [hdec]
  have b1 : Acount FIa (x : ℝ) * |FI_S x.sqrt - Gprod FIg|
      ≤ Acount FIa (x : ℝ) / Real.log x := by
    calc Acount FIa (x : ℝ) * |FI_S x.sqrt - Gprod FIg|
        ≤ Acount FIa (x : ℝ) * (1 / (2 * Real.log x)) := mul_le_mul_of_nonneg_left hS hA0
      _ ≤ Acount FIa (x : ℝ) / Real.log x := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_left hA0 hlogpos (by linarith)
  have b2 : 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25))
      ≤ 8 * Acount FIa (x : ℝ) / Real.log x := by
    have h1 : 4 * (Submission.Aseq x : ℝ) ≤ 8 * Acount FIa (x : ℝ) := by linarith [hAseq]
    calc 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25))
        ≤ (8 * Acount FIa (x : ℝ)) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hlogpos.le _)
      _ ≤ (8 * Acount FIa (x : ℝ)) * (1 / Real.log x) :=
          mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ = 8 * Acount FIa (x : ℝ) / Real.log x := by ring
  have b3 : Acount FIa (x : ℝ) * K3 / (Real.log ((x : ℝ) + 2)) ^ 2
      ≤ Acount FIa (x : ℝ) * K3 / Real.log x :=
    div_le_div_of_nonneg_left (by positivity) hlogpos hlogx_le_sq
  have b4 : Acount FIa (x : ℝ) * K3 / Real.sqrt (L : ℝ)
      ≤ Acount FIa (x : ℝ) * K3 / Real.log x :=
    div_le_div_of_nonneg_left (by positivity) hlogpos hsqrtL
  have hT2 : |FI_T x x.sqrt|
      ≤ 8 * Acount FIa (x : ℝ) / Real.log x
        + (Acount FIa (x : ℝ) * K3 / (Real.log ((x : ℝ) + 2)) ^ 2
            + Acount FIa (x : ℝ) * K3 / Real.sqrt (L : ℝ)) := by
    linarith [hT, b2]
  refine le_trans (le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_mul, abs_of_nonneg hA0]))) ?_
  refine le_trans (add_le_add b1 hT2) ?_
  have hK30 : (0 : ℝ) ≤ K3 := le_of_lt hK3pos
  have hfin : Acount FIa (x : ℝ) / Real.log x
        + (8 * Acount FIa (x : ℝ) / Real.log x
          + (Acount FIa (x : ℝ) * K3 / (Real.log ((x : ℝ) + 2)) ^ 2
            + Acount FIa (x : ℝ) * K3 / Real.sqrt (L : ℝ)))
      ≤ (18 + 2 * K3) * Acount FIa (x : ℝ) / Real.log x := by
    have h1 : Acount FIa (x : ℝ) / Real.log x + 8 * Acount FIa (x : ℝ) / Real.log x
        = 9 * Acount FIa (x : ℝ) / Real.log x := by ring
    have h2 : Acount FIa (x : ℝ) * K3 / Real.log x + Acount FIa (x : ℝ) * K3 / Real.log x
        = 2 * (Acount FIa (x : ℝ) * K3) / Real.log x := by ring
    have hle : 9 * Acount FIa (x : ℝ) / Real.log x
          + 2 * (Acount FIa (x : ℝ) * K3) / Real.log x
        ≤ (18 + 2 * K3) * Acount FIa (x : ℝ) / Real.log x := by
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hlogpos.le
      nlinarith [hA0, hK30]
    linarith [b3, b4, h1, h2, hle]
  linarith [hfin]

/-! ### The split point `L` -/

/-- `2^{1/30} ≤ 2`. -/
private lemma two_rpow_one_div_30_le_two : (2 : ℝ) ^ ((1 : ℝ) / 30) ≤ 2 := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (1 : ℝ) / 30 ≤ 1)
  rwa [Real.rpow_one] at h

/-- The existence of the split point `L` used in (9.12): `L` is essentially
`x^{1/3}(log x)^{75}`, which lies above the (9.2)-threshold and below both `√x` and
`√(R3cut x)`. -/
lemma exists_split_point : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
    ∃ L : ℕ, 1 ≤ L ∧ L ≤ x.sqrt ∧ L ^ 2 < Submission.X2Y4R3.R3cut x ∧
      (x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) ≤ (L : ℝ) := by
  obtain ⟨X1, -, h1⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := 32) (by norm_num)
      (n := 150) (r := (1 : ℝ) / 30) (by norm_num)
  obtain ⟨X2, -, h2⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := 4) (by norm_num)
      (n := 75) (r := (1 : ℝ) / 6) (by norm_num)
  refine ⟨max 16 (max ⌈X1⌉₊ ⌈X2⌉₊) + 1, fun x hx => ?_⟩
  have hx16 : 16 ≤ x := by
    have h : max 16 (max ⌈X1⌉₊ ⌈X2⌉₊) + 1 ≤ x := hx
    omega
  have hcast : ((max 16 (max ⌈X1⌉₊ ⌈X2⌉₊) + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  push_cast at hcast
  have hxX1 : X1 ≤ (x : ℝ) + 2 := by
    have h3 : ((⌈X1⌉₊ : ℕ) : ℝ) ≤ (x : ℝ) := by
      have h4 : ((⌈X1⌉₊ : ℕ) : ℝ) ≤ ((max 16 (max ⌈X1⌉₊ ⌈X2⌉₊) : ℕ) : ℝ) := by
        exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _)
      push_cast at h4
      linarith
    linarith [Nat.le_ceil X1]
  have hxX2 : X2 ≤ (x : ℝ) + 2 := by
    have h3 : ((⌈X2⌉₊ : ℕ) : ℝ) ≤ (x : ℝ) := by
      have h4 : ((⌈X2⌉₊ : ℕ) : ℝ) ≤ ((max 16 (max ⌈X1⌉₊ ⌈X2⌉₊) : ℕ) : ℝ) := by
        exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _)
      push_cast at h4
      linarith
    linarith [Nat.le_ceil X2]
  -- elementary positivity / log facts
  have hx0 : (0 : ℝ) < (x : ℝ) := by positivity
  have hx2 : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 4 ≤ x)
  have hlgx : (1 : ℝ) ≤ Real.log x := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) := by linarith
    have he : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans he h3)
    rwa [Real.log_exp] at h
  have hlog1 : (1 : ℝ) ≤ Real.log ((x : ℝ) + 2) := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) + 2 := by linarith
    have he : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans he h3)
    rwa [Real.log_exp] at h
  have hlog0 : (0 : ℝ) < Real.log ((x : ℝ) + 2) := lt_of_lt_of_le zero_lt_one hlog1
  -- the two log bounds
  have hb1 : 32 * (Real.log ((x : ℝ) + 2)) ^ (150 : ℕ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 30) := by
    have h := h1 ((x : ℝ) + 2) hxX1
    have hstep : ((x : ℝ) + 2) ^ ((1 : ℝ) / 30) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 30) := by
      have h2x : (x : ℝ) + 2 ≤ 2 * (x : ℝ) := by linarith
      calc ((x : ℝ) + 2) ^ ((1 : ℝ) / 30) ≤ (2 * (x : ℝ)) ^ ((1 : ℝ) / 30) :=
            Real.rpow_le_rpow (by positivity) h2x (by norm_num)
        _ = (2 : ℝ) ^ ((1 : ℝ) / 30) * (x : ℝ) ^ ((1 : ℝ) / 30) :=
            Real.mul_rpow (by norm_num) (le_of_lt hx0)
        _ ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 30) :=
            mul_le_mul_of_nonneg_right two_rpow_one_div_30_le_two
              (Real.rpow_nonneg (le_of_lt hx0) _)
    linarith
  have hb2 : 4 * (Real.log ((x : ℝ) + 2)) ^ (75 : ℕ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 6) := by
    have h := h2 ((x : ℝ) + 2) hxX2
    have hstep : ((x : ℝ) + 2) ^ ((1 : ℝ) / 6) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 6) := by
      have h2x : (x : ℝ) + 2 ≤ 2 * (x : ℝ) := by linarith
      have h6 : (2 : ℝ) ^ ((1 : ℝ) / 6) ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 : ℝ) / 6 ≤ 1)
        rwa [Real.rpow_one] at h
      calc ((x : ℝ) + 2) ^ ((1 : ℝ) / 6) ≤ (2 * (x : ℝ)) ^ ((1 : ℝ) / 6) :=
            Real.rpow_le_rpow (by positivity) h2x (by norm_num)
        _ = (2 : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 6) :=
            Real.mul_rpow (by norm_num) (le_of_lt hx0)
        _ ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 6) :=
            mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg (le_of_lt hx0) _)
    linarith
  have hb2r : 2 * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    have h := hb2
    rw [← Real.rpow_natCast (Real.log ((x : ℝ) + 2)) 75] at h
    have h' : (Real.log ((x : ℝ) + 2)) ^ ((75 : ℕ) : ℝ)
        = (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) := rfl
    rw [h'] at h
    calc 2 * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ)
        = 4 * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) / 2 := by ring
      _ ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 6) / 2 := div_le_div_of_nonneg_right h (by norm_num)
      _ = (x : ℝ) ^ ((1 : ℝ) / 6) := by ring
  have hb1r : (Real.log ((x : ℝ) + 2)) ^ (150 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 30) / 16 := by
    have h := hb1
    rw [← Real.rpow_natCast (Real.log ((x : ℝ) + 2)) 150] at h
    have h' : (Real.log ((x : ℝ) + 2)) ^ ((150 : ℕ) : ℝ)
        = (Real.log ((x : ℝ) + 2)) ^ (150 : ℝ) := rfl
    rw [h'] at h
    calc (Real.log ((x : ℝ) + 2)) ^ (150 : ℝ)
        = 32 * (Real.log ((x : ℝ) + 2)) ^ (150 : ℝ) / 32 := by ring
      _ ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 30) / 32 := div_le_div_of_nonneg_right h (by norm_num)
      _ = (x : ℝ) ^ ((1 : ℝ) / 30) / 16 := by ring
  set y : ℝ := (x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) with hy
  set L : ℕ := ⌊y⌋₊ + 1 with hLdef
  have hy1 : (1 : ℝ) ≤ y := by
    rw [hy]
    have h1' : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := Real.one_le_rpow (by linarith) (by norm_num)
    have h2' : (1 : ℝ) ≤ (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) := Real.one_le_rpow hlog1 (by norm_num)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) :=
          mul_le_mul h1' h2' (by norm_num) (by positivity)
  have hy0 : (0 : ℝ) ≤ y := le_trans zero_le_one hy1
  have hLy : y ≤ (L : ℝ) := by
    rw [hLdef]
    push_cast
    exact le_of_lt (Nat.lt_floor_add_one y)
  have hLy1 : (L : ℝ) ≤ y + 1 := by
    rw [hLdef]
    push_cast
    linarith [Nat.floor_le hy0]
  refine ⟨L, by omega, ?_, ?_, ?_⟩
  · -- `L ≤ √x`
    rw [Nat.le_sqrt]
    have hy2 : 2 * y ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [hy]
      rw [show 2 * ((x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ))
          = (x : ℝ) ^ ((1 : ℝ) / 3) * (2 * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ)) from by ring]
      calc (x : ℝ) ^ ((1 : ℝ) / 3) * (2 * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ))
          ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 6) :=
            mul_le_mul_of_nonneg_left hb2r (Real.rpow_nonneg (le_of_lt hx0) _)
        _ = (x : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_add hx0]; norm_num
    have hA : (L : ℝ) ≤ 2 * y := by linarith [hLy1, hy1]
    have hLhalf : (L : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := le_trans hA hy2
    have hsqrtx : (x : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (x : ℝ) := (Real.sqrt_eq_rpow x).symm
    rw [hsqrtx] at hLhalf
    have hsq : (L : ℝ) ^ 2 ≤ (x : ℝ) := by
      calc (L : ℝ) ^ 2 ≤ (Real.sqrt (x : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hLhalf 2
        _ = (x : ℝ) := Real.sq_sqrt (le_of_lt hx0)
    have h2 : ((L * L : ℕ) : ℝ) ≤ (x : ℝ) := by push_cast; simpa [pow_two] using hsq
    exact_mod_cast h2
  · -- `L² < R3cut x`
    have hx2 : ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) = (x : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    have hl2 : ((Real.log ((x : ℝ) + 2)) ^ (75 : ℝ)) ^ (2 : ℕ)
        = (Real.log ((x : ℝ) + 2)) ^ (150 : ℝ) := by
      rw [← Real.rpow_natCast ((Real.log ((x : ℝ) + 2)) ^ (75 : ℝ)) 2,
        ← Real.rpow_mul hlog0.le]
      norm_num
    have hy2 : y ^ 2 = (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (150 : ℝ) := by
      rw [hy, mul_pow, hx2, hl2]
    have hstep3 : 8 * y ^ 2 ≤ (1 / 2) * (x : ℝ) ^ ((7 : ℝ) / 10) := by
      rw [hy2]
      have hx23 : (0 : ℝ) < (x : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hx0 _
      calc 8 * ((x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (150 : ℝ))
          = (x : ℝ) ^ ((2 : ℝ) / 3) * (8 * (Real.log ((x : ℝ) + 2)) ^ (150 : ℝ)) := by ring
        _ ≤ (x : ℝ) ^ ((2 : ℝ) / 3) * (8 * ((x : ℝ) ^ ((1 : ℝ) / 30) / 16)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1r (by norm_num)) (le_of_lt hx23)
        _ = (1 / 2) * ((x : ℝ) ^ ((2 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 30)) := by ring
        _ = (1 / 2) * (x : ℝ) ^ ((7 : ℝ) / 10) := by
            rw [← Real.rpow_add hx0]; norm_num
    have hstep1 : (L : ℝ) ^ 2 ≤ 4 * y ^ 2 := by nlinarith [hLy1, hy1, hy0]
    have hstep2 : (L : ℝ) ^ 2 + 1 ≤ 8 * y ^ 2 := by nlinarith [hstep1, hy1]
    set Y : ℝ := (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) with hYdef
    have hstep4 : (1 / 2) * (x : ℝ) ^ ((7 : ℝ) / 10) < Y := by
      rw [hYdef]
      have hxpow : (0 : ℝ) < (x : ℝ) ^ ((7 : ℝ) / 10) := Real.rpow_pos_of_pos hx0 _
      have hlogbig : (1 / 2 : ℝ) < (Real.log x) ^ ((2 : ℝ) ^ 25) :=
        lt_of_lt_of_le (by norm_num) (Real.one_le_rpow hlgx (by norm_num))
      calc (1 / 2) * (x : ℝ) ^ ((7 : ℝ) / 10)
          = (x : ℝ) ^ ((7 : ℝ) / 10) * (1 / 2) := by ring
        _ < (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) :=
            mul_lt_mul_of_pos_left hlogbig hxpow
    have hY : (L : ℝ) ^ 2 + 1 < Y := lt_of_le_of_lt (le_trans hstep2 hstep3) hstep4
    rw [Submission.X2Y4R3.R3cut]
    rw [← hYdef]
    have hlt : Y - 1 < ((⌊Y⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one Y
      linarith
    have hfin : ((L ^ 2 : ℕ) : ℝ) < ((⌊Y⌋₊ : ℕ) : ℝ) := by
      push_cast
      linarith [hY, hlt]
    exact_mod_cast hfin
  · exact hLy

/-! ### (9.12) for the Friedlander–Iwaniec sequence -/

/-- `Gprod FIg > 0` (from (9.13): `Htil·G = 4/π` with `Htil > 0`). -/
lemma Gprod_FIg_pos : 0 < Gprod FIg := by
  obtain ⟨Htil, hHpos, -, hprod⟩ := FIgtil_H_exists
  have h := FIgtil_H_mul_Gprod hprod
  have h4 : (0 : ℝ) < 4 / Real.pi := by positivity
  nlinarith [hHpos, h4]

/-- **(9.12)**: `Ã(x) = G·A(x)·(1 + O(1/log x))`. -/
theorem FI_912 : ∃ X₀ : ℕ, ∃ Cg : ℝ, 0 < Cg ∧ ∀ x : ℕ, X₀ ≤ x →
    |Acount (atil FIa) (x : ℝ) - Gprod FIg * Acount FIa (x : ℝ)|
      ≤ Cg * Acount FIa (x : ℝ) / Real.log x := by
  obtain ⟨K1, hK1, hRate⟩ := FI_sq_rates.1
  obtain ⟨K2, hK2, hTail⟩ := FI_sq_rates.2
  obtain ⟨X1, Cg, hCg, h912⟩ := FI_912_of_rates hK1 hK2 hRate hTail
  obtain ⟨X2, hsplit⟩ := exists_split_point
  refine ⟨max X1 X2, Cg, hCg, fun x hx => ?_⟩
  obtain ⟨L, hL1, hLx, hLsq, hLbig⟩ := hsplit x (le_trans (le_max_right _ _) hx)
  exact h912 x (le_trans (le_max_left _ _) hx) L hL1 hLx hLsq hLbig


/-- The lower bound `Ã(x) ≫ A(x)` implicit in (9.12) (needed for the (1.6)-type input of `ã`). -/
theorem FI_Aseq_le_const_mul_Atil :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      Acount FIa (x : ℝ) ≤ (2 / Gprod FIg) * Acount (atil FIa) (x : ℝ) := by
  obtain ⟨X1, Cg, hCg, h912⟩ := FI_912
  have hG := Gprod_FIg_pos
  set K : ℝ := 2 * Cg / Gprod FIg + 1 with hKdef
  refine ⟨max X1 (Nat.ceil (Real.exp K) + 1), fun x hx => ?_⟩
  have hxX1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hxexp : Real.exp K ≤ (x : ℝ) := by
    have h1 : ((Nat.ceil (Real.exp K) + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hx
    push_cast at h1
    have h2 : Real.exp K ≤ ((Nat.ceil (Real.exp K) : ℕ) : ℝ) := Nat.le_ceil (Real.exp K)
    linarith
  have hlogK : K ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos K) hxexp
    rwa [Real.log_exp] at h
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]
    have h0 : (0 : ℝ) ≤ 2 * Cg / Gprod FIg := by positivity
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log x := le_trans hK1 hlogK
  have hlogpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hA1 : (1 : ℝ) ≤ Acount FIa (x : ℝ) := by
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have h := Finset.single_le_sum (f := FIa) (fun i _ => FIa_nonneg i) hmem
    rw [Acount, Nat.floor_natCast]
    have h2 : (1 : ℝ) ≤ FIa 1 := by rw [FIa]; exact_mod_cast an_one_pos'
    linarith
  have hA0 : (0 : ℝ) ≤ Acount FIa (x : ℝ) := le_trans zero_le_one hA1
  have h912' := h912 x hxX1
  have hClog : Cg / Real.log x ≤ Gprod FIg / 2 := by
    rw [div_le_iff₀ hlogpos]
    have hmono : (Gprod FIg / 2) * K ≤ (Gprod FIg / 2) * Real.log x :=
      mul_le_mul_of_nonneg_left hlogK (by linarith)
    have hKval : (Gprod FIg / 2) * K = Cg + Gprod FIg / 2 := by
      rw [hKdef]; field_simp
    linarith [hmono, hKval, hG]
  have hfinal : Gprod FIg / 2 * Acount FIa (x : ℝ) ≤ Acount (atil FIa) (x : ℝ) := by
    have hlower : Gprod FIg * Acount FIa (x : ℝ) - Cg * Acount FIa (x : ℝ) / Real.log x
        ≤ Acount (atil FIa) (x : ℝ) := by
      have h := (abs_le.mp h912').1
      linarith
    have h2 : Cg * Acount FIa (x : ℝ) / Real.log x
        ≤ (Gprod FIg / 2) * Acount FIa (x : ℝ) := by
      calc Cg * Acount FIa (x : ℝ) / Real.log x
          = (Cg / Real.log x) * Acount FIa (x : ℝ) := by ring
        _ ≤ (Gprod FIg / 2) * Acount FIa (x : ℝ) := mul_le_mul_of_nonneg_right hClog hA0
    linarith [hlower, h2]
  calc Acount FIa (x : ℝ) = (2 / Gprod FIg) * (Gprod FIg / 2 * Acount FIa (x : ℝ)) := by
        field_simp
    _ ≤ (2 / Gprod FIg) * Acount (atil FIa) (x : ℝ) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)

end

end Submission.ASP
